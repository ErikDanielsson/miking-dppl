include "pval-interface.mc"
include "graph-print-helpers.mc"
include "json.mc"
include "option.mc"
include "stats.mc"
include "map.mc"

-- NOTE(vipa, 2025-12-09, ed, 2026-01-23): In lieu of proper distribution translations
-- I'll make these easy to substitute in
let mkBernoulli = lam p. use RuntimeDistElementary in DistBernoulli {p = p}
let mkExponential = lam rate. use RuntimeDistElementary in DistExponential {rate = rate}
let mkGaussian = lam mu. lam sigma. use RuntimeDistElementary in DistGaussian {mu = mu, sigma = sigma}
let mkGamma = lam shape. lam scale. use RuntimeDistElementary in DistGamma {shape = shape, scale = scale}
let mkPoisson = lam lambda. use RuntimeDistElementary in DistPoisson {lambda = lambda}
let mkUniform = lam a. lam b. use RuntimeDistElementary in DistUniform {a = a, b = b}
let mkDirichlet = lam a. use RuntimeDistElementary in DistDirichlet {a = a}
let mkCategorical = lam p. use RuntimeDistElementary in DistCategorical {p = p}
let mkReciprocal = lam a. lam b. use RuntimeDistElementary in DistReciprocal {a = a, b = b}

-- === General implementation of MCMC ===
let println = printLn

lang MCMCPVal = PValInterface
  type MCMCConfig st a =
    { getSample : PValInstance Complete st -> a
    , step : PValInstance Partial st -> PValInstance Partial st
    , iterations : Int  -- TODO(vipa, 2025-09-24): Make this something more general
    }

  type MCMCResult st a =
    { samples : [a]
    , acceptanceRatio : Float
    , finalInstance : PValInstance Complete st
    }

  sem mcmc : all st. all a. MCMCConfig st a -> PValInstance Complete st -> MCMCResult st a
  sem mcmc config = | instance ->
    let acceptPred = lam. lam prob. 
      -- printLn (join ["Accept prob: ", float2string prob]);
      -- printLn (join ["Current weight: ", float2string (getWeight instance)]);
      bernoulliSample (exp prob) in
    recursive let work = lam acc.
      if eqi acc.iterations 0 then acc else
      match finalizeStep acceptPred (config.step (startStep acc.instance)) with (accepted, instance) in
      let acc =
        { iterations = subi acc.iterations 1
        , accepted = addi acc.accepted (if accepted then 1 else 0)
        , samples = snoc acc.samples (config.getSample instance)
        , instance = instance
        } in
      work acc in
    let res = work {iterations = config.iterations, accepted = 0, samples = [], instance = instance} in
    { samples = res.samples
    , acceptanceRatio = divf (int2float res.accepted) (int2float config.iterations)
    , finalInstance = res.instance
    }
end


-- === A simple store of assumes, generic enough to work for any model ===

let _chooseUniform : all a. [a] -> a
  = lam l. get l (uniformDiscreteSample 0 (subi (length l) 1))

let normalize : [Float] -> [Float] = lam ws.
  let s = foldl addf 0. ws in
  map ((flip divf) s) ws

let _chooseNonUniform : all a. [a] -> [Float] -> a
  = lam l. lam ws. get l (categoricalSample (normalize ws))

let cmpTup : (Int, Int) -> (Int, Int) -> Int = lam kva. lam kvb. 
  let cmp1 = subi kva.0 kvb.0 in
  if eqi cmp1 0 then subi kva.1 kvb.1 else cmp1 

let mapInsertOrAppend : all k. all v. k -> v -> Map k [v] -> Map k [v]= 
  lam k. lam v. lam m.  
    match mapLookup k m with Some prev then
      mapInsert k (snoc prev v) m
    else
      mapInsert k [v] m

let mapInsertOrCreate =
 lam k1. lam k2. lam cmp. lam v. lam m.  
    match mapLookup k1 m with Some m2 then
      mapInsert k1 (mapInsert k2 v m2) m
    else
      mapInsert k1 (mapSingleton cmp k2 v) m




lang HRMState = PValInterface
  
  syn HRMState x =
  | HRMState
    { mu: Option (PAssumeRef Float)
    , beta: Option (PAssumeRef Float)
    , lambda: Option (PAssumeRef [Float])
    , topo : Map Int {left : Int, right : Int, isRoot : Bool}
    , nodes : Map Int (Map Int (PAssumeRef Int))
    , branchTimes : Map Int (Map Int (PAssumeRef Float))
    , likrWeights : Map Int [PWeightRef]
    , branchSuppWeights : Map Int [PWeightRef]
    , bridgeSuppWeights : Map Int (Map Int PWeightRef)
    , branches : Map Int (Map Int (Either (PAssumeRef Float) (PAssumeRef Int)))
    , below : [PSubmodelRef (HRMState ())]
    , export : x
    }

  sem hrmInit : all x. x -> HRMState x
  sem hrmInit = | export ->
    HRMState
      { mu = None ()
      , beta = None ()
      , lambda = None ()
      , topo = mapEmpty subi
      , nodes = mapEmpty subi
      , branchTimes = mapEmpty subi
      , likrWeights = mapEmpty subi
      , branchSuppWeights = mapEmpty subi
      , bridgeSuppWeights = mapEmpty subi
      , branches = mapEmpty subi
      , below = []
      , export = export
      }

  --
  -- Assume stores
  -- 
  sem hrmStoreMu : all a. all x. HRMState x -> PAssumeRef Float -> HRMState x
  sem hrmStoreMu st = | ref ->
    match st with HRMState st in
    HRMState {st with mu = Some ref}

  sem hrmStoreBeta : all a. all x. HRMState x -> PAssumeRef Float -> HRMState x
  sem hrmStoreBeta st = | ref ->
    match st with HRMState st in
    HRMState {st with beta = Some ref}

  sem hrmStoreLambda : all a. all x. HRMState x -> PAssumeRef [Float] -> HRMState x
  sem hrmStoreLambda st = | ref ->
    match st with HRMState st in
    HRMState {st with lambda = Some ref}

  sem hrmStoreNode : all x. Int -> Int -> HRMState x -> PAssumeRef Int -> HRMState x
  sem hrmStoreNode nodeLabel hostLabel st = | ref ->
    match st with HRMState st in
    HRMState
      { st with nodes = mapInsertOrCreate nodeLabel hostLabel subi ref st.nodes
      }

  sem hrmStoreBranchTime : all x. Int -> Int -> HRMState x -> PAssumeRef Float -> HRMState x
  sem hrmStoreBranchTime nodeLabel hostLabel st = | ref ->
    match st with HRMState st in
    HRMState
      { st with branchTimes = mapInsertOrCreate nodeLabel hostLabel subi ref st.branchTimes
      , branches = mapInsertOrCreate nodeLabel hostLabel subi (Left ref) st.branches
      }

  sem hrmStoreBranchState : all x. Int -> Int -> HRMState x -> PAssumeRef Int -> HRMState x
  sem hrmStoreBranchState nodeLabel hostLabel st = | ref ->
    match st with HRMState st in
    HRMState
      { st with branches = mapInsertOrCreate nodeLabel hostLabel subi (Right ref) st.branches
      }

  --
  -- Weight stores
  -- 
  sem hrmStoreLikrWeight : all x. Int -> HRMState x -> PWeightRef -> HRMState x
  sem hrmStoreLikrWeight nodeLabel st = | ref -> 
    match st with HRMState st in 
    HRMState {st with likrWeights = mapInsertOrAppend nodeLabel ref st.likrWeights}

  sem hrmStoreBranchSuppWeight : all x.Int -> HRMState x -> PWeightRef -> HRMState x
  sem hrmStoreBranchSuppWeight nodeLabel st = | ref -> 
    match st with HRMState st in 
    HRMState {st with branchSuppWeights = mapInsertOrAppend nodeLabel ref st.branchSuppWeights}

  sem hrmStoreBridgeSuppWeight : all x. Int -> Int -> HRMState x -> PWeightRef -> HRMState x
  sem hrmStoreBridgeSuppWeight nodeLabel hostLabel st = | ref -> 
    match st with HRMState st in 
    HRMState {st with bridgeSuppWeights = mapInsertOrCreate nodeLabel hostLabel subi ref st.bridgeSuppWeights}

  sem hrmStoreSubmodel : all x. HRMState x -> PSubmodelRef (HRMState ()) -> HRMState x
  sem hrmStoreSubmodel st = | ref ->
    match st with HRMState st in
    HRMState {st with below = snoc st.below ref}

  --
  -- Export stores
  -- 
  sem hrmStoreExport : all x1. all x2. HRMState x1 -> PExportRef x2 -> HRMState (PExportRef x2)
  sem hrmStoreExport st = | ref ->
    match st with HRMState st in
    HRMState
      { mu = st.mu
      , beta = st.beta
      , lambda = st.lambda
      , topo = st.topo
      , nodes = st.nodes
      , likrWeights = st.likrWeights
      , branchSuppWeights = st.branchSuppWeights
      , bridgeSuppWeights = st.bridgeSuppWeights
      , branches = st.branches
      , branchTimes= st.branchTimes
      , below = st.below
      , export = ref
      }
  
  -- Store local information about the topology. I think I am (mis|ab)using the export function here...
  sem hrmStoreLocTopo : all x. (Int, Int, Int, Bool) -> HRMState x -> PExportRef Bool -> HRMState x
  sem hrmStoreLocTopo topoLoc st = | ref ->
    match st with HRMState st in
    match topoLoc with (thisLabel, leftLabel, rightLabel, isRoot) in
      HRMState
        {st with topo = mapInsert thisLabel
          { left = leftLabel
          , right = rightLabel
          , isRoot = isRoot
          } st.topo
        }

  sem hrmReadExport : all x. all complete. PValInstance complete (HRMState (PExportRef x)) -> x
  sem hrmReadExport = | instance ->
    match getSt instance with HRMState st in
    readPreviousExport st.export instance

  -- Resample an assume wrapped in an option
  sem optResample : all a. all x. Option (PAssumeRef a) -> (Dist a -> a -> Dist a) -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem optResample optRef drift = | instance -> 
    match optRef with Some ref in
    resampleAssume drift ref instance
  
  -- Equivalent of RevBayes scaleMove
  sem scaleMove : Float -> (Dist Float -> Float -> Dist Float)
  sem scaleMove = | l ->
    let scale = exp (divf l 2.) in
    lam. lam x. mkReciprocal (divf x scale) (mulf x scale)

  -- Equivalent of RevBayes simplexMove
  sem simplexMove : Float -> (Dist [Float] -> [Float] -> Dist [Float])
  sem simplexMove = | d -> lam. lam x. mkDirichlet (map (lam v. divf (mulf d v) (foldl addf 0. x)) x)

  sem hrmResampleMu : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleMu l = | instance -> 
    match getSt instance with HRMState st in
    optResample st.mu (scaleMove l) instance

  sem hrmResampleBeta : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleBeta l = | instance -> 
    match getSt instance with HRMState st in
    optResample st.beta (scaleMove l) instance

  sem hrmResampleLambda : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleLambda a = | instance -> 
    match getSt instance with HRMState st in
    optResample st.lambda (simplexMove a) instance
  
  -- Pick an inner node at random and pick each host to be resampled with probability p
  sem hrmResampleBlockNode : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleBlockNode p = | instance -> 
    match getSt instance with HRMState st in
    let node = _chooseUniform (mapKeys st.nodes) in
    match mapLookup node st.nodes with Some hrefs in 
    -- Pick which hosts to resample
    let hKeys = foldr (
      lam hKey. lam acc.
        if bernoulliSample p then cons hKey acc else acc
    ) [] (mapKeys hrefs) in
    -- printLn (join ["Resampling node: ", int2string node, "hosts:", strJoin " " (map int2string hKeys)]);
    -- Resample the node
    let instance = foldr (
      lam hKey. lam ist.
        match mapLookup hKey hrefs with Some href in
        hrmResampleHost href ist
    ) instance hKeys in
    -- Resample the incident branches
    match mapLookup node st.topo with Some {left = left, right = right, isRoot = isRoot} then 
      let trySampleBranch = lam nodeLabel. lam ist. foldr (hrmResampleBridge nodeLabel) ist hKeys in
      let instance = if isRoot then instance else trySampleBranch node instance in
      foldl (lam acc. lam n. trySampleBranch n acc) instance [left, right]
    else 
      printLn (join ["Node: ", int2string node, " is missing from stored topology"]);
      exit 1

  -- Resample the bridge between two nodes for a single host 
  sem hrmResampleBridge : all x. Int -> Int -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleBridge nodeLabel hostLabel = | instance -> 
    match getSt instance with HRMState st in
    -- println (join ["nodeLabel: ", int2string nodeLabel, "hostLabel", int2string hostLabel]);
    match mapLookup nodeLabel st.branchTimes with Some hostMap in
    match mapLookup hostLabel hostMap with Some href in
    -- Here we only resample from the prior but we could consider doing something fancier
    let branchMove = lam d. lam. d in
    resampleAssume branchMove href instance
  
  -- Resample a single host at a single node. Will select one of the other states with equal probability
  sem hrmResampleHost : all x. PAssumeRef Int -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleHost nodeRef =  | instance -> 
    match getSt instance with HRMState st in
    let catMove = lam. lam x. mkCategorical (normalize (map (lam c. if neqi x c then 1. else 0.) [0, 1, 2])) in
    resampleAssume catMove nodeRef instance

  -- MCMC move entrypoint
  sem hrmResampleAligned : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleAligned globalProb = | instance ->
    match getSt instance with HRMState st in
    let rbSchedule =
      [ (2., hrmResampleMu 1.0)
      , (5., hrmResampleMu 0.2)
      , (1., hrmResampleBeta 1.)
      , (2., hrmResampleLambda 10.)
      , (5., hrmResampleLambda 25.)
      , (0., hrmResampleBlockNode 1.) -- Weight should depend on the number of branches!
      ] in
    let weights = map (lam t. t.0) rbSchedule in
    let moves = map (lam t. t.1) rbSchedule in
    let instance = (_chooseNonUniform moves weights) instance in
    -- printJsonLn (hrmStateToDebugJson instance (getSt instance));
    instance

  sem hrmStateToDebugJson : all partial. all x. all y. PValInstance partial (HRMState x) -> HRMState y -> JsonValue
  sem hrmStateToDebugJson instance = | pvi ->
    let optJson = hrmStateToDebugJsonHelper instance pvi in
    match optJson with Some json then json else JsonObject (mapFromSeq cmpString [])

  sem hrmStateToDebugJsonHelper : all partial. all x. all y. PValInstance partial (HRMState x) -> HRMState y -> Option JsonValue
  sem hrmStateToDebugJsonHelper instance = | HRMState x ->
    let readA = lam ref. readPreviousAssume ref instance in
    let readW = lam ref. readPreviousWeight ref instance in
    let showTopoKey = lam k. match k with (node, host) in join ["N", int2string node, ",H", int2string host] in
    let showLocTop = lam locTop. JsonObject (mapFromSeq cmpString
      [ ("left", showInt locTop.left)
      , ("right", showInt locTop.right)
      , ("isRoot", showBool locTop.isRoot)
      ]) in
    let submodels = (map (lam ref. hrmStateToDebugJsonHelper instance (readPreviousSubmodel ref instance)) x.below) in
    let v =  (mapFromSeq cmpString (join
      -- Global parameters
      [ maybeShowOpt (compose showFloat readA) "mu" x.mu 
      , maybeShowOpt (compose showFloat readA) "beta" x.beta 
      , maybeShowOpt (compose (showSeq showFloat) readA) "lambda" x.lambda
      -- Topology assume refs
      , maybeShowMap int2string (showMap int2string (compose showInt readA)) "nodes" x.nodes
      -- , maybeShowMap int2string (showMap int2string (compose showFloat readA)) "branchTimes" x.branchTimes
      -- , maybeShowMap int2string (showMap int2string (showEither (compose showFloat readA) (compose showInt readA))) "branches" x.branches
      -- Weight refs
      -- , maybeShowMap int2string (showMap int2string (compose showFloat readW)) "bridge-supp-weights" x.bridgeSuppWeights
      -- , maybeShowMap int2string (showSeq (compose showFloat readW)) "branch-supp-weights" x.branchSuppWeights
      -- , maybeShowMap int2string (showSeq  (compose showFloat readW)) "likr-weights" x.likrWeights
      -- -- Topology (abused export (?))
      -- , maybeShowMap int2string showLocTop "topology" x.topo
      -- -- Submodels
      -- , pruneSubmodels submodels
      ]
    )) in
    if eqi (mapLength v) 0 then None () else Some (JsonObject v)
end

lang HRMMCMCPVal = HRMState + MCMCPVal
  sem mkMCMCConfig : all x. Int -> Float -> MCMCConfig (HRMState (PExportRef x)) x
  sem mkMCMCConfig iterations = | globalProb ->
    { getSample = hrmReadExport
    , step = hrmResampleAligned globalProb
    , iterations = iterations
    }
end
