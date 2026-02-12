include "pval-interface.mc"
include "graph-print-helpers.mc"
include "helpers.mc"
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
let printArr = lam arr. printLn (join arr) 

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

  sem mcmc : all st. all a. (Int -> Bool -> PValInstance Complete st -> ()) -> MCMCConfig st a -> PValInstance Complete st -> MCMCResult st a
  sem mcmc printer config = | instance ->
    let acceptPred = lam prob. 
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
      
      printer acc.iterations true instance;
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
  syn HRMTree =
  | HRMNode { left : HRMTree, right : HRMTree, label : Int }
  | HRMLeaf { label : Int }
  | HRMEmptyTree ()

  syn HRMState x =
  | HRMState
    { mu: Option (PAssumeRef Float)
    , beta: Option (PAssumeRef Float)
    , lambda: Option (PAssumeRef [Float])
    , topo : Map Int {left : Int, right : Int, isRoot : Bool}
    , tree : HRMTree 
    , interactions : [[Int]]
    , nodes : Map Int (Map Int (PAssumeRef Int))
    , branchTimes : Map Int (Map Int (PAssumeRef Float))
    , branchStates : Map Int (Map Int (PAssumeRef Int))
    , likrWeights : Map Int PWeightRef
    , nodeSuppWeights : Map Int PWeightRef
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
      , branchStates = mapEmpty subi
      , likrWeights = mapEmpty subi
      , nodeSuppWeights = mapEmpty subi
      , bridgeSuppWeights = mapEmpty subi
      , branches = mapEmpty subi
      , below = []
      , tree = HRMEmptyTree ()
      , interactions = []
      , export = export
      }

  sem hrmRejectionSampling : all x. Bool -> Int -> (PValInstance Partial (HRMState x) -> Bool)
    -> (PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x))
    -> PValInstance Partial (HRMState x)
    -> (PValInstance Partial (HRMState x), Bool)
  sem hrmRejectionSampling forceMove rejectionDepth pred move = | instance -> 
    let instance = if forceMove then intermediateStep (move instance) else instance in
    recursive let rec = lam d. lam ist.
      -- hrmPrintState false ist;
      if pred ist then (ist, true) else
        if eqi d 0 then (ist, false) else
          rec (subi d 1) (intermediateStep (move instance))
    in
    rec rejectionDepth instance 
  
  sem foldLHRMTree : all a. all b. (HRMTree -> a -> a) -> a -> HRMTree -> a  
  sem foldLHRMTree f init = | tree ->
    recursive let foldLTree : all a. all b. (HRMTree -> a -> a) -> HRMTree -> a -> a =
      lam f. lam tree. lam acc.
        match tree with HRMLeaf l then f tree acc else
        match tree with HRMNode n in
          (compose 
            (foldLTree f n.left)
            (foldLTree f n.right)
          ) (f tree acc)
    in
    foldLTree f tree init

  -- Try finding an initialization of the program with probablity > 0.
  -- We use the following strategy:
  -- 1. Resample each node repertoire from prior until it is valid (at least one 2)
  -- 2. Resample branches until they are valid
  --   2.1. Resample bridges until they are valid
  --   2.2. Check importance weight, if invalid resample all bridges again
  -- 3. If all of the above fails, redraw mu, lambda and beta and go to 1.
  sem hrmFindPointInSupport : all x. all st. PValInstance Complete (HRMState x) -> PValInstance Complete (HRMState x)
  sem hrmFindPointInSupport = | instance ->  
    match startStep instance with instance in
    match getSt instance with HRMState st in

    let aHugeNumber = 10000000 in
    -- 
    let instance = optResample st.mu (lam. lam. mkGaussian 5. 0.000001) instance in 
    match getSt instance with HRMState st in
    let instance = optResample st.lambda (lam. lam. mkDirichlet [10000., 10000., 10000., 10000.]) instance in 
    let instance = intermediateStep instance in

    let mendNode = lam label. lam ist.
      match getSt ist with HRMState st in
      match mapLookup label st.nodeSuppWeights with Some wref in
      let hKeys = match mapLookup label st.nodes with Some hosts in mapKeys hosts in
      let move = lam ist. (hrmResampleNode label hKeys ist) in
      let pred = (lam ist. checkPreviousWeight wref ist) in
      match hrmRejectionSampling false aHugeNumber pred move ist with (ist, _) in
      ist
    in
   
    let longMend = lam l. lam ist. (hrmMendBranch aHugeNumber l ist).0 in 
    let branchMend = lam n. lam ist.
      let l = match n with HRMNode t then t.label else match n with HRMLeaf t in t.label in
      longMend l ist in
    let nodeMend = lam n. lam ist. match n with HRMNode t then mendNode t.label ist else ist in
    let postorderResampleBranch = lam tree. lam ist. foldLHRMTree branchMend ist tree in
    let postorderResampleNode = lam tree. lam ist. foldLHRMTree nodeMend ist tree in
    
    hrmPrintState false instance;
    printLn "Resampling node repertoires...";
    let instance = postorderResampleNode st.tree instance in
    printLn "Done resampling node repertoires.";
    hrmPrintState false instance;
    printLn "Resampling branches repertoires...";
    let instance = postorderResampleBranch st.tree instance in
    printLn "Done resampling node repertoires.";
    hrmPrintState false instance;
    -- hrmPrintBranch 1 instance;
    -- hrmPrintBranch 2 instance;
    -- hrmPrintBranch 3 instance;
    -- hrmPrintBranch 4 instance;
    -- hrmPrintBranch 5 instance;
    -- hrmPrintBranch 6 instance;
    -- hrmPrintBranch 7 instance;
    -- hrmPrintBranch 8 instance;
    -- let instance = postorderResample st.tree instance in
    (finalizeStep (lam. true) instance).1

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
      { st with branchStates = mapInsertOrCreate nodeLabel hostLabel subi ref st.branchStates
      , branches = mapInsertOrCreate nodeLabel hostLabel subi (Right ref) st.branches
      }

  sem hrmStoreAssume : all x. all a. HRMState x -> PAssumeRef a -> HRMState x
  sem hrmStoreAssume st = | ref ->
    st

  --
  -- Weight stores
  -- 
  sem hrmStoreWeight : all x. HRMState x -> PWeightRef -> HRMState x
  sem hrmStoreWeight st = | ref -> 
    st 

  sem hrmStoreLikrWeight : all x. Int -> HRMState x -> PWeightRef -> HRMState x
  sem hrmStoreLikrWeight nodeLabel st = | ref -> 
    match st with HRMState st in 
    -- printLn (join ["Likrweight: ", int2string nodeLabel]);
    HRMState {st with likrWeights = mapInsert nodeLabel ref st.likrWeights}

  sem hrmStoreNodeSuppWeight : all x.Int -> HRMState x -> PWeightRef -> HRMState x
  sem hrmStoreNodeSuppWeight nodeLabel st = | ref -> 
    match st with HRMState st in 
    -- printLn (join ["NodeSuppWeight: ", int2string nodeLabel]);
    HRMState {st with nodeSuppWeights = mapInsert nodeLabel ref st.nodeSuppWeights}

  sem hrmStoreBridgeSuppWeight : all x. Int -> Int -> HRMState x -> PWeightRef -> HRMState x
  sem hrmStoreBridgeSuppWeight nodeLabel hostLabel st = | ref -> 
    match st with HRMState st in 
    -- printLn (join ["BridgeSuppWeight: ", int2string nodeLabel, ", ", int2string hostLabel]);
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
      , nodeSuppWeights = st.nodeSuppWeights
      , bridgeSuppWeights = st.bridgeSuppWeights
      , branches = st.branches
      , branchTimes= st.branchTimes
      , branchStates = st.branchStates
      , below = st.below
      , tree = st.tree
      , interactions = st.interactions
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
  
  sem hrmStoreTree : all x. HRMTree -> [[Int]] -> HRMState x -> PExportRef () -> HRMState x
  sem hrmStoreTree tree interactions st = | ref -> 
    match st with HRMState st in
    let getLabel = lam t.
      match t with HRMNode n then
        n.label
      else match t with HRMLeaf n in
        n.label
    in 
    let insertNode = lam t. lam acc.
      match acc with (m, isRoot) in
      match t with HRMNode t then
        (mapInsert t.label { left = getLabel t.left, right = getLabel t.right, isRoot = isRoot} m, false)
      else (m, false)
    in
    HRMState {st with tree = tree, interactions = interactions, topo = (foldLHRMTree insertNode (st.topo, true) tree).0}

  sem hrmReadExport : all x. all complete. PValInstance complete (HRMState (PExportRef x)) -> x
  sem hrmReadExport = | instance ->
    match getSt instance with HRMState st in
    readPreviousExport st.export instance 

  -- Resample an assume wrapped in an Option
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
    -- printLn "Resampling mu";
    match getSt instance with HRMState st in
    let ist = intermediateStep (optResample st.mu (scaleMove l) instance) in
    match getSt ist with HRMState newSt in
    ist

  sem hrmResampleBeta : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleBeta l = | instance -> 
    -- printLn "Resampling beta";
    match getSt instance with HRMState st in
    optResample st.beta (scaleMove l) instance

  sem hrmResampleLambda : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleLambda a = | instance -> 
    -- printLn "Resampling Lambda";
    match getSt instance with HRMState st in
    optResample st.lambda (simplexMove a) instance
 
  sem hrmMendBranch : all x. Int -> Int -> PValInstance Partial (HRMState x) -> (PValInstance Partial (HRMState x), Bool)
  sem hrmMendBranch rejectionDepth node = | instance ->

    -- Resample only the broken bridges
    let tryRepairBranch = lam rdepth. lam hrefs. lam wrefs. lam ist. 
      let checkAndRepairBridge : all x. PValInstance Partial (HRMState x) -> Int -> (PValInstance Partial (HRMState x), Bool) =
        lam ist. lam h.
          match mapLookup h wrefs with Some wref in
          if checkPreviousWeight wref ist then (ist, true)
          else
            hrmResampleBridge rdepth node h ist
      in
      maybeFoldl checkAndRepairBridge ist (mapKeys hrefs) in

    -- Resample the whole branch
    let resampleBranch = lam rdepth. lam hrefs. lam ist. 
      maybeFoldl (flip (hrmResampleBridge rdepth node)) ist (mapKeys hrefs) in
 
    match getSt instance with HRMState st in
    match mapLookup node st.bridgeSuppWeights with Some wrefs then
      match mapLookup node st.branchTimes with Some hrefs in
      match mapLookup node st.likrWeights with Some wref in
      let valBridge = lam ist. foldl (lam acc. lam ref. and acc (checkPreviousWeight ref ist)) true (mapValues wrefs) in
      let valBranch = lam ist. checkPreviousWeight wref ist in
      let pred = lam ist. and (valBridge ist) (valBranch ist) in
      let move = lam ist.
        if valBridge ist then 
          if valBranch ist then ist
          else match (resampleBranch 100 hrefs ist) with (ist, success) in ist
        else match (tryRepairBranch 1000 hrefs wrefs ist) with (ist, success) in ist
      in
      hrmRejectionSampling false rejectionDepth pred move instance
    else (instance, true)

  -- Pick an inner node at random and pick each host to be resampled with probability p
  sem hrmResampleABlockNode : all x. Int -> Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleABlockNode rejectionDepth p = | instance -> 

    -- printLn "Inside blocknode";
    match getSt instance with HRMState st in
    let node = _chooseUniform (mapKeys st.nodes) in
    -- printLn (join ["Trying to resample node ", int2string node]);
    match mapLookup node st.nodes with Some hrefs in 
    match mapLookup node st.nodeSuppWeights with Some wref in
    -- Pick which hosts to resample
    let hKeys = foldr (
      lam hKey. lam acc.
        if bernoulliSample p then cons hKey acc else acc
    ) [] (mapKeys hrefs) in
    match hrmRejectionSampling true 10000 (checkPreviousWeight wref) (hrmResampleNode node hKeys) instance with (instance, success) in
    printArr ["Node ", int2string node];
    hrmPrintState false instance;
    let instance = match mapLookup node st.topo with Some {left = left, right = right, isRoot = isRoot} then 
      let branches = if isRoot then [left, right] else [node, left, right] in
      (maybeFoldl (lam acc. lam branch. hrmPrintState false acc; hrmPrintBranch branch acc; hrmMendBranch 10 branch acc) instance branches).0
    else 
      printLn (join ["Node: ", int2string node, " is missing from stored topology"]);
      exit 1 in
    printArr ["Node ", int2string node, " finished"];
    hrmPrintState false instance;
    instance
  
  sem hrmResampleBlockNode : all x. Int -> Int -> Int -> Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleBlockNode node hKey rejectionDepth p = | instance -> 
    match getSt instance with HRMState st in
    -- println "\n --- Start block move--";
    -- Resample the host
    match mapLookup node st.topo with Some {left = left, right = right, isRoot = isRoot} then 
    match mapLookup node st.nodes with Some hrefs in 
      -- printLn (join ["Resampling node: ", int2string node, ", host: ", int2string hKey]);
      -- printLn "---- Start Branches ----";
      -- Resample the incident branches
      let trySampleBranch = lam nodeLabel. lam instance. (hrmResampleBridge rejectionDepth nodeLabel hKey instance).0 in
      let instance = if isRoot then instance else trySampleBranch node instance in
      let instance = foldl (lam acc. lam n. trySampleBranch n acc) instance [left, right] in
      -- printLn "---- End branches ----";
      -- printJsonLn (hrmStateToDebugJson instance (getSt ist));
      instance
    else 
      printLn (join ["Node: ", int2string node, " is missing from stored topology"]);
      exit 1


  -- Resample the bridge between two nodes for a single host 
  sem hrmResampleBridge : all x. Int -> Int -> Int -> PValInstance Partial (HRMState x) -> (PValInstance Partial (HRMState x), Bool)
  sem hrmResampleBridge rejectionDepth nodeLabel hostLabel = | instance -> 
    match getSt instance with HRMState st in
    -- println (join ["nodeLabel: ", int2string nodeLabel, "hostLabel", int2string hostLabel]);
    match mapLookup nodeLabel st.branchTimes with Some hostMap in
    match mapLookup hostLabel hostMap with Some href in
    -- Here we only resample from the prior but we could consider doing something fancier
    let branchMove = lam d. lam. d in
    match mapLookup nodeLabel st.bridgeSuppWeights with Some hostWeights in
    match mapLookup hostLabel hostWeights with Some wref in
    hrmRejectionSampling true rejectionDepth (checkPreviousWeight wref) (resampleAssume branchMove href) instance
  
  sem hrmResampleBranch : all x. Int -> Int -> [Int] -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleBranch rejectionDepth nodeLabel hosts = | instance ->
    match getSt instance with HRMState st in
    match mapLookup nodeLabel st.likrWeights with Some wref in
    match mapLookup nodeLabel st.bridgeSuppWeights with Some wrefs in
    match mapLookup nodeLabel st.branchTimes with Some hrefs in
    recursive let rsBranch = lam ist. lam depth.
      if lti depth 0 then ist else
      -- printLn (join ["Resampling branch ", int2string label]);
      let tryRepairBranch = lam rdepth. lam ist. 
        let checkAndRepairBridge = lam h. lam ist.
          match mapLookup h wrefs with Some wref in
          if checkPreviousWeight wref ist then (ist, true) else 
            -- printLn (join ["Repairing branch ", int2string nodeLabel]);
            hrmResampleBridge rdepth nodeLabel h ist in
        foldl (lam acc. lam h.
          match acc with (_, false) then acc
        else checkAndRepairBridge h acc.0) (ist, true) hosts 
      in
      let resampleBranch = -- : all a. all b. Int -> Int -> Map Int (PAssumeRef Int) -> Map Int PWeightRef ->  PValInstance Partial (HRMState a) -> (PValInstance Partial (HRMState a), Bool) =
        lam rdepth. lam ist. 
        -- printLn (join ["Resampling branch ", int2string nodeLabel]);
        foldl (lam acc. lam h.
          match acc with (_, false) then acc
        else hrmResampleBridge rdepth nodeLabel h acc.0) (ist, true) hosts 
      in
      if foldl (lam acc. lam ref. and acc (checkPreviousWeight ref ist)) true (mapValues wrefs) then
        if checkPreviousWeight wref ist then ist
        else 
          match (resampleBranch rejectionDepth ist) with (ist, success) in
          match intermediateStep ist with ist in
          rsBranch ist (subi depth 1)
      else
        match (tryRepairBranch rejectionDepth ist) with (ist, success) in
        match intermediateStep ist with ist in
        rsBranch ist (subi depth 1)
    in
    let ist = rsBranch instance rejectionDepth in
    instance 

  -- Resample a single host at a single node. Will select one of the other states with equal probability
  sem hrmResampleHost : all x. PAssumeRef Int -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleHost nodeRef = | instance -> 
    match getSt instance with HRMState st in
    let catMove = lam. lam x. mkCategorical (normalize (map (lam c. if neqi x c then 1. else 0.) [0, 1, 2])) in
    -- let catMove = lam. lam x. mkCategorical [0., 0., 1.] in
    resampleAssume catMove nodeRef instance

  -- Resample all hosts at a node from the independence model
  -- We might want to consider tempering or other perturbations of the
  -- independence model distribution
  sem hrmResampleNode : all x. Int -> [Int] -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleNode nodeLabel hKeys = | instance -> 
    match getSt instance with HRMState st in
    match mapLookup nodeLabel st.nodes with Some nodes in
    let hrefs = map (lam s. match mapLookup s nodes with Some href in href) hKeys in
    let catMove = lam. lam x. mkCategorical (normalize (map (lam c. if neqi x c then 1. else 0.) [0, 1, 2])) in
    let ist = foldl (flip (resampleAssume catMove)) instance hrefs in
    ist

  -- MCMC move entrypoint
  sem hrmResampleAligned : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleAligned globalProb = | instance ->
    match getSt instance with HRMState st in
    -- let rbSchedule =
    --   [ (2., hrmResampleMu 1.0)
    --   , (5., hrmResampleMu 0.2)
    --   , (1., hrmResampleBeta 1.)
    --   , (2., hrmResampleLambda 10.)
    --   , (5., hrmResampleLambda 25.)
    --   , (8., hrmResampleABlockNode 100 1.) -- Weight should depend on the number of branches!
    --   ] in
    let rbSchedule =
      [ (1., hrmResampleMu 1.0)
      , (1., hrmResampleMu 0.2)
      , (1., hrmResampleMu 0.01)
      -- , (1., hrmResampleBeta 1.)
      , (1., hrmResampleLambda 10.)
      , (1., hrmResampleLambda 25.)
      , (10., hrmResampleABlockNode 10000 1.0) -- Weight should depend on the number of branches!
      ] in
    let weights = map (lam t. t.0) rbSchedule in
    let moves = map (lam t. t.1) rbSchedule in
    let instance = (_chooseNonUniform moves weights) instance in
    -- recursive let applyn = lam n. lam f. lam x.
    --   if leqi n 0 then x
    --   else applyn (subi n 1) f (f x)
    -- in
    -- let instance = foldl (lam ist. lam mw. match mw with (w, m) in applyn (roundfi w) m ist) instance rbSchedule in
    -- printJsonLn (hrmStateToDebugJson instance (getSt instance));
    let instance = intermediateStep instance in
    -- hrmPrintState false instance;
    instance
  
  sem hrmPrintState : all partial. all x. all y. Bool -> PValInstance partial (HRMState x) -> ()
  sem hrmPrintState mode = | instance ->
    match getSt instance with HRMState x in
    let readA = lam ref. readPreviousAssume ref instance in
    let checkW = lam ref. if checkPreviousWeight ref instance then "  valid" else "invalid" in
    let readW = lam ref. readPreviousWeight ref instance in
    let makePrefix = lam isLeft. if isLeft then "├──" else "└──" in
    recursive let depth = lam tree.
      match tree with HRMLeaf _ then 0
      else match tree with HRMNode t in 
      addi 1 (maxi (depth t.left) (depth t.right)) in
    let bridgeVis =
      lam label.
       match mapLookup label x.bridgeSuppWeights with Some bridgeWeights then
       match mapLookup label x.branchTimes with Some branchTimes in
        let hostVis = lam h.
          match mapLookup h bridgeWeights with Some w in
          let padf = match mapLookup h branchTimes with Some t then
            let f = float2string (roundf (readA t) 1) in
            concat (make (subi 5 (length f)) ' ') f 
          else "-----" in
          join ["b", int2string h, ":{w:", checkW w,",t:", padf , "}"] in
        strJoin ", " (map hostVis (mapKeys bridgeWeights))
        else
          "" in
    recursive let printTree = lam tree. lam prefix. lam isLeft. lam depth.
      match tree with HRMLeaf { label = label } then 
        let ints = get x.interactions (subi label 1) in
        let hostVis = lam h. lam s.
          join ["h:", int2string h, "{s:", int2string s, "}"] in
        [join 
          [ prefix
          , makePrefix isLeft
          , make (subi (muli depth 4) (length prefix)) '─'
          , " "
          , int2string label
          , ":"
          ," ["
          , strJoin ", " (map int2string ints)
          , "], "
          , bridgeVis label
          ]]
      else match tree with HRMNode { label = label, left = left, right = right } in 
        match mapLookup label x.nodes with Some hosts in
        let optSuppWeights = mapLookup label x.bridgeSuppWeights in
        match mapLookup label x.nodeSuppWeights with Some branchWeights in
        match mapLookup label x.likrWeights with Some likw in
        let nodeStr = join
          [ prefix
          , makePrefix isLeft
          , " "
          , int2string label
          , ":"
          , join (make (subi (muli depth 4) (length prefix)) " ")
          ," {"
          , strJoin ", " (map (compose int2string readA) (mapValues hosts))
          , "}, "
          , bridgeVis label
          , "b: "
          , checkW branchWeights
          , ", likr: "
          , float2string (readW likw)
          ] in
        let newPrefix = (join [prefix, if isLeft then "│   " else "    "]) in
        let leftStr = cons nodeStr (printTree left newPrefix true depth) in
        concat leftStr (printTree right newPrefix false depth) in

    match x.mu with Some mu in 
    match x.beta with Some beta in 
    match x.lambda with Some lambda in 
    let treelines = printTree x.tree "" false (depth x.tree) in
    -- let maxLength = foldl maxi 0 (map length lines) in
    let weightStr = join ["Total weight: ", float2string (getWeight instance)] in
    let instanceSt = if mode then "Complete" else "Partial" in
    let header =
      [ join ["╭──────────┬─", make (length weightStr) '─', "─┬─", make (length instanceSt) '─', "─╮"]
      , join ["│ HRMState │ ", weightStr,                   " │", instanceSt]
      , join ["╰──────────┴─", make (length weightStr) '─', "─┴─", make (length instanceSt) '─', "─╯"]
      ] in
    let lines = join
      [ header
      , [ join ["μ: ", float2string (readA mu)]
        , join ["β: ", float2string (readA beta)]
        , join ["λ: [", strJoin ", " (map float2string (readA lambda)), "]"]
        , "Tree:"
        ]
      , treelines
      , [[]]
      ] in
    let maxLength = foldl maxi 0 (map length lines) in
    let addPadding : [Char] -> [Char] = lam s. concat  s (make (subi maxLength (length s)) ' ')in
    let paddedLines = map addPadding lines in
    print (join ["╭", make (addi maxLength 2) '─', "╮\n"]);
    print (join (map (lam s. join ["│ ", s, " │\n"]) paddedLines));
    print (join ["╰", make (addi maxLength 2) '─', "╯\n"]);
    flushStdout ()

  sem hrmPrintBranch : all partial. all x. Int -> PValInstance partial (HRMState x) -> () 
  sem hrmPrintBranch node = | instance -> 
    match getSt instance with HRMState st in
    printLn (join ["Subbranch node: ", int2string node]);
    match mapLookup node st.branchTimes with Some hrefs in
    let hKeys = mapKeys hrefs in 
    (map (lam h. hrmPrintBridge node h instance) hKeys);
    ()
  
  sem hrmPrintBridge : all partial. all x. all y. Int -> Int -> PValInstance partial (HRMState x) -> ()
  sem hrmPrintBridge node host = | instance -> 
    match getSt instance with HRMState st in
    let readA = lam ref. readPreviousAssume ref instance in
    -- match mapLookup node st.nodes with Some arefs in
    -- match mapLookup host arefs with Some aref in
    -- let endState = readA aref in
    let dLook = lam m.
      match mapLookup node m with Some ts then
        match mapLookup host ts with Some ts then Some (readA ts)
        else None ()
      else None ()
    in

    let getTrans = lam st. (dLook st.branchTimes, dLook st.branchStates) in

    recursive let descend : PSubmodelRef (HRMState ()) -> [(Option Float, Option Int)] = lam smref. 
    -- recursive let descend = lam ist. lam hst. 
      let sm = readPreviousSubmodel smref instance in
      match sm with HRMState st  in
      let t = getTrans st in
      -- let r : PSubmodelRef (HRMState ()) -> [(Option Float, Option Int)] = lam sm. (descend sm)) in
      let s = foldl (lam acc. lam sm. concat acc (descend sm)) [] st.below in
      cons t s
    in
    let s = join (map descend st.below) in
    let s = filter (lam t. match t with (Some _, Some _) then true else false) s in
    let s = map (lam t. match t with (Some t, Some s) in (t, s)) s in
    let times = map (lam t. t.0) s in
    let times = cons (match dLook st.branchTimes with Some t in t) times in
    let states = map (lam t. t.1) s in
    let cumsum = lam arr. (mapAccumL (lam a. lam b. (addf a b, addf a b)) 0. arr).1 in
    let times = cumsum times in
    let termWidth = 196 in
    let maxTime = 6. in
    let pixst = 7 in

    let pixPerT = divf (divf (int2float termWidth) maxTime) (int2float pixst) in
    let ts = zip times states in
    let ps = lam c. lam ts. match ts with (_, s) in join [make (divi (subi pixst 3) 2) '─', "(", int2string s, ")", make (divi (subi pixst 3) 2) c] in
    let pt = lam c. lam ts. match ts with (t, _) in join [[c], float2string (truncf t (subi pixst 2)), [c]] in
    let f = lam c. lam p. lam acc. lam i. 
      match acc with (j, str) in
      if geqi j (length ts) then (j, concat str (make pixst c)) else
      match get ts j with (t, s) in
      if leqi (roundfi (mulf pixPerT t)) i then (addi j 1, concat str (p c (t, s)))
     else (j, concat str (make pixst c)) in
    let stateStr = (foldl (f '─' ps) (0, "") (range 0 (divi termWidth pixst) 1)).1 in
    let timeStr =  (foldl (f ' ' pt) (0, "") (range 0 (divi termWidth pixst) 1)).1 in
    printLn stateStr;
    printLn timeStr;
    ()
    

    

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
      -- [ maybeShowOpt (compose showFloat readA) "mu" x.mu 
      -- , maybeShowOpt (compose showFloat readA) "beta" x.beta 
      -- , maybeShowOpt (compose (showSeq showFloat) readA) "lambda" x.lambda
      -- Topology assume refs
      [ maybeShowMap int2string (showMap int2string (compose showInt readA)) "nodes" x.nodes
      -- , maybeShowMap int2string (showMap int2string (compose showFloat readA)) "branchTimes" x.branchTimes
      -- , maybeShowMap int2string (showMap int2string (showEither (compose showFloat readA) (compose showInt readA))) "branches" x.branches
      -- Weight refs
      , maybeShowMap int2string (showMap int2string (compose showFloat readW)) "bridge-supp-weights" x.bridgeSuppWeights
      , maybeShowMap int2string (compose showFloat readW) "node-supp-weights" x.nodeSuppWeights
      , maybeShowMap int2string (compose showFloat readW) "likr-weights" x.likrWeights
      -- Topology (abused export (?))
      -- , maybeShowMap int2string showLocTop "topology" x.topo
      -- Submodels
      , pruneSubmodels submodels
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
