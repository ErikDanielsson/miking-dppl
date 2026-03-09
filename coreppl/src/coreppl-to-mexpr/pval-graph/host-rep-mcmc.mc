include "pval-interface.mc"
include "graph-print-helpers.mc"
include "helpers.mc"
include "json.mc"
include "option.mc"
include "stats.mc"
include "map.mc"
include "ext/mat-ext.mc"
include "ext/math-ext.mc"

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
  type MCMCConfig st a b =
    { getSample : PValInstance Complete st -> a
    , step : PValInstance Partial st -> (PValInstance Partial st, b)
    , cmpMoves : b -> b -> Int
    , sampleWriter : Int -> a -> ()
    , iterations : Int  -- TODO(vipa, 2025-09-24): Make this something more general
    }

  type MCMCResult st a b c =
    { samples : [a]
    , acceptanceRatio : Map b c
    , finalInstance : PValInstance Complete st
    }

  sem mcmc : all st. all a. all b. all c. (Int -> Bool -> PValInstance Complete st -> ()) -> MCMCConfig st a String -> PValInstance Complete st -> MCMCResult st a String (Int, Int)
  sem mcmc printer config = | instance ->
    let acceptPred = lam prob. 
      -- printLn (join ["Accept prob: ", float2string prob]);
      -- printLn (join ["Current weight: ", float2string (getWeight instance)]);
      bernoulliSample (exp prob) in
    recursive let work = lam acc.
      if eqi acc.iterations 0 then acc else
      -- println "Before step";
      match (config.step (startStep acc.instance)) with (instance, moveId) in

      match finalizeStep acceptPred instance with (accepted, instance) in
      -- printArr ["Accepted: ", bool2string accepted];
      printer acc.iterations true instance;
      -- hrmPrintNode 3 instance;
      -- (if and (eqi (cmpString moveId "Block node  ") 0) accepted then 
      --   printLn (join ["Accepted: ", bool2string accepted]);
      -- else ());
      -- println "After finalize step";
      -- printLn (join ["Accepted: ", bool2string accepted]);
      let sample = config.getSample instance in
      config.sampleWriter acc.iterations sample;
      let acc =
        { iterations = subi acc.iterations 1
        , accepted = mapInsertOrAdd moveId (if accepted then 1 else 0) acc.accepted 
        , samples = acc.samples
        , instance = instance
        } in
      
      work acc in
    let res = work {iterations = config.iterations, accepted = mapEmpty config.cmpMoves, samples = [], instance = instance} in
    { samples = res.samples
    , acceptanceRatio = res.accepted
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
  = lam l. lam ws.
    let c = (categoricalSample (normalize ws)) in
    get l c

let _sampleNonUniform : all a. [Float] -> Int =
  lam ws. categoricalSample (normalize ws)

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
    , transitionKernels : Map Int (PExportRef (Mat Float))
    , nodeSampleMsgs : Map Int (PExportRef (Mat Float))
    , preorderMsgs : Map Int (PExportRef (Mat Float))
    , below : [PSubmodelRef (HRMState ())]
    , export : x
    , subrootLabel : Option Int
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
      , transitionKernels = mapEmpty subi
      , nodeSampleMsgs = mapEmpty subi
      , preorderMsgs = mapEmpty subi
      , export = export
      , subrootLabel = None ()
      }

  sem hrmRejectionSampling : all x. Bool -> Int -> (PValInstance Partial (HRMState x) -> Bool)
    -> (PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x))
    -> PValInstance Partial (HRMState x)
    -> (PValInstance Partial (HRMState x), Bool)
  sem hrmRejectionSampling forceMove rejectionDepth pred move = | instance -> 
    let instance = if forceMove then intermediateStep (move instance) else instance in
    recursive let rec = lam d. lam instance.
      if pred instance then (instance, true) else
        if eqi d 0 then (instance, false) else
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
    let instance = optResample st.mu (Some (lam. mkGaussian 1. 0.000001)) instance in 
    match getSt instance with HRMState st in
    let instance = optResample st.lambda (Some (lam. mkDirichlet [10000., 10000., 10000., 10000.])) instance in 
    let instance = intermediateStep instance in

    let mendNode = lam label. lam instance.
      match getSt instance with HRMState st in
      match mapLookup label st.nodeSuppWeights with Some wref in
      let hKeys = match mapLookup label st.nodes with Some hosts in mapKeys hosts in
      let move = lam instance. (hrmResampleNode label hKeys instance) in
      let pred = (lam instance. checkPreviousWeight wref instance) in
      match hrmRejectionSampling false aHugeNumber pred move instance with (instance, _) in
      instance
    in
   
    let longMend = lam l. lam instance. (hrmMendBranch aHugeNumber 10 10 l instance).0 in 
    let branchMend = lam n. lam instance.
      let l = match n with HRMNode t then t.label else match n with HRMLeaf t in t.label in
      longMend l instance in
    let nodeMend = lam n. lam instance. match n with HRMNode t then mendNode t.label instance else instance in
    let postorderResampleBranch = lam tree. lam instance. foldLHRMTree branchMend instance tree in
    let postorderResampleNode = lam tree. lam instance. foldLHRMTree nodeMend instance tree in
    
    hrmPrintState false instance;
    printLn "Resampling node repertoires...";
    let instance = postorderResampleNode st.tree instance in
    printLn "Done resampling node repertoires.";
    hrmPrintState false instance;
    printLn "Resampling branches repertoires...";
    let instance = postorderResampleBranch st.tree instance in
    printLn "Done resampling node repertoires.";
    hrmPrintState false instance;
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
      , transitionKernels = st.transitionKernels
      , nodeSampleMsgs = st.nodeSampleMsgs
      , preorderMsgs = st.preorderMsgs
      , interactions = st.interactions
      , export = ref
      , subrootLabel = st.subrootLabel
      }

  sem hrmStoreTree : all x. Option Int -> HRMTree -> [[Int]] -> HRMState x -> PExportRef () -> HRMState x
  sem hrmStoreTree optSubrootLabel tree interactions st = | ref -> 
    match st with HRMState st in
    let getLabel = lam t.
      match t with HRMNode n then
        n.label
      else match t with HRMLeaf n in
        n.label
    in 
    let hasSubroot = match optSubrootLabel with None () then false else true in
    let insertNode = lam t. lam acc.
      match acc with (m, isRoot) in
      match t with HRMNode t then
        (mapInsert t.label { left = getLabel t.left, right = getLabel t.right, isRoot = isRoot} m, false)
      else (m, false)
    in
    -- Create the local topology
    let topo = (foldLHRMTree insertNode (st.topo, not hasSubroot) tree).0 in
    -- Handle the optional subroot
    let topo = match optSubrootLabel with Some subrootLabel then
      let rootLabel = getLabel tree in
      mapInsert subrootLabel {left = rootLabel, right = rootLabel, isRoot = true} topo
    else topo in
    HRMState {st with tree = tree, interactions = interactions, topo = topo, subrootLabel = optSubrootLabel}

  sem hrmHasSubroot : all x. HRMState x -> Bool
  sem hrmHasSubroot = | st ->
    match st with HRMState st in 
    match st.subrootLabel with Some label then true  else false

  sem hrmStoreTransKernel : all x. Int -> HRMState x -> PExportRef (Mat Float) -> HRMState x
  sem hrmStoreTransKernel nodeLabel st = | ref -> 
    match st with HRMState st in
    HRMState {st with transitionKernels = mapInsert nodeLabel ref st.transitionKernels}

  sem hrmStoreNodeMsg : all x. Int -> HRMState x -> PExportRef (Mat Float) -> HRMState x
  sem hrmStoreNodeMsg nodeLabel st = | ref -> 
    match st with HRMState st in
    printArr ["Node: Inserting ", int2string nodeLabel];
    HRMState {st with nodeSampleMsgs = mapInsert nodeLabel ref st.nodeSampleMsgs}

  sem hrmStorePreorderMsg : all x. Int -> HRMState x -> PExportRef (Mat Float) -> HRMState x
  sem hrmStorePreorderMsg nodeLabel st = | ref -> 
    match st with HRMState st in
    printArr ["Preorder: Inserting ", int2string nodeLabel];
    HRMState {st with preorderMsgs = mapInsert nodeLabel ref st.preorderMsgs}

  sem hrmReadExport : all x. all complete. PValInstance complete (HRMState (PExportRef x)) -> x
  sem hrmReadExport = | instance ->
    match getSt instance with HRMState st in
    readPreviousExport st.export instance 


  -- Resample an assume wrapped in an Option
  sem optResample : all a. all x. Option (PAssumeRef a) -> (Option (a -> Dist a)) -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem optResample optRef drift = | instance -> 
    match optRef with Some ref in
    resampleAssume drift ref instance
  
  -- Equivalent of RevBayes scaleMove
  sem scaleMove : Float -> Option (Float -> Dist Float)
  sem scaleMove = | l ->
    let scale = exp (divf l 2.) in
    Some (lam x. mkReciprocal (divf x scale) (mulf x scale))

  -- Equivalent of RevBayes simplexMove
  sem simplexMove : Float -> Option ([Float] -> Dist [Float])
  sem simplexMove = | d -> Some (lam x. mkDirichlet (map (lam v. divf (mulf d v) (foldl addf 0. x)) x))

  sem hrmResampleMu : all x. Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleMu l = | instance -> 
    -- printLn "Resampling mu";
    match getSt instance with HRMState st in
    -- printLn "Performing move on mu";
    -- hrmPrintState false instance;
    -- hrmPrintBranch 1 instance;
    -- hrmPrintBranch 2 instance;
    let instance = intermediateStep (optResample st.mu (scaleMove l) instance) in
    -- hrmPrintState false instance;
    -- printLn "Done performing move on mu";
    match getSt instance with HRMState newSt in
    instance

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
 
  sem hrmMendBranch : all x. Int -> Int -> Int -> Int -> PValInstance Partial (HRMState x) -> (PValInstance Partial (HRMState x), Bool)
  sem hrmMendBranch topLevelDepth repairDepth resampleDepth node = | instance ->

    -- Resample only the broken bridges
    let tryRepairBranch = lam rdepth. lam hrefs. lam wrefs. lam instance. 
      let checkAndRepairBridge : all x. PValInstance Partial (HRMState x) -> Int -> (PValInstance Partial (HRMState x), Bool) =
        lam instance. lam h.
          match mapLookup h wrefs with Some wref in
          if checkPreviousWeight wref instance then (instance, true)
          else
            hrmResampleBridge rdepth node h instance
      in
      maybeFoldl checkAndRepairBridge instance (mapKeys hrefs)
    in

    -- Resample the whole branch
    let resampleBranch = lam rdepth. lam hrefs. lam instance. 
      maybeFoldl (flip (hrmResampleBridge rdepth node)) instance (mapKeys hrefs)
    in
 
    match getSt instance with HRMState st in
    match mapLookup node st.bridgeSuppWeights with Some wrefs then
      match mapLookup node st.branchTimes with Some hrefs in
      match mapLookup node st.likrWeights with Some wref in
      let valBridge = lam instance. foldl (lam acc. lam ref. and acc (checkPreviousWeight ref instance)) true (mapValues wrefs) in
      let valBranch = lam instance. checkPreviousWeight wref instance in
      let pred = lam instance. and (valBridge instance) (valBranch instance) in
      let move = lam instance.
        if valBridge instance then 
          if valBranch instance then
            instance
          else match (resampleBranch resampleDepth hrefs instance) with (instance, success) in
            instance
        else match (tryRepairBranch repairDepth hrefs wrefs instance) with (instance, success) in
          instance
      in
      hrmRejectionSampling false topLevelDepth pred move instance
    else
      printLn "No bridge supp weights";
      (instance, true)

  -- Pick an inner node at random and pick each host to be resampled with probability p
  sem hrmResampleABlockNode : all x. Int -> Int -> Int -> Int -> Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleABlockNode rejectionDepthNode mendDepth repairDepth branchDepth p = | instance -> 

    -- printLn "Inside blocknode";
    match getSt instance with HRMState st in
    let node = _chooseUniform (mapKeys st.nodes) in
    -- printLn (join ["Trying to resample node ", int2string node]);
    match mapLookup node st.nodes with Some hrefs in 
    match mapLookup node st.nodeSuppWeights with Some wref in
    -- Pick which hosts to resample
    -- printArr ["Before node sampling ", int2string node];
    let hKeys = foldr (
      lam hKey. lam acc.
        if bernoulliSample p then cons hKey acc else acc
    ) [] (mapKeys hrefs) in
    match hrmRejectionSampling true rejectionDepthNode (checkPreviousWeight wref) (hrmResampleNodeLocalBP node hKeys) instance with (instance, success) in
    let strH = lam href. int2string (readPreviousAssume href instance) in
    -- printArr ["Suggested node state: ", strJoin ", " (map strH (mapValues hrefs)), ", ", bool2string success];
    -- printArr ["After node sampling ", int2string node];
    -- hrmPrintState false instance;
    let instance = if success then
      match mapLookup node st.topo with Some {left = left, right = right, isRoot = isRoot} then 
        let branches = if isRoot then [left, right] else [node, left, right] in
        let instance = (maybeFoldl (lam acc. lam branch. hrmMendBranch mendDepth repairDepth branchDepth branch acc) instance branches).0 in
        -- hrmPrintState false instance;
        -- (map (lam b. hrmPrintBranch b instance) branches);
        instance
      else 
        printLn (join ["Node: ", int2string node, " is missing from stored topology"]);
        exit 1
      else instance in

    -- printArr ["Node ", int2string node, " finished"];
    -- hrmPrintState false instance;
    instance

  sem hrmResampleABranch : all x. Int -> Int -> Int -> Float -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleABranch mendDepth repairDepth branchDepth p = | instance -> 
    match getSt instance with HRMState st in
    let branchStart = _chooseUniform (mapKeys st.branchTimes) in
    match mapLookup branchStart st.branchTimes with Some bridgeRefs in 
    let bKeys = foldr (
      lam hKey. lam acc.
        if bernoulliSample p then cons hKey acc else acc
    ) [] (mapKeys bridgeRefs) in
    let instance = foldl (lam instance. lam bKey. match mapLookup bKey bridgeRefs with Some bRef in resampleAssume (None ()) bRef instance) instance bKeys in
    match hrmMendBranch mendDepth repairDepth branchDepth branchStart instance with (instance, _) in
    instance

  -- Resample the bridge between two nodes for a single host 
  sem hrmResampleBridge : all x. Int -> Int -> Int -> PValInstance Partial (HRMState x) -> (PValInstance Partial (HRMState x), Bool)
  sem hrmResampleBridge rejectionDepth nodeLabel hostLabel = | instance -> 
    match getSt instance with HRMState st in
    -- println (join ["nodeLabel: ", int2string nodeLabel, "hostLabel", int2string hostLabel]);
    match mapLookup nodeLabel st.branchTimes with Some hostMap in
    match mapLookup hostLabel hostMap with Some href in
    -- Here we only resample from the prior but we could consider doing something fancier
    match mapLookup nodeLabel st.bridgeSuppWeights with Some hostWeights in
    match mapLookup hostLabel hostWeights with Some wref in
    hrmRejectionSampling true rejectionDepth (checkPreviousWeight wref) (resampleAssume (None ()) href) instance
  
  sem hrmResampleBranch : all x. Int -> Int -> [Int] -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleBranch rejectionDepth nodeLabel hosts = | instance ->
    match getSt instance with HRMState st in
    match mapLookup nodeLabel st.likrWeights with Some wref in
    match mapLookup nodeLabel st.bridgeSuppWeights with Some wrefs in
    match mapLookup nodeLabel st.branchTimes with Some hrefs in
    recursive let rsBranch = lam instance. lam depth.
      if lti depth 0 then instance else
      -- printLn (join ["Resampling branch ", int2string label]);
      let tryRepairBranch = lam rdepth. lam instance. 
        let checkAndRepairBridge = lam h. lam instance.
          match mapLookup h wrefs with Some wref in
          if checkPreviousWeight wref instance then (instance, true) else 
            -- printLn (join ["Repairing branch ", int2string nodeLabel]);
            hrmResampleBridge rdepth nodeLabel h instance in
        foldl (lam acc. lam h.
          match acc with (_, false) then acc
        else checkAndRepairBridge h acc.0) (instance, true) hosts 
      in
      let resampleBranch = -- : all a. all b. Int -> Int -> Map Int (PAssumeRef Int) -> Map Int PWeightRef ->  PValInstance Partial (HRMState a) -> (PValInstance Partial (HRMState a), Bool) =
        lam rdepth. lam instance. 
        -- printLn (join ["Resampling branch ", int2string nodeLabel]);
        foldl (lam acc. lam h.
          match acc with (_, false) then acc
        else hrmResampleBridge rdepth nodeLabel h acc.0) (instance, true) hosts 
      in
      if foldl (lam acc. lam ref. and acc (checkPreviousWeight ref instance)) true (mapValues wrefs) then
        if checkPreviousWeight wref instance then instance
        else 
          match (resampleBranch rejectionDepth instance) with (instance, success) in
          match intermediateStep instance with instance in
          rsBranch instance (subi depth 1)
      else
        match (tryRepairBranch rejectionDepth instance) with (instance, success) in
        match intermediateStep instance with instance in
        rsBranch instance (subi depth 1)
    in
    let instance = rsBranch instance rejectionDepth in
    instance 

  -- Resample a single host at a single node. Will select one of the other states with equal probability
  sem hrmResampleHost : all x. PAssumeRef Int -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleHost nodeRef = | instance -> 
    match getSt instance with HRMState st in
    let catMove = lam x. mkCategorical (normalize (map (lam c. if neqi x c then 1. else 0.) [0, 1, 2])) in
    -- let catMove = lam. lam x. mkCategorical [0., 0., 1.] in
    resampleAssume (Some catMove) nodeRef instance

  -- Resample some hosts at a node from the independence model
  -- We might want to consider tempering or other perturbations of the
  -- independence model distribution
  sem hrmResampleNode : all x. Int -> [Int] -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleNode nodeLabel hKeys = | instance -> 
    match getSt instance with HRMState st in
    match mapLookup nodeLabel st.nodes with Some nodes in
    let hrefs = map (lam s. match mapLookup s nodes with Some href in href) hKeys in
    let catMove = lam x. mkCategorical (normalize (map (lam c. if neqi x c then 1. else 0.) [0, 1, 2])) in
    let instance = foldl (flip (resampleAssume (Some catMove))) instance hrefs in
    instance

  -- Resample some hosts at a node using local belief propagation
  -- This is achieved by computing messages with the transition kernels
  -- on each incident branch
  sem hrmResampleNodeLocalBP : all x. Int -> [Int] -> PValInstance Partial (HRMState x) -> PValInstance Partial (HRMState x)
  sem hrmResampleNodeLocalBP nodeLabel hKeys = | instance -> 
    match getSt instance with HRMState st in
    match mapLookup nodeLabel st.nodes with Some node in
    -- Get the neighbourhood in the tree
    match mapLookup nodeLabel st.topo with Some {left = left, right = right, isRoot = isRoot} in 
    -- Get the states of the child nodes
    -- Compute the left msg
    let leftObsMsg = readPreviousExport (match mapLookup left st.nodeSampleMsgs with Some v in v) instance in
    let leftKernel = readPreviousExport (match mapLookup left st.transitionKernels with Some v in v) instance in
    let leftMsg = matMulExn leftObsMsg (matTranspose leftKernel) in 
    -- Compute the right msg
    let rightObsMsg = readPreviousExport (match mapLookup right st.nodeSampleMsgs with Some v in v) instance in
    let rightKernel = readPreviousExport (match mapLookup right st.transitionKernels with Some v in v) instance in
    let rightMsg = matMulExn rightObsMsg (matTranspose rightKernel) in 

    -- Get the preordered message -- the state at the predecessor times the transition kernel
    let preorderMsg = readPreviousExport (match mapLookup nodeLabel st.preorderMsgs with Some v in v) instance in

    -- Normalize twice to prevent floating point errors
    let combindMsgPart = matNormalize (_matElemMul leftMsg rightMsg) in
    let combindMsg = matNormalize (_matElemMul preorderMsg combindMsgPart) in
      
    -- TODO(ed, 2026-02-22): Think about whether we should temper the distribution
    let temper = lam s. map (lam s. pow s 0.9) s in 
    let getDist = lam r. normalize (temper (matGetRowAsSeq r combindMsg)) in
    let resampleHost = lam instance. lam h. 
      let dist = getDist (subi h 1) in
      -- printArr ["Dist ", strJoin "," (map (lam f. float2string (roundf f 4)) dist)];
      let dk = lam. mkCategorical dist in
      let href = (match mapLookup h node with Some v in v) in
      resampleAssume (Some dk) href instance
    in
    let instance = intermediateStep (foldl resampleHost instance hKeys) in
    instance


  -- MCMC move entrypoint
  sem hrmResampleAligned : all x. Float -> PValInstance Partial (HRMState x) -> (PValInstance Partial (HRMState x), String)
  sem hrmResampleAligned globalProb = | instance ->
    match getSt instance with HRMState st in
    let nLeafs = length st.interactions in
    let nB = int2float (muli (subi nLeafs 1) 2) in
    let rbSchedule =
      [ (2.,         "Huge mu      ", hrmResampleMu 5.0)
      , (2.,         "Large mu     ", hrmResampleMu 1.0)
      , (5.,         "Medium mu    ", hrmResampleMu 0.2)
      , (1.,         "Beta         ", hrmResampleBeta 1.)
      , (2.,         "Large  lambda", hrmResampleLambda 10.)
      , (5.,         "Small  lambda", hrmResampleLambda 25.)
      , (5.,         "Minute lambda", hrmResampleLambda 100.)
      , (divf nB 2., "Block node l ", hrmResampleABlockNode 5 10 10 10 0.75) 
      , (nB,         "Branch     l ", hrmResampleABranch      10 10 10 0.75) 
      , (nB,         "Block node s ", hrmResampleABlockNode 10 10 10 10 0.2) 
      , (mulf nB 2., "Branch     s ", hrmResampleABranch      5 10 10 0.2) 
      ] in
    -- let rbSchedule =
    --   [ (1., "Large mu     ", hrmResampleMu 1.0)
    --   , (1., "Medium mu    ", hrmResampleMu 0.2)
    --   , (1., "Super mu     ", hrmResampleMu 10.)
    --   -- , (1., "Minute mu   ", hrmResampleMu 0.01)
    --   , (1., "Beta         ", hrmResampleBeta 4.)
    --   , (1., "Large  lambda", hrmResampleLambda 10.)
    --   , (1., "Small  lambda", hrmResampleLambda 25.)
    --   , (1., "Minute lambda", hrmResampleLambda 50.)
    --   , (1., "Tiny lambda  ", hrmResampleLambda 100.)
    --   , (50., "Block node   ", hrmResampleABlockNode 5 10 10 10 0.2) -- Weight should depend on the number of branches!
    --   , (50., "Branch       ", hrmResampleABranch 10 10 10 0.2) -- Weight should depend on the number of branches!
    --   , (25., "Block node   ", hrmResampleABlockNode 5 10 10 10 0.75) -- Weight should depend on the number of branches!
    --   , (25., "Branch       ", hrmResampleABranch 10 10 10 0.75) -- Weight should depend on the number of branches!
    --   ] in
    let weights = map (lam t. t.0) rbSchedule in
    let moveNames = map (lam t. t.1) rbSchedule in
    let moves = map (lam t. t.2) rbSchedule in
    -- printLn "Starting move";
    let moveId = _sampleNonUniform weights in
    let moveName = get moveNames moveId in
    let instance = (get moves moveId) instance in
    -- printLn "Done with move";
    -- recursive let applyn = lam n. lam f. lam x.
    --   if leqi n 0 then x
    --   else applyn (subi n 1) f (f x)
    -- in
    -- let instance = foldl (lam ist. lam mw. match mw with (w, m) in applyn (roundfi w) m ist) instance rbSchedule in
    -- printJsonLn (hrmStateToDebugJson instance (getSt instance));
    let instance = intermediateStep instance in
    -- printLn "Done with intermediate step";
    -- hrmPrintState false instance;
    (instance, moveName)
  
  sem hrmPrintState : all partial. all x. all y. Bool -> PValInstance partial (HRMState x) -> ()
  sem hrmPrintState mode = | instance ->
    if true then
    match getSt instance with HRMState x in
    (if false then
      let showMat = lam mat. lam d.
        let toString = lam f. float2string (roundf f d) in
        let showRow = lam i. join ["[", strJoin ", " (map (lam j. toString (matGetExn mat i j)) (range 0 mat.n 1)), "]"] in
        join ["[", strJoin "\n" (map showRow (range 0 mat.m 1)), "]"]
      in
      let getMat = lam ref. showMat (readPreviousExport ref instance) 5 in
      printLn "Transkernels";
      (mapMapWithKey (lam k. lam ref. printLn (strJoin " " [int2string k, getMat ref])) (x.transitionKernels));
      printLn "Node msgs";
      (mapMapWithKey (lam k. lam ref. printLn (strJoin " " [int2string k, getMat ref])) (x.nodeSampleMsgs));
      printLn "Preorder msgs";
      (mapMapWithKey (lam k. lam ref. printLn (strJoin " " [int2string k, getMat ref])) (x.preorderMsgs));
      printLn (strJoin ", " (map int2string (mapKeys x.nodeSampleMsgs))) 
    else ());
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
            let padLen = maxi (subi 5 (length f)) 1 in
            concat (make (maxi (subi 5 (length f)) 0) ' ') f 
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
        printArr ["Node ", int2string label];
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
    let treeDepth = depth x.tree in
    let treelines = printTree x.tree "" false treeDepth in
    let subrootLines = match x.subrootLabel with Some label then
      match mapLookup label x.nodes with Some hosts in
      match mapLookup label x.nodeSuppWeights with Some branchWeights in
      match mapLookup label x.likrWeights with Some likw in
        [join [ int2string label 
        , ":"
        , join (make (muli (addi treeDepth 1) 4 ) " ")
        , "{"
        , strJoin ", " (map (compose int2string readA) (mapValues hosts))
        , "}, "
        , "b: "
        , checkW branchWeights
        , ", likr: "
        , float2string (readW likw)
        ]]
      else [] in
    let treelines = concat subrootLines treelines in 
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
    else ()

  sem hrmPrintBranch : all partial. all x. Int -> PValInstance partial (HRMState x) -> () 
  sem hrmPrintBranch node = | instance -> 
    if true then
    match getSt instance with HRMState st in
    printLn (join ["Subbranch node: ", int2string node]);
    match mapLookup node st.branchTimes with Some hrefs in
    let hKeys = mapKeys hrefs in 
    (map (lam h. hrmPrintBridge node h instance) hKeys);
    ()
    else ()

  sem hrmPrintNode : all partial. all x. all y. Int -> PValInstance partial (HRMState x) -> ()
  sem hrmPrintNode nodeLabel = | instance -> 
    match getSt instance with HRMState st in
    match mapLookup nodeLabel st.nodes with Some node in
    let strH = lam href. int2string (readPreviousAssume href instance) in ()
    -- printArr ["INSIDE ACCEPT: New node state: ", strJoin ", " (map strH (mapValues node))]

 

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
  sem mkMCMCConfig : all x. (Int -> x -> ()) -> Int -> Float -> MCMCConfig (HRMState (PExportRef x)) x String
  sem mkMCMCConfig writer iterations = | globalProb ->
    { getSample = hrmReadExport
    , step = hrmResampleAligned globalProb
    , cmpMoves = cmpString
    , sampleWriter = writer 
    , iterations = iterations
    }
end
