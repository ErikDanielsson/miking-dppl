include "graph-experiment-2.mc"
include "stdlib::ext/mat-ext.mc"

-- === CTMC Bridge ===

let ctmc_a = 0
let ctmc_b = 2
let ctmc_T = 10.
let baseline = lam.
  let params = assume (Dirichlet [1., 1., 1., 1.]) in
  let l01 = get params 0 in
  let l10 = get params 1 in
  let l12 = get params 2 in
  let l21 = get params 3 in
  let rates = [l01, addf l10 l12, l21] in
  let embeddedMC = [
    [0., 1., 0.], 
    [divf l10 (get rates 1), 0., divf l21 (get rates 1)], 
    [0., 1., 0.] 
  ] in
  recursive let ctmc = lam a. lam t.
    if geqf t 0. then 
      let b = assume (Categorical (get embeddedMC a)) in
      let t0 = assume (Exponential (get rates a)) in
      let t = subf t t0 in
      ctmc b t
    else a in
  let t0 = assume (Exponential (get rates ctmc_a)) in
  let t = subf ctmc_T t0 in
  let res = ctmc ctmc_a t in
  weight (if eqi ctmc_b res then 0. else log 0.);
  l01
  
lang CTMCBridge = SimpleResample
  sem run = | st -> 
    match p_pure st (p_dirichlet [1., 1., 1., 1.]) with (st, dist) in
    match p_assume st simpleStore dist with (st, params) in
    -- Construct rate vector
    match p_map st (lam l. [get l 0, addf (get l 1) (get l 2), get l 3]) params with (st, rates) in
    match p_map st (lam rates. lam a. p_exponential (get rates a)) rates with (st, gtime) in
    -- Construct embedded Markov chain matrix
    match p_map st (lam l.
      let l10 = get l 1 in
      let l12 = get l 2 in
      let r1 = addf l10 l12 in
      [ [0., 1., 0.] 
      , [divf l10 r1, 0., divf l12 r1] 
      , [0., 1., 0.]
      ]
    ) params with (st, eMC) in
    match p_map st (lam eMC. lam a. p_categorical (get eMC a)) eMC with (st, gtrans) in
    -- Construct the CTMC recursion
    recursive let ctmc : all z.
      PValState () z -> (Int, Float) -> PValHList z Unknown -> (PValState () z, PVal z Unknown)
      = lam st. lam s. lam list.
      match list with PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
      match s with (a, t) in
      if geqf t 0. then
        match p_pure st a with (st, a_) in
        -- Draw the next state
        match p_apply st gtrans a_ with (st, dist_a) in
        match p_assume_ st dist_a with (st, b_) in
        -- Draw the next time
        match p_apply st gtime a_ with (st, dist_t) in
        match p_assume_ st dist_t with (st, t0) in
        match p_map st (subf t) t0 with (st, t_) in
        -- Set up the recursive call
        match p_map st (lam a. lam t. (a, t)) b_ with (st, s1_) in
        match p_apply st s1_ t_ with (st, s_) in
        p_bind_ st ctmc s_ list 
      else
        p_pure st a in

    -- Set up the initial and terminal values
    match p_pure st ctmc_a with (st, a_) in
    match p_apply st gtime a_ with (st, dist_t) in
    match p_assume st simpleStore dist_t with (st, t0_) in
    match p_map st (subf ctmc_T) t0_ with (st, t_) in
    match p_map st (lam t. (ctmc_a, t)) t_ with (st, s) in
    match p_bind_ st ctmc s with (st, res) in
    match p_weight_ st (lam e. if eqi e ctmc_b then 0. else log 0.) res with st in
    match p_map st ((flip get) 0) params with (st, l01) in
    p_export st simpleExport l01
  end

lang RunCTMCBridgeMut = CTMCBridge + MCMCPVal + MutPVal
end

-- lang RunCTMCBridgePersistent = CTMCBridge + MCMCPVal + SimplePersistentPVal
-- end

lang RunCTMCBridgePersistent2 = CTMCBridge + MCMCPVal + SimplePersistentPVal2
end

let shouldRun = false
let result = if shouldRun then
  printLn "\n=== CTMC bridge ===";
  let globalProb = 0.1 in
  let iterations = 100000 in
  let toString = interval2string in
  let mkHisto = bucket 10 0.0 1.0 in
  let summarizePVal = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto res)) else () in
  let summarizeBaseline = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in
  let run =
    use RunCTMCBridgeMut in
    let instance = instantiate run ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut" (timeF run);
  -- let run =
  --   use RunCTMCBridgePersistent in
  --   let instance = instantiate run ([], ()) in
  --   lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  -- summarizePVal "pval mcmc Persistent" (timeF run);
  let run =
    use RunCTMCBridgePersistent2 in
    let instance = instantiate run ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  summarizeBaseline "mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  summarizeBaseline "mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  summarizeBaseline "mcmc-lw full" (timeF run);
  ()
  else ()

-- === Tree history reconstruction, forward process ===

type STree
-- Each leaf is at time 0.0 and contains a state
con SLeaf : Int -> STree
-- Each node contains its time 
con SNode : {left : STree, right : STree, t: Float} -> STree

let stree = SNode {
  left = SNode {
    left = SLeaf 0,
    right = SLeaf 0,
    t = 0.3
  },
  right = SNode {
    left = SLeaf 0,
    right = SLeaf 0,
    t = 0.5
  },
  t = 1.
}

let subrootT = 2.

let baseline = lam.
  -- Set up the model parameters
  let params = assume (Dirichlet [1., 1., 1., 1.]) in
  let l01 = get params 0 in
  let l10 = get params 1 in
  let l12 = get params 2 in
  let l21 = get params 3 in
  let rates = [l01, addf l10 l12, l21] in
  let embeddedMC = [
    [0., 1., 0.], 
    [divf l10 (get rates 1), 0., divf l21 (get rates 1)], 
    [0., 1., 0.] 
  ] in

  -- Simulate a single CTMC 
  let branch : Int -> Float -> Int = lam a. lam t.
    recursive let recur = lam a. lam t.
      if geqf t 0. then 
        let b = assume (Categorical (get embeddedMC a)) in
        let t0 = assume (Exponential (get rates a)) in
        let t = subf t t0 in
        recur b t
      else a in
    let t0 = assume (Exponential (get rates a)) in
    let t = subf t t0 in
    recur a t in

 -- Simulate from the root and check if we sampled the tip states correctly
  recursive let walk : STree -> Float -> Int -> () = lam tree. lam t. lam a.
    switch tree 
      case SLeaf l then 
        let b = branch a t in
        weight (if eqi l b then 0. else log 0.)
      case SNode n then
        let b = branch a (subf t n.t) in
        walk n.left n.t b;
        walk n.right n.t b
    end
  in

  (switch stree 
    case SLeaf _ then ()
    case SNode n then
    let rootState = assume (UniformDiscrete 0 2) in
    walk n.left n.t rootState;
    walk n.right n.t rootState
  end);
  l01

lang TreeHistoryReconstruction = SimpleResample
  sem run = | st -> 
    match p_pure st (p_dirichlet [1., 1., 1., 1.]) with (st, dist) in
    match p_assume st simpleStore dist with (st, params) in
    -- Construct rate vector
    match p_map st (lam l. [get l 0, addf (get l 1) (get l 2), get l 3]) params with (st, rates) in
    match p_map st (lam rates. lam a. p_exponential (get rates a)) rates with (st, gtime) in
    -- Construct embedded Markov chain matrix
    match p_map st (lam l.
      let l10 = get l 1 in
      let l12 = get l 2 in
      let r1 = addf l10 l12 in
      [ [0., 1., 0.] 
      , [divf l10 r1, 0., divf l12 r1] 
      , [0., 1., 0.]
      ]
    ) params with (st, eMC) in
    match p_map st (lam eMC. lam a. p_categorical (get eMC a)) eMC with (st, gtrans) in

    -- Construct the CTMC recursion
    let branch : all z.
      PValState () z -> (Int, Float) -> (PValState () z, PVal z Unknown) =
      lam st. lam s. lam list.
      recursive let recur : all z.
        PValState () z -> (Int, Float) -> (PValState () z, PVal z Unknown)
        = lam st. lam s. lam list.
        match list with PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
        match s with (a, t) in
        if geqf t 0. then
          match p_pure st a with (st, a_) in
          -- Draw the next state
          match p_apply st gtrans a_ with (st, dist_a) in
          match p_assume_ st dist_a with (st, b_) in
          -- Draw the next time
          match p_apply st gtime a_ with (st, dist_t) in
          match p_assume_ st dist_t with (st, t0) in
          match p_map st (subf t) t0 with (st, t_) in
          -- Set up the recursive call
          match p_map st (lam a. lam t. (a, t)) b_ with (st, s1_) in
          match p_apply st s1_ t_ with (st, s_) in
          p_bind_ st recur s_ list 
        else
          p_pure st a
      in
      match list with PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
      -- Get the initial state
      match s with (a, t) in
      match p_pure st a with (st, a_) in
      -- Simulate the first event time
      match p_apply st gtime a_ with (st, dist_t) in
      match p_assume_ st dist_t with (st, t0_) in
      match p_map st (subf t) t0_ with (st, t_) in
      match p_map st (lam t. (ctmc_a, t)) t_ with (st, s) in
      -- Simulate the rest of the CTMC
      p_bind_ st recur s list
    in
    recursive let walk : all z.
      PValState () z -> (STree, (Int, Float)) -> (PValState () z, PVal z Unknown) =
      lam st. lam arg.
      match arg with (stree, s) in
      switch stree 
        case SNode n then
          match s with (a, t) in
          match p_pure st (a, t, n.t) with (st, ts) in
          match p_map st (lam ts.
            match ts with (a, prev_t, this_t) in
            (a, subf prev_t this_t)
          ) ts with (st, s_) in
          match p_bind_ st branch s_ list with (st, res) in
          match p_map st (lam a. (n, a)) res with (st, ns) in
          -- Left
          match p_map st (lam ns. match ns with (tree, a) in (tree.left, (a, tree.t))) ns with (st, leftS) in
          match p_bind_ st walk leftS list with (st, _) in
          -- Right
          match p_map st (lam ns. match ns with (tree, a) in (tree.right, (a, tree.t))) ns with (st, rightS) in
          p_bind_ st walk rightS list 
        case SLeaf l then
          match p_pure st s with (st, s_) in
          match p_bind_ st branch s_ list with (st, res) in
          match p_weight_ st (lam e. if eqi e l then 0. else log 0.) res with st in
          p_pure st () 
      end
    in
    match (switch stree 
      -- If we just have a root node then do nothing
      case SLeaf _ then
        p_pure st () 
      -- This is where all work is done
      case SNode n then
        match p_pure st (p_uniformDiscrete 0 2) with (st, srdist) in
        match p_assume st simpleStore srdist with (st, sr) in
        match p_map st (lam r. (n.left, (r, n.t))) sr with (st, left) in
        match p_map st (lam r. (n.right, (r, n.t))) sr with (st, right) in
        -- Run the recursion
        match p_bind_ st walk left (PVHCons (gtrans, PVHCons (gtime, PVHNil ()))) with (st, res) in
        match p_bind_ st walk right (PVHCons (gtrans, PVHCons (gtime, PVHNil ()))) with (st, res) in
        (st, res)
    end) with (st, res) in
    match p_map st ((flip get) 0) params with (st, l01) in
    p_export st simpleExport l01
  end

lang RunTreeHistoryReconstructionMut = TreeHistoryReconstruction + MCMCPVal + MutPVal
end

-- lang RunTreeHistoryReconstructionPersistent = TreeHistoryReconstruction + MCMCPVal + SimplePersistentPVal
-- end

lang RunTreeHistoryReconstructionPersistent2 = TreeHistoryReconstruction + MCMCPVal + SimplePersistentPVal2
end

-- let result =
--   printLn "\n=== Tree history reconstruction, forward ===";
--   let globalProb = 0.1 in
--   let iterations = 100000 in
--   let toString = interval2string in
--   let mkHisto = bucket 10 0. 1. in
--   let summarizePVal = lam label. lam pair.
--     match pair with (time, res) in
--     printLn (join [float2string time, "ms (", label, ")"]);
--     if showHistogram then printLn (hist2string toString (mkHisto res)) else () in
--   let summarizeBaseline = lam label. lam pair.
--     match pair with (time, res) in
--     printLn (join [float2string time, "ms (", label, ")"]);
--     if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in
--   let run =
--     use RunTreeHistoryReconstructionMut in
--     let instance = instantiate run ([], ()) in
--     lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
--   summarizePVal "pval mcmc mut" (timeF run);
--   let run =
--     use RunTreeHistoryReconstructionPersistent in
--     let instance = instantiate run ([], ()) in
--     lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
--   summarizePVal "pval mcmc Persistent" (timeF run);
--   let run =
--     use RunTreeHistoryReconstructionPersistent2 in
--     let instance = instantiate run ([], ()) in
--     lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
--   summarizePVal "pval mcmc Persistent2" (timeF run);
--   let run = lam.
--     infer (LightweightMCMC {cps = "none", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
--   summarizeBaseline "mcmc-lw" (timeF run);
--   let run = lam.
--     infer (LightweightMCMC {cps = "partial", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
--   summarizeBaseline "mcmc-lw partial" (timeF run);
--   let run = lam.
--     infer (LightweightMCMC {cps = "full", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
--   summarizeBaseline "mcmc-lw full" (timeF run);
--   ()


-- === Tree history reconstruction, BP from leafs ===

type STree
-- Each leaf is at time 0.0 and contains a state
con SLeaf : Int -> STree
-- Each node contains its time 
con SNode : {left : STree, right : STree, t: Float} -> STree

type MsgTree 
con MsgLeaf : Mat Float -> MsgTree
con MsgNode :
  { left : MsgTree
  , leftKernel: Mat Float -- The Markov kernel describing the transition probility from this node to the left node
  , right : MsgTree
  , rightKernel: Mat Float -- The Markov kernel describing the transition probility from this node to the right node
  , t: Float
  , msg: Mat Float
  } -> MsgTree

let stree = SNode {
  left = SNode {
    left = SLeaf 1,
    right = SLeaf 2,
    t = 0.3
  },
  right = SNode {
    left = SLeaf 2,
    right = SLeaf 2,
    t = 0.5
  },
  t = 1.
}
-- let stree = SNode {
--   left = SLeaf 1,
--   right = SLeaf 2,
--   t = 1.
-- }

let printMat : Mat Float -> () = lam mat.
  printLn (join ["m:", int2string mat.m, ",n:", int2string mat.n])

let sKronecker = lam n. lam i. map (lam j. if eqi i j then 1. else 0.) (range 0 n 1)

let kroneckers : [Int] -> Int -> Mat Float = lam is. lam ncols.
  let nrows = length is in
  let flatMap = lam f. compose (foldl concat []) (map f) in
  let sKroneckers = flatMap (sKronecker ncols) is in
  let mat = matFromArrExn nrows ncols (extArrOfSeq extArrKindFloat64 sKroneckers) in
  -- printMat mat;
  mat

let transKernels : Mat Float -> Float -> (Mat Float, Mat Float) = lam q. lam t.
  let forward = matExpExn (matScale t q) in
  let backward = matTranspose forward in
  (forward, backward)

let mvMsg : Mat Float -> Mat Float -> Mat Float = lam k. lam m.
  matMulExn m k

let matRowSums : Mat Float -> [Float] = lam mat.
  map (
    lam i. foldl (lam acc. lam j. addf acc (matGetExn mat i j)) 0. (range 0 mat.m 1)
  ) (range 0 mat.m 1) 

-- These should really be replaced by BLAS operations -- is there an interface in OCaml?
let matNormalizeRows : Mat Float -> (Mat Float, Float) = lam mat.
  let sums = matRowSums mat in
  let mat = matCopy mat in
  iteri (lam i. lam s. repeati (lam j. matSetExn mat i j (divf (matGetExn mat i j) (get sums j))) mat.m) sums;
  let logLik = foldl (lam acc. lam s. addf acc (log s)) 0.0 sums in
  (mat, logLik)

let seqNest : all a. [a] -> Int -> Int -> [[a]] = lam l. lam r. lam c.
  let row = lam i.
    let rs = muli i c in
    let re = addi rs c in
    subsequence l rs c in
  map row (range 0 r 1)

let matToSeqs : Mat Float -> [[Float]] = lam mat.
  let seq = extArrToSeq mat.arr in
  seqNest seq mat.m mat.n 

let combineMsgs : Mat Float -> Mat Float -> (Mat Float, Float) = lam l. lam r.
  let unnormalized = matElemMulExn l r in
  matNormalizeRows unnormalized

-- Compute the postorder messages 
recursive let makeMsgs : STree -> Mat Float -> (Mat Float, Float, Float, MsgTree) = 
  lam tree. lam q.
    switch tree 
      case SLeaf l then
        let lDist = kroneckers [l] 3 in
        -- printLn "MakeMsgs";
        -- printMat lDist; 
        (lDist, 0.0, 0.0, MsgLeaf lDist)
      case SNode n then
        -- Left subtree: compute state and push through backwards kernel
        match makeMsgs n.left q with (lDist, lT, logLikL, left) in
        let ldt = subf n.t lT in
        match transKernels q ldt with (lforward, lbackward) in
        let lMsg = mvMsg lbackward lDist in
        -- Right subtree: compute state and push through backwards kernel
        match makeMsgs n.right q with (rDist, rT, logLikR, right) in
        let rdt = subf n.t lT in
        match transKernels q rdt with (rforward, rbackward) in
        let rMsg = mvMsg rbackward rDist in
        match combineMsgs lMsg rMsg with (msg, localLogLik) in 
        -- Accumulate the log likelihood from the left and right trees, and the one from normalizing message.
        -- printLn (join ["Local log likelihood: ", float2string localLogLik]);
        let accLogLik = addf localLogLik (addf logLikL logLikR) in
        ( msg
        , n.t
        , accLogLik
        , MsgNode
          { left = left
          , leftKernel = lforward
          , right = right
          , rightKernel = rforward
          , t = n.t
          , msg = msg
          }
        ) 
    end
end

let baseline = lam.
  -- Set up the model parameters
  let params = assume (Dirichlet [1., 1., 1., 1.]) in
  let l01 = get params 0 in
  let l10 = get params 1 in
  let l12 = get params 2 in
  let l21 = get params 3 in
  let rates = [l01, addf l10 l12, l21] in
  let embeddedMC = [
    [0., 1., 0.], 
    [divf l10 (get rates 1), 0., divf l21 (get rates 1)], 
    [0., 1., 0.] 
  ] in
  let q = matFromArrExn 3 3 (extArrOfSeq extArrKindFloat64 [
    negf l01, l01                , 0.       , 
    l10     , negf (addf l10 l12), l12      , 
    0.      , l21                , negf l21
  ]) in

  -- Simulate the nodes using the messages and the branches in between them
  let branch : Int -> Float -> Int = lam a. lam t.
    recursive let recur = lam a. lam t.
      if geqf t 0. then 
        let b = assume (Categorical (get embeddedMC a)) in
        let t0 = assume (Exponential (get rates a)) in
        let t = subf t t0 in
        recur b t
      else a in
    let t0 = assume (Exponential (get rates a)) in
    let t = subf t t0 in
    recur a t in
  
  -- A branch with fixed endpoint
  let clamped_branch : Float -> Int -> Int -> () = lam t. lam a. lam b. 
    let e = branch a t in
    weight (if eqi e b then 0. else log 0.) in

  -- Simulate from the root and check if we sampled the tip states correctly
  recursive let walk : MsgTree -> Float -> Mat Float -> [Int] -> () = lam tree. lam t. lam msg. lam as.
    switch tree 
      case MsgLeaf l then 
        let ls = map (lam p. assume (Categorical p)) (matToSeqs l) in
        -- Simulate what happens on the branch
        zipWith (clamped_branch t) as ls;
        ()
      case MsgNode n then
        -- Combine the current message at this node with the message coming from 
        -- the parent node
        -- printLn (join ["Node ", int2string n.msg.n, ",", int2string n.msg.m, " Incoming", int2string msg.n, ",", int2string msg.m]);
        match combineMsgs n.msg msg with (msg, _) in
        let ns = map (lam p. assume (Categorical p)) (matToSeqs msg) in
        -- Simulate what happens on the branch
        (zipWith (clamped_branch t) as ns);
        -- Simulate the left subtree
        let leftMsg = matMulExn (kroneckers ns 3) n.leftKernel in
        -- printLn "LeftMsg";
        walk n.left n.t leftMsg ns; 
        -- Simulate the right subtree
        let rightMsg = matMulExn (kroneckers ns 3) n.rightKernel in
        -- printLn "rightmsg";
        walk n.right n.t rightMsg ns 
    end
  in
  -- Compute the postorder messages
  match makeMsgs stree q with (rootMsg, rootT, accLogLik, msgTree) in

  (switch msgTree 
    case MsgLeaf _ then () -- Trivial case nothing to do
    case MsgNode n then
      -- Weight the program according to the BP likelihood
      let rootSum = foldl addf 0. (matRowSums rootMsg) in
      let rootLogLik = subf (log rootSum) (log (int2float (muli rootMsg.m rootMsg.n))) in
      let totalLogLik = addf rootLogLik accLogLik in
      weight totalLogLik;

      -- Sample the root and prepare the message
      let rootState = map (lam p. assume (Categorical p)) (matToSeqs rootMsg) in
      let rootMsg = kroneckers rootState 3 in
      -- Walk the left tree
      let leftMsg = matMulExn rootMsg n.leftKernel in
      walk n.left n.t leftMsg rootState; 
      -- Walk the right tree
      let rightMsg = matMulExn rootMsg n.rightKernel in
      walk n.right n.t rightMsg rootState
  end);
  l01

lang TreeHistoryReconstruction = SimpleResample
  sem run = | st -> 
    match p_pure st (p_dirichlet [1., 1., 1., 1.]) with (st, dist) in
    match p_assume st simpleStore dist with (st, params) in
    -- Construct rate vector
    match p_map st (lam l. [get l 0, addf (get l 1) (get l 2), get l 3]) params with (st, rates) in
    match p_map st (lam rates. lam a. p_exponential (get rates a)) rates with (st, gtime) in
    -- Construct embedded Markov chain matrix
    match p_map st (lam l.
      let l10 = get l 1 in
      let l12 = get l 2 in
      let r1 = addf l10 l12 in
      [ [0., 1., 0.] 
      , [divf l10 r1, 0., divf l12 r1] 
      , [0., 1., 0.]
      ]
    ) params with (st, eMC) in
    match p_map st (lam eMC. lam a. p_categorical (get eMC a)) eMC with (st, gtrans) in
    
    let construct_q : [Float] -> Mat Float = lam l.
      let l01 = get l 0 in
      let l10 = get l 1 in
      let l12 = get l 2 in
      let l21 = get l 3 in
      matFromArrExn 3 3 (extArrOfSeq extArrKindFloat64 [
        negf l01, l01                , 0.       , 
        l10     , negf (addf l10 l12), l12      , 
        0.      , l21                , negf l21
      ]) in
    match p_map st construct_q params with (st, q) in

    -- Construct the CTMC recursion
    let branch : all z.
      PValState Unknown z -> (Int, Float) -> (PValState Unknown z, PVal z Unknown) =
      lam st. lam s. lam list.
      recursive let recur : all z.
        PValState Unknown z -> (Int, Float) -> (PValState Unknown z, PVal z Unknown)
        = lam st. lam s. lam list.
        match list with PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
        match s with (a, t) in
        if geqf t 0. then
          match p_pure st a with (st, a_) in
          -- Draw the next state
          match p_apply st gtrans a_ with (st, dist_a) in
          match p_assume_ st dist_a with (st, b_) in
          -- Draw the next time
          match p_apply st gtime a_ with (st, dist_t) in
          match p_assume_ st dist_t with (st, t0) in
          match p_map st (subf t) t0 with (st, t_) in
          -- Set up the recursive call
          match p_map st (lam a. lam t. (a, t)) b_ with (st, s1_) in
          match p_apply st s1_ t_ with (st, s_) in
          p_bind_ st recur s_ list 
        else
          p_pure st a
      in
      match list with PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
      -- Get the initial state
      match s with (a, t) in
      match p_pure st a with (st, a_) in
      -- Simulate the first event time
      match p_apply st gtime a_ with (st, dist_t) in
      match p_assume_ st dist_t with (st, t0_) in
      match p_map st (subf t) t0_ with (st, t_) in
      match p_map st (lam t. (ctmc_a, t)) t_ with (st, s) in
      -- Simulate the rest of the CTMC
      p_bind_ st recur s list
    in

    let clamped_branch : all z.
      PValState Unknown z -> PVal z ((Int, Float), Int) -> PValState Unknown z =
      lam st. lam s. 
        match p_map st (lam s. s.0) s with (st, s_) in
        match p_bind_ st branch s_ list with (st, e) in
        match p_map st (lam b. lam s. (b, s.1)) e with (st, partial) in
        match p_apply st partial s with (st, res) in
        p_weight_ st (lam e. if eqi e.0 e.1 then 0. else log 0.) res in

    let sample_helper : all z. all y.
      (PValState Unknown z, [PVal z Int]) -> [Float] -> (PValState Unknown z, [PVal z Int]) =
      lam st_state. lam dist. 
        match st_state with (st, state) in
        match p_pure st (p_categorical dist) with (st, dist) in
        match p_assume_ st simpleStore dist with (st, res) in
        (st, snoc state res) in
    
    let sample_many : all z. 
      PValState Unknown z -> Mat Float -> (PValState Unknown z, [PVal z Int]) =
      lam st. lam msg. 
        foldl sample_helper (st, []) (matToSeqs msg) in

    -- Map a function over two lists, on with deterministic values, one with PVals 
    let zipWithDetPVal_ : all z. all a. all b. all c.   
      PValState Unknown z ->  [a] -> [PVal z b] -> (a -> b -> c) -> (PValState Unknown z, [PVal z c]) =
      lam st. lam as. lam bs. lam f.
        let zipped = zipWith (lam a. lam b. (a, b)) as bs in
        foldl (lam acc. lam v.
          match acc with (st, states) in
          match v with (a, b) in
          match p_map st (f a) b with (st, res) in
          (st, snoc states res)
        ) (st, []) zipped in
    
    let p_sequence = lam st. lam s. foldr (lam a. lam acc.
      match acc with (st, acc) in
      match p_map st cons a with (st, res) in
      match p_apply st res acc with (st, res) in
      (st, res)
    ) (p_pure st []) s in
   
    
    recursive let walk : all z.
      PValState Unknown z -> (MsgTree, Float, Mat Float, [Int]) -> (PValState Unknown z, PVal z Unknown) =
      lam st. lam arg. 
      match arg with (msgTree, t, msg, as) in
      match list with PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
      let branchList = PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
      switch msgTree 
        case MsgLeaf l then
          --printLn "In MsgLeaf";
          -- Sample the leaf state
          match sample_many st l with (st, bs) in
          -- Zip with actual state
          match zipWithDetPVal_ st as bs (lam a. lam b. ((a, t), b)) with (st, states) in
          let st = foldl (clamped_branch branchList) st states in
          p_pure st () 

        case MsgNode n then 
         match combineMsgs msg n.msg with (msg, _) in
          match sample_many st msg with (st, ns) in
          match zipWithDetPVal_ st as ns (lam a. lam b. ((a, t), b)) with (st, states) in
          let st = foldl (clamped_branch branchList) st states in
          match p_sequence st ns with (st, ns) in
          -- Left 
          match p_map st (lam ns. matMulExn (kroneckers ns 3) n.leftKernel) ns with (st, leftMsg) in
          match p_map st (lam msg. lam ns. (n.left, n.t, msg, ns)) leftMsg with (st, left) in
          match p_apply st left ns  with (st, left) in
          match p_bind_ st walk left list with (st, _) in

          -- Right
          match p_map st (lam ns. matMulExn (kroneckers ns 3) n.rightKernel) ns with (st, rightMsg) in
          match p_map st (lam msg. lam ns. (n.right, n.t, msg, ns)) rightMsg with (st, right) in
          match p_apply st right ns  with (st, right) in
          p_bind_ st walk right list 
      end
    in
    -- Compute the postorder messages
    match p_map st (makeMsgs stree) q with (st, msgData) in

    let init : all z.
      PValState () z -> (Mat Float, Float, Float, MsgTree) -> (PValState () z, PVal z Unknown) =
      lam st. lam msgData. 
      match msgData with (rootMsg, rootT, accLogLik, msgTree) in
      match list with PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
      let list = PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
      switch msgTree 
        -- If we just have a root node then do nothing
        case MsgLeaf _ then
          p_pure st () 
        -- This is where all work is done
        case MsgNode n then
          --printLn "Before rootsum";
          let rootSum = foldl addf 0. (matRowSums rootMsg) in
          let rootLogLik = subf (log rootSum) (log (int2float (muli rootMsg.m rootMsg.n))) in
          let totalLogLik =  addf rootLogLik accLogLik in
          match p_pure st totalLogLik with (st, totalLogLik) in
          let st = p_weight_ st (lam a. a) totalLogLik in

          --printLn "Before samplerootmsg";
          match sample_many st rootMsg with (st, rs) in
          -- --printLn "after samplerootmsg";
          match p_sequence st rs with (st, rs) in
          -- Left
          match p_map st (lam rs. matMulExn (kroneckers rs 3) n.leftKernel) rs with (st, leftMsg) in
          match p_map st (lam msg. lam ns. (n.left, n.t, msg, ns)) leftMsg with (st, left) in
          match p_apply st left rs with (st, left) in
          match p_bind_ st walk left list with (st, res) in
          -- Right
          match p_map st (lam rs. matMulExn (kroneckers rs 3) n.rightKernel) rs with (st, rightMsg) in
          match p_map st (lam msg. lam ns. (n.right, n.t, msg, ns)) rightMsg with (st, right) in
          match p_apply st right rs with (st, right) in
          match p_bind_ st walk right list with (st, res) in
          (st, res)
      end
    in
    let list = PVHCons (gtrans, PVHCons (gtime, PVHNil ())) in
    match p_bind_ st init msgData list with (st, res) in
    match p_map st ((flip get) 0) params with (st, l01) in
    p_export st simpleExport l01
  end

lang RunTreeHistoryReconstructionMut = TreeHistoryReconstruction + MCMCPVal + MutPVal
end

-- lang RunTreeHistoryReconstructionPersistent = TreeHistoryReconstruction + MCMCPVal + SimplePersistentPVal
-- end

lang RunTreeHistoryReconstructionPersistent2 = TreeHistoryReconstruction + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== Tree history reconstruction, belief propagation ===";
  let globalProb = 0.1 in
  let iterations = 10000 in
  let toString = interval2string in
  let mkHisto = bucket 10 0. 1. in
  let summarizePVal = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto res)) else () in
  let summarizeBaseline = lam label. lam pair.
    match pair with (time, res) in
    printLn (join [float2string time, "ms (", label, ")"]);
    if showHistogram then printLn (hist2string toString (mkHisto (distEmpiricalSamples res).0)) else () in
  let run =
    use RunTreeHistoryReconstructionMut in
    let instance = instantiate run ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut" (timeF run);
  -- let run =
  --   use RunTreeHistoryReconstructionPersistent in
  --   let instance = instantiate run ([], ()) in
  --   lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  -- summarizePVal "pval mcmc Persistent" (timeF run);
  let run =
    use RunTreeHistoryReconstructionPersistent2 in
    let instance = instantiate run ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent2" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "none", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  summarizeBaseline "mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  summarizeBaseline "mcmc-lw partial" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "full", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  summarizeBaseline "mcmc-lw full" (timeF run);
  ()





mexpr
let x = infer (Default ()) (lam. ()) in
printLn "\n\nDone";
()

