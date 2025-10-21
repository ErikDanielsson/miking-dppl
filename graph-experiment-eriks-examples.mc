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
        p_bind_ st #frozen"ctmc" s_ list 
      else
        p_pure st a in

    -- Set up the initial and terminal values
    match p_pure st ctmc_a with (st, a_) in
    match p_apply st gtime a_ with (st, dist_t) in
    match p_assume st simpleStore dist_t with (st, t0_) in
    match p_map st (subf ctmc_T) t0_ with (st, t_) in
    match p_map st (lam t. (ctmc_a, t)) t_ with (st, s) in
    match p_bind_ st #frozen"ctmc" s (PVHCons (gtrans, PVHCons (gtime, PVHNil ()))) with (st, res) in
    match p_weight_ st (lam e. if eqi e ctmc_b then 0. else log 0.) res with st in
    match p_map st ((flip get) 0) params with (st, l01) in
    p_export st simpleExport l01
  end

lang RunCTMCBridgeMut = CTMCBridge + MCMCPVal + MutPVal
end

lang RunCTMCBridgePersistent = CTMCBridge + MCMCPVal + SimplePersistentPVal
end

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
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut" (timeF run);
  let run =
    use RunCTMCBridgePersistent in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent" (timeF run);
  let run =
    use RunCTMCBridgePersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
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

  let subrootState = assume (UniformDiscrete 0 2) in
  walk stree subrootT subrootState;
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
      PValState () z -> (Int, Float) -> PValHList z Unknown -> (PValState () z, PVal z Unknown) =
      lam st. lam s. lam list.
      recursive let recur : all z.
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
          p_bind_ st #frozen"recur" s_ list 
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
      p_bind_ st #frozen"recur" s list
    in
    recursive let walk : all z.
      PValState () z -> (STree, (Int, Float)) -> PValHList z Unknown -> (PValState () z, PVal z Unknown) =
      lam st. lam arg. lam list. 
      match arg with (stree, s) in
      switch stree 
        case SNode n then
          match s with (a, t) in
          match p_pure st (a, t, n.t) with (st, ts) in
          match p_map st (lam ts.
            match ts with (a, prev_t, this_t) in
            (a, subf prev_t this_t)
          ) ts with (st, s_) in
          match p_bind_ st #frozen"branch" s_ list with (st, res) in
          match p_map st (lam a. (n, a)) res with (st, ns) in
          -- Left
          match p_map st (lam ns. match ns with (tree, a) in (tree.left, (a, tree.t))) ns with (st, leftS) in
          match p_bind_ st #frozen"walk" leftS list with (st, _) in
          -- Right
          match p_map st (lam ns. match ns with (tree, a) in (tree.right, (a, tree.t))) ns with (st, rightS) in
          p_bind_ st #frozen"walk" rightS list 
        case SLeaf l then
          match p_pure st s with (st, s_) in
          match p_bind_ st #frozen"branch" s_ list with (st, res) in
          match p_weight_ st (lam e. if eqi e l then 0. else log 0.) res with st in
          p_pure st () 
      end
    in
    match p_pure st (p_uniformDiscrete 0 2) with (st, srdist) in
    match p_assume st simpleStore srdist with (st, sr) in
    match p_map st (lam r. (stree, (r, subrootT))) sr with (st, s) in
    -- Run the recursion
    match p_bind_ st #frozen"walk" s (PVHCons (gtrans, PVHCons (gtime, PVHNil ()))) with (st, res) in
    match p_map st ((flip get) 0) params with (st, l01) in
    p_export st simpleExport l01
  end

lang RunTreeHistoryReconstructionMut = TreeHistoryReconstruction + MCMCPVal + MutPVal
end

lang RunTreeHistoryReconstructionPersistent = TreeHistoryReconstruction + MCMCPVal + SimplePersistentPVal
end

lang RunTreeHistoryReconstructionPersistent2 = TreeHistoryReconstruction + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== Tree history reconstruction, forward ===";
  let globalProb = 0.1 in
  let iterations = 100000 in
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
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut" (timeF run);
  let run =
    use RunTreeHistoryReconstructionPersistent in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent" (timeF run);
  let run =
    use RunTreeHistoryReconstructionPersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
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


-- === Tree history reconstruction, BP from leafs ===

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

type MsgTree 
con MsgLeaf : Mat Float -> MsgTree
con MsgNode : {left : MsgTree, right : MsgTree, t: Float, msg: Mat Float} -> MsgTree

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
  -- Compute the postorder mess§ages 
  recursive let makeMessages STree -> Float -> Mat Float 
 
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

  let subrootState = assume (UniformDiscrete 0 2) in
  walk stree subrootT subrootState;
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
      PValState () z -> (Int, Float) -> PValHList z Unknown -> (PValState () z, PVal z Unknown) =
      lam st. lam s. lam list.
      recursive let recur : all z.
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
          p_bind_ st #frozen"recur" s_ list 
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
      p_bind_ st #frozen"recur" s list
    in
    recursive let walk : all z.
      PValState () z -> (STree, (Int, Float)) -> PValHList z Unknown -> (PValState () z, PVal z Unknown) =
      lam st. lam arg. lam list. 
      match arg with (stree, s) in
      switch stree 
        case SNode n then
          match s with (a, t) in
          match p_pure st (a, t, n.t) with (st, ts) in
          match p_map st (lam ts.
            match ts with (a, prev_t, this_t) in
            (a, subf prev_t this_t)
          ) ts with (st, s_) in
          match p_bind_ st #frozen"branch" s_ list with (st, res) in
          match p_map st (lam a. (n, a)) res with (st, ns) in
          -- Left
          match p_map st (lam ns. match ns with (tree, a) in (tree.left, (a, tree.t))) ns with (st, leftS) in
          match p_bind_ st #frozen"walk" leftS list with (st, _) in
          -- Right
          match p_map st (lam ns. match ns with (tree, a) in (tree.right, (a, tree.t))) ns with (st, rightS) in
          p_bind_ st #frozen"walk" rightS list 
        case SLeaf l then
          match p_pure st s with (st, s_) in
          match p_bind_ st #frozen"branch" s_ list with (st, res) in
          match p_weight_ st (lam e. if eqi e l then 0. else log 0.) res with st in
          p_pure st () 
      end
    in
    match p_pure st (p_uniformDiscrete 0 2) with (st, srdist) in
    match p_assume st simpleStore srdist with (st, sr) in
    match p_map st (lam r. (stree, (r, subrootT))) sr with (st, s) in
    -- Run the recursion
    match p_bind_ st #frozen"walk" s (PVHCons (gtrans, PVHCons (gtime, PVHNil ()))) with (st, res) in
    match p_map st ((flip get) 0) params with (st, l01) in
    p_export st simpleExport l01
  end

lang RunTreeHistoryReconstructionMut = TreeHistoryReconstruction + MCMCPVal + MutPVal
end

lang RunTreeHistoryReconstructionPersistent = TreeHistoryReconstruction + MCMCPVal + SimplePersistentPVal
end

lang RunTreeHistoryReconstructionPersistent2 = TreeHistoryReconstruction + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== Tree history reconstruction, forward ===";
  let globalProb = 0.1 in
  let iterations = 100000 in
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
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut" (timeF run);
  let run =
    use RunTreeHistoryReconstructionPersistent in
    let instance = instantiate #frozen"run" ([], ()) in
    lam. (mcmc {getSample = simpleRead, step = simpleResample globalProb, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc Persistent" (timeF run);
  let run =
    use RunTreeHistoryReconstructionPersistent2 in
    let instance = instantiate #frozen"run" ([], ()) in
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

