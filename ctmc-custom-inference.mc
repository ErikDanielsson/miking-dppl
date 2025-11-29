
lang CTMCResample = PValInterface
  -- type HRMState x = ([SomePAssumeRef], x)
  type NodeID = Int
  type BranchState a b c d =
    { branchStart : a -- This should be the initial assume of the branch, so that we can resample the branch
    , globalMu : b 
    , globalLambda : c
    , export : d
    }

  sem branchStore : all a. all b. all c. all d. BranchState a b c d -> PAssumeRef Float -> BranchState a b c (PAssumeRef Float)
  sem branchStore rs = | r -> 
    { branch = snoc rs.branch (SomePAssumeRef r)
    , globalMu = rs.globalMu
    , globalLambda = rs.globalLambda
    , export = rs.export
    }

  sem muStore : all a. all b. all c. all a. BranchState () b c -> PAssumeRef a -> BranchState (PAssumeRef a) b c
  sem muStore rs = | mu -> 
    { branch = snoc rs.branch (SomePAssumeRef r)
    , globalMu = mu
    , globalLambda = rs.globalLambda
    , export = rs.export
    }

  sem lambdaStore : all a. all b. all c. all a. BranchState a () c -> PAssumeRef b -> BranchState a (PAssumeRef b) c
  sem lambdaStore rs = | lambda -> 
    { branch = snoc rs.branch (SomePAssumeRef r)
    , globalMu = rs.globalMu
    , globalLambda = lambda
    , export = rs.export
    }


--   sem topStore : all a. NodeID -> NodeID -> HRMState () -> PAssumeRef a -> HRMState ()
--   sem topStore label = | pLabel rs r ->
--     let 
--   (snoc rs.0 (SomePAssumeRef r), rs.1)

  sem singleExport : all x2. HRMState () -> PExportRef x2 -> SimpleState (PExportRef x2)
  sem singleExport rs = | r -> { assumes = rs.assumes, export = r }

  sem branchResample : all a. all b. all c. Float -> PValInstance Partial (BranchState a b c) -> PValInstance Partial (BranchState a b c)
  sem branchResample globalProb = | instance ->
    let st = getSt instance in
    let doResample = lam instance. lam someAssume.
      match someAssume with SomePAssumeRef x in
      resampleAssume (lam d. lam. d) x instance in
    if bernoulliSample globalProb then
      foldl doResample instance st.0
    else
      doResample instance (_chooseUniform st.0)

  sem branchRead : all x. all complete. PValInstance complete (HRMState (PExportRef x)) -> x
  sem branchRead = | instance ->
    readPreviousExport (getSt instance).1 instance

lang CTMCBridge = BranchResample
  sem run = | st -> 
    match p_pure st (p_dirichlet [1., 1., 1., 1.]) with (st, dist) in
    match p_assume st Store dist with (st, params) in
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
      PValState () z -> (Int, Float) -> (PValState () z, PVal z Unknown)
      = lam st. lam s. lam list.
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