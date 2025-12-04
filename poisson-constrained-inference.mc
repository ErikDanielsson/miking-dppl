include "graph-experiment-2.mc"


lang PoissonResample = PValInterface
  -- type PoissonState x = ([SomePAssumeRef], x)
  type NodeID = Int
  type PoissonState c =
    { poissonStart : Option SomePAssumeRef -- This should be the initial assume of the Poisson process, so that we can resample the Poisson
    , globalMu : Option SomePAssumeRef 
    , bridgeWeight : Option SomePWeightRef
    , export : c
    }

  sem poissonStartStore : all b. all c. PoissonState c -> PAssumeRef Float -> PoissonState c 
  sem poissonStartStore rs = | r -> 
    { poissonStart = Some (SomePAssumeRef r)
    , globalMu = rs.globalMu
    , bridgeWeight = rs.bridgeWeight
    , export = rs.export
    }
  
  sem bridgeWeight : all c. PoissonState c -> PWeightRef -> PoissonState c
  sem bridgeWeight rs = | w -> 
    { poissonStart = rs.poissonStart
    , globalMu = rs.globalMu
    , bridgeWeight = Some (SomePWeightRef w)
    , export = rs.export
    }

  sem muStore : all b. all c. PoissonState c -> PAssumeRef b -> PoissonState c
  sem muStore rs = | mu -> 
    { poissonStart = rs.poissonStart
    , globalMu = Some (SomePAssumeRef mu)
    , bridgeWeight = rs.bridgeWeight
    , export = rs.export
    }

  sem muExport : all a. all b. all x2. PoissonState () -> PExportRef x2 -> PoissonState (PExportRef x2)
  sem muExport rs = | r ->
    { poissonStart = rs.poissonStart
    , globalMu = rs.globalMu
    , bridgeWeight = rs.bridgeWeight
    , export = r
    }

  sem poissonResample : all a. all b. all c. Float -> PValInstance Partial (PoissonState c) -> PValInstance Partial (PoissonState c)
  sem poissonResample globalProb = | instance ->
    let st = getSt instance in
    let doResample = lam instance. lam someAssume.
      match someAssume with Some (SomePAssumeRef x) in
      resampleAssume (lam d. lam. d) x instance in
    doResample instance st.poissonStart
  
  sem poissonRejectionMove : all a. all b. all c. Int -> PValInstance Partial (PoissonState c) -> PValInstance Partial (PoissonState c)
  sem poissonRejectionMove rejMax = | instance -> 
    -- Here we would like to resample until we get a positive weight (with some upper limit)
    recursive let rejectionSampling = lam n. lam f. lam inst.
      let inst = f inst in
      let st = getSt inst in
      match st.bridgeWeight with Some (SomePWeightRef w) in
      printLn (join ["Should we reject? ", bool2string ((not (checkPreviousWeight w instance)) )]);
      if and (neqi n 0) (not (checkPreviousWeight w instance)) then -- Here we should also have a weight check
        printLn "Rejection";
        rejectionSampling (subi n 1) f inst 
      else
        (if lti n rejMax then printLn (join ["Rejections: ", int2string (subi rejMax n)]) else ());
        inst in
    printLn (join ["Rejection move. yay"]);
    rejectionSampling rejMax (poissonResample 0.0) instance
  
  -- Resample the rate parameter with a reciprocal distribution
  sem muResample : all a. all b. all c. Float -> PValInstance Partial (PoissonState c) -> PValInstance Partial (PoissonState c)
  sem muResample scale = | instance ->
    let st = getSt instance in
    let doResample = lam instance. lam someAssume.
      match someAssume with Some (SomePAssumeRef x) in
      let c = exp (divf scale 2.) in
      let reciprocalKernel = lam. lam s. p_reciprocal (divf s c) (mulf s c) in
      resampleAssume reciprocalKernel x instance in
    doResample instance st.globalMu 
  
  sem multResample : all a. all b. all c. Int -> PValInstance Partial (PoissonState c) -> PValInstance Partial (PoissonState c)
  sem multResample rejMax = | instance -> 
    printLn "";
    printLn "Starting resample!";
    let moves = [muResample 1., poissonRejectionMove 1000] in
    -- Here we need could use any distribution as long as each kernel is invariant
    let move = _chooseUniform moves in
    move instance 


  sem muRead : all a. all b. all x. all complete. PValInstance complete (PoissonState (PExportRef x)) -> x
  sem muRead = | instance ->
    readPreviousExport (getSt instance).export instance

end

-- As a small recursive example we consider the model: \mu \sim \Exp(1) and S_i \sim \Exp(\mu) with X(t) = |\{i : \sum_i S_i < t \}|

let obs_t = 10.
let obs_n = 5 
let eta = 1.0

let analytical = lam. assume (Gamma (int2float (addi obs_n 1)) (divf 1. (addf obs_t 1.)))

let baseline = lam. 
  let mu = assume (Exponential eta) in
  recursive let work = lam acc. lam t.
    if geqf t 0.
    then
      let s = assume (Exponential eta) in
      work (addi acc 1) (subf t s)
    else acc in
  let s = assume (Exponential mu) in
  let t = subf obs_t s in
  let n = work 0 t in
  (if eqi n obs_n then () else weight (log 0.));
  mu
  
lang PoissonBridge = PoissonResample
  sem run = | st -> 
    match p_pure st (p_exponential 1.) with (st, dist_mu) in
    match p_assume st muStore dist_mu with (st, mu) in
    -- Construct the distribution for the recursion
    match p_map st p_exponential mu with (st, dist_s) in
    -- Construct the Poisson recursion
    recursive let poisson = lam n. lam st. lam t.
      let recur = lam st. lam t. poisson (addi n 1) st t in
      if geqf t 0. then
        -- Draw the next time
        match p_assume_ st dist_s with (st, s) in
        match p_map st (
          lam s. printLn (join [int2string n, ": ", float2string s])
        ) s with (st, _) in
        match p_map st (subf t) s with (st, t) in
        -- Set up the recursive call
        p_bind_ st recur t
      else
        p_pure st n in

    -- Set up the initial and terminal values
    match p_assume st poissonStartStore dist_s with (st, s) in
    match p_map st (subf obs_t) s with (st, t) in
    let start = poisson 0 in
    match p_bind_ st start t with (st, res) in
    match p_map st (lam n. printLn (join ["Should be n: ", int2string obs_n, " sampled n: ", int2string n])) res with (st, _) in
    match p_weight st bridgeWeight (lam n. if eqi n obs_n then 0.0 else log 0.) res with st in
    -- match p_weight st bridgeWeight (lam n. int2float n) res with st in
    -- p_export st muExport mu
    match p_map st (lam i. divf (int2float i) 50.) res with (st, res) in
    p_export st muExport res 
  end

lang RunPoissonBridgeMut = PoissonBridge + MCMCPVal + MutPVal
end

lang RunPoissonBridgePersistent2 = PoissonBridge + MCMCPVal + SimplePersistentPVal2
end

let result =
  printLn "\n=== Poisson bridge ===";
  let globalProb = 0.0 in
  let iterations = 1000 in
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
  let initState = lam. { poissonStart = None (), bridgeWeight = None (), globalMu = None (), export = () } in
  let run =
    use RunPoissonBridgeMut in
    let instance = instantiate #frozen"run" (initState ()) in
    lam. (mcmc {getSample = muRead, step = multResample 10, iterations = iterations} instance).samples in
  summarizePVal "pval mcmc mut" (timeF run);
  -- let run =
  --   use RunPoissonBridgePersistent2 in
  --   let instance = instantiate #frozen"run" (initState ()) in
  --   lam. (mcmc {getSample = muRead, step = multResample 10, iterations = iterations} instance).samples in
  -- summarizePVal "pval mcmc Persistent2" (timeF run);
  -- let run = lam.
  --   infer (LightweightMCMC {cps = "none", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  -- summarizeBaseline "baseline mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  summarizeBaseline "baseline mcmc-lw partial" (timeF run);
  -- let run = lam.
  --   infer (LightweightMCMC {cps = "full", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) baseline in
  -- summarizeBaseline "baseline mcmc-lw full" (timeF run);
  -- let run = lam.
  --   infer (LightweightMCMC {cps = "none", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) analytical in
  -- summarizeBaseline "analytical mcmc-lw" (timeF run);
  let run = lam.
    infer (LightweightMCMC {cps = "partial", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) analytical in
  summarizeBaseline "analytical mcmc-lw partial" (timeF run);
  -- let run = lam.
  --   infer (LightweightMCMC {cps = "full", globalProb = globalProb, continue = (iterations, lam r. lam. (subi r 1, neqi r 1))}) analytical in
  -- summarizeBaseline "analytical mcmc-lw full" (timeF run);
  ()

mexpr
-- TODO(vipa, 2025-09-25): For whatever reason we end up with a Decl
-- without an info field if we have `infer` above but not here. I have
-- no idea why.
let x = infer (Default ()) (lam. ()) in
printLn "\n\nDone";
()

