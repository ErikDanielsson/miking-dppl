include "host-rep-mcmc.mc"
include "ext/file-ext.mc"


-- === Single chain MCMC === -- 

let contStateInitBase : () -> Int = lam. 0

let continueBase : all a. all b. all k. Int -> Int -> (Int -> a -> ()) -> Int -> b -> a -> (k, Bool) -> (Int, Bool) =
  lam iterations. lam samplingPeriod. lam writer. lam idx. lam sampleInfo. lam sample. lam.
    -- printLn (strJoin " : " ["Incremental continue", int2string idx, int2string iterations]);
    (if eqi 0 (modi idx samplingPeriod) then
      writer idx sample
    else ()); 
    if eqi idx iterations then 
      (addi idx 1, false)
    else
      (addi idx 1, true)

let temperatureBase : Int -> Float = lam. 1.


-- === Non-reversible PT with Pigeons === -- 

recursive let listenPigeons : Float -> Option Float = lam weight.
  switch fileReadLine fileStdin
  case Some ("log_potential(" ++ beta ++ ")") then
    let beta = string2float beta in
    -- printErrorLn (join ["weight: ", float2string weight, " priorWeight: ", float2string priorWeight, " beta: ", float2string beta]);
    let valid = not (or (eqf weight (negf inf)) (isNaN weight)) in
    let result = if valid then mulf beta weight else log 0. in
    printLn (join ["response(", float2string result, ")"]);
    listenPigeons weight
  case Some ("call_sampler!(" ++ beta ++ ")") then
    printLn "response()"; 
    Some (string2float beta)
  case Some cmd then
    printErrorLn (concat "Unrecognized command, ignoring: " cmd);
    listenPigeons weight
  case None () then
    None ()
  end
end

let contStateInitPigeons : () -> (Int, Float) = lam.
  -- Initialize Pigeons continue state. We assume that Pigeons first issues a `call_sampler!(beta)`
  fileReadLine fileStdin;
  printLn "response()";
  (0, 1.0)

let continuePigeons : all a. all k. Int -> Int -> (Int -> a -> ()) -> (Int, Float) -> SampleInfo -> a -> (k, Bool) -> ((Int, Float), Bool) =
  lam exploreSteps. lam samplingPeriod. lam writer. lam contState. lam sampleInfo. lam sample. lam.
    match contState with (idx, beta) in
    let weight = sampleInfo.weight in
    -- printLn (strJoin " : " ["Pigeons continue", int2string idx, float2string beta, float2string weight, float2string priorWeight]);
    (if and (eqi 0 (modi idx samplingPeriod)) (eqf beta 1.0) then 
      writer idx sample
    else ()); 
    let optBeta = if (eqi 0 (modi idx exploreSteps)) then 
      listenPigeons weight
    else Some beta in
    match optBeta with Some beta then 
        ((addi idx 1, beta), true) 
    else 
        ((addi idx 1, beta), false)

let temperaturePigeons : (Int, Float) -> Float =
  lam contState. contState.1

-- let globalProbPigeons : Bool -> Float -> (Int, Float, Option WriteChannel) -> Float =
--   lam forceGlobal. lam globalProb. lam contState.
--     match contState with (_, beta, _) in
--     if and forceGlobal (eqf beta 0.0)
--     then 1.0 else globalProb