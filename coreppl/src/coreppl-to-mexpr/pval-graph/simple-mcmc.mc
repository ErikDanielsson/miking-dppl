include "pval-interface.mc"
include "json.mc"

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

type SampleInfo = {
  weight : Float
}

lang MCMCPVal = PValInterface
  type MCMCConfig st s k contState =
    { getSample : PValInstance Complete st -> s
    , step : PValInstance Partial st -> PValInstance Partial st
    , contStateInit : () -> contState
    , continue : contState -> SampleInfo -> s -> (k, Bool) -> (contState, Bool)
    , temperature : contState -> Float
    }

  type MCMCResult st a =
    { samples : [a]
    , acceptanceRatio : Float
    , finalInstance : PValInstance Complete st
    }

  sem mcmc : all st. all a. all k. all c. MCMCConfig st a () c-> PValInstance Complete st -> MCMCResult st a
  sem mcmc config = | instance ->
    let acceptPred = lam prob. bernoulliSample (exp prob) in
    recursive let work = lam acc.
      match acc.contState with (contState, contSample) in
      if contSample then
        let beta = config.temperature contState in
        let modWeight = if eqf beta 0.0
          then (lam w. if (or (eqf w (negf inf)) (isNaN w))
            then log 0.
            else 0.0
          )
          else lam w. mulf beta w
        in
        match (config.step (startStep acc.instance)) with instance in
        match finalizeStep modWeight acceptPred instance with (accepted, instance) in
        let sample = config.getSample instance in
        let sinfo = { weight = getWeight instance } in
        let contState = config.continue contState sinfo sample ((), accepted) in
        let acc =
          { contState = contState
          , accepted = addi acc.accepted (if accepted then 1 else 0)
          , samples = snoc acc.samples sample
          , instance = instance
          } in
        work acc
      else acc
    in
    let res = work {contState = (config.contStateInit (), true), accepted = 0, samples = [], instance = instance} in
    { samples = res.samples
    , acceptanceRatio = int2float res.accepted
    , finalInstance = res.instance
    }
end


-- === A simple store of assumes, generic enough to work for any model ===

let _chooseUniform : all a. [a] -> a
  = lam l. get l (uniformDiscreteSample 0 (subi (length l) 1))

lang SimpleState = PValInterface
  syn SimpleState x =
  | SimpleState {here : [PSomeAssumeRef], below : [PSubmodelRef (SimpleState ())], export : x}

  sem simpleInit : all x. x -> SimpleState x
  sem simpleInit = | export ->
    SimpleState {here = [], below = [], export = export}

  sem simpleStoreAssume : all a. all x. SimpleState x -> PAssumeRef Float -> SimpleState x
  sem simpleStoreAssume st = | ref ->
    match st with SimpleState st in
    SimpleState {st with here = snoc st.here (asSomeAssume (Some (lam x. mkGaussian x 1.)) ref)}


  sem simpleStoreExport : all x1. all x2. SimpleState x1 -> PExportRef x2 -> SimpleState (PExportRef x2)
  sem simpleStoreExport st = | ref ->
    match st with SimpleState st in
    SimpleState {here = st.here, below = st.below, export = ref}

  sem simpleStoreWeight : all x. SimpleState x -> PWeightRef -> SimpleState x
  sem simpleStoreWeight st = | ref -> st

  sem simpleStoreSubmodel : all x. SimpleState x -> PSubmodelRef (SimpleState ()) -> SimpleState x
  sem simpleStoreSubmodel st = | ref ->
    match st with SimpleState st in
    SimpleState {st with below = snoc st.below ref}

  sem simpleReadExport : all x. all complete. PValInstance complete (SimpleState (PExportRef x)) -> x
  sem simpleReadExport = | instance ->
    match getSt instance with SimpleState st in
    readPreviousExport st.export instance

  sem simpleResampleAligned : all x. Float -> PValInstance Partial (SimpleState x) -> PValInstance Partial (SimpleState x)
  sem simpleResampleAligned globalProb = | instance ->
    match getSt instance with SimpleState st in
    if bernoulliSample globalProb then
      -- NOTE(vipa, 2025-12-09): We assume that all submodels depend
      -- on at least one aligned assume, so that if the aligned assume
      -- is resampled then the submodel will be replaced. I believe
      -- the only cases where this does not hold are 1) we have a
      -- `pure` value fed into a `bind` or 2) there's a `cache` before
      -- feeding into `bind`. Neither should happen with the automatic
      -- generation.
      foldr resampleSomeAssume instance st.here
    else
      resampleSomeAssume (_chooseUniform st.here) instance

  sem simpleStateToDebugJson : all partial. all x. all y. PValInstance partial (SimpleState x) -> SimpleState y -> JsonValue
  sem simpleStateToDebugJson instance = | SimpleState x ->
    JsonObject (mapFromSeq cmpString
      [ ("assumes", JsonInt (length x.here))
      , ("sub-models", JsonArray (map (lam ref. simpleStateToDebugJson instance (readPreviousSubmodel ref instance)) x.below))
      ])
end

lang SimpleMCMCPVal = SimpleState + MCMCPVal
  sem mkMCMCConfig : all x. all contState. 
    (() -> contState) ->
    (contState -> SampleInfo -> Float -> ((), Bool) -> (contState, Bool)) ->
    (contState -> Float) -> 
    Float -> 
    MCMCConfig (SimpleState (PExportRef Float)) Float () contState

  sem mkMCMCConfig contStateInit continue  temperature = | globalProb ->
    { getSample = simpleReadExport
    , step = simpleResampleAligned globalProb
    , contStateInit = contStateInit
    , continue = continue
    , temperature = temperature
    }
end
