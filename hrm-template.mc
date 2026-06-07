include "coreppl::coreppl-to-mexpr/pval-graph/host-rep-mcmc.mc"
include "coreppl::coreppl-to-mexpr/pval-graph/pval-mut.mc"
include "coreppl::coreppl-to-mexpr/pval-graph/pval-debug.mc"
include "coreppl::coreppl-to-mexpr/pval-graph/continues.mc"
include "ext/mat-ext.mc"
include "ext/file-ext.mc"
include "common.mc"
include "json.mc"
include "sys.mc"

-- NOTE(vipa, 2025-12-09): In lieu of proper distribution translations
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

lang Model = HRMMCMCPVal
  sem model = | st ->
    (
{{HERE}}
    ) st
end

lang ComposedMut = Model + MutPVal + RuntimeDistElementary
end

lang ComposedVisi = Model + PValVisiGraph + RuntimeDistElementary
end

let timeF : all a. (() -> a) -> (Float, a)
  = lam f.
    let before = wallTimeMs () in
    let res = f () in
    let after = wallTimeMs () in
    (subf after before, res)

let interval2string : (Float, Float) -> String
  = lam pair.
    join [float2string pair.0, "-", float2string pair.1]

let histogram : all a. (a -> a -> Int) -> [a] -> [(a, Float)]
  = lam cmp. lam l.
    let hist = foldl (lam acc. lam a. mapInsertWith addi a 1 acc) (mapEmpty cmp) l in
    let count = int2float (mapFoldWithKey (lam total. lam. lam count. addi total count) 0 hist) in
    let hist = mapMap (lam v. divf (int2float v) count) hist in
    mapBindings hist

let bucket : all a. Int -> Float -> Float -> [Float] -> [((Float, Float), Float)]
  = lam numBuckets. lam min. lam max. lam l.
    let bucketSize = divf (subf max min) (int2float numBuckets) in
    let hist = mapFromSeq subi (create numBuckets (lam i. (i, 0))) in
    let f = lam acc. lam x. mapInsertWith addi (floorfi (divf (subf x min) bucketSize)) 1 acc in
    let hist = foldl f hist l in
    let count = int2float (mapFoldWithKey (lam total. lam. lam count. addi total count) 0 hist) in
    let convPair = lam pair.
      let base = addf min (mulf bucketSize (int2float pair.0)) in
      ( (base, addf bucketSize base)
      , divf (int2float pair.1) count
      ) in
    map convPair (mapBindings hist)

let progressBarNoPad : Int -> Float -> String
  = lam width. lam fraction.
    let filled = roundfi (mulf (int2float width) fraction) in
    make filled '=' -- (make (subi width filled) ' ')

let hist2string : all a. (a -> String) -> [(a, Float)] -> String
  = lam toStr. lam l.
    strJoin "\n" (map (lam pair. join [toStr pair.0, "\t", float2string pair.1, "\t", progressBarNoPad 100 pair.1]) l)

let sampleToJson = lam sample.
  JsonObject (mapFromSeq cmpString
    (concat
    [ ("mu", JsonFloat sample.mu)
    , ("beta", JsonFloat sample.beta)
    , ("lambda", JsonArray (map (lam f. JsonFloat f) sample.lambda))
    ] (map
      (lam kv.
        match kv with (k, rep) in
        (int2string k, JsonArray (map (lam h. JsonInt h) rep))
      )
      (mapToSeq sample.reps)
    )
    )
  )
let samplesToJson = lam samples.
  JsonArray (map sampleToJson samples)

let getSampleFn : () -> String = lam.
  match sysGetEnv "PPL_OUTPUT" with Some fn
    then fn
    else error "No sample filename provided via PPL_OUTPUT!"

let tryOpenSampleFile : String -> WriteChannel = lam fn.
    match fileWriteOpen fn with Some wc then wc
    else error (join ["Failed to open sample file ", fn])

let sampleWriter = lam wc. lam i. lam s.
  let jStr = join [int2string i, "\t", json2string (sampleToJson s), "\n"] in
  fileWriteString wc jStr;
  fileWriteFlush wc

let usePigeons = lam exploreSteps. lam samplingPeriod.
  let fn = getSampleFn () in
  let wc = tryOpenSampleFile fn in
  let writer = sampleWriter wc in
  let continue = (lam c. lam sinfo. lam s.
    continuePigeons exploreSteps samplingPeriod writer c sinfo s
  ) in
  { init = contStateInitPigeons
  , continue = continue
  , temp = temperaturePigeons
  , wc = wc
  }

let useSingleChain = lam iterations. lam samplingPeriod.
  let fn = getSampleFn () in
  let wc = tryOpenSampleFile fn in
  let writer = sampleWriter wc in
  let continue = (lam c. lam sinfo. lam s.
    continueBase iterations samplingPeriod writer c sinfo s
  ) in
  { init = (lam. contStateInitBase ())
  , continue = continue
  , temp = (lam c. temperatureBase c)
  , wc = wc
  }

let getSeed : () -> Int = lam.
  match sysGetEnv "PPL_SEED" with Some seedStr
    then string2int seedStr
    else error "No seed provided via PPL_SEED!"

  

mexpr




let showHistogram : Bool = true in

let globalProb = 0.0 in
let iterations = 400000 in
let samplingPeriod = 100 in
-- let toString = lam. "()" in
let mkHisto2 = histogram (seqCmp subi) in
let toString2 = lam s. join ["[", strJoin ", " (map int2string s), "]"] in
let toString = interval2string in
let mkHisto = bucket 10 0.0 1. in
let summarizePVal = lam label. lam pair.
  match pair with (time, res) in
  printLn (join [float2string time, "ms (", label, ")"]);
  -- printLn (join ["Acceptance ratio: ", res.acceptanceRatio]);
  -- printLn (join (map (lam x. join [float2string x, "\t"]) res.samples));
  ()
  -- let showAccept = lam acceptM. 
  --   let ratio = lam a. lam n. divf (int2float a) (int2float n) in
  --   strJoin "\n"
  --     (map (lam t. match t with (m, (a, n)) in join [m, ": ", float2stringFixed (ratio a n) 10, " : ", int2string a, "/", int2string n])
  --     (mapToSeq acceptM))
  -- in
  -- printLn "Acceptance ratios";
  -- printLn (showAccept res.acceptanceRatio);
  -- if showHistogram then
  --   -- (map (lam s. printLn (join
  --   --   [ "mu:", float2string s.mu
  --   --   , ", beta: ", float2string s.beta
  --   --   , ", lambda:[", (strJoin "," (map float2string s.lambda)), "]"
  --   --   ]))
  --   -- res.samples);
  --   let muSamples = map (lam s. s.mu) res.samples in
  --   printLn "------ Mu ------";
  --   printLn (hist2string toString (mkHisto muSamples));
  --   let betaSamples = map (lam s. s.beta) res.samples in
  --   printLn "------ Beta ------";
  --   printLn (hist2string toString (mkHisto betaSamples));
  --   let lambdaSamples = map (lam s. s.lambda) res.samples in
  --   map (lam i. 
  --     let lamiSamples = map (lam s. get s i) lambdaSamples in
  --     printLn (join ["------ Lambda ", int2string i, " ------"]);
  --     printLn (hist2string toString (mkHisto lamiSamples))
  --   ) [0, 1, 2, 3];
  --   -- let rootRepSamples = map (lam s. s.rootRep) res.samples in
  --   let reps = mapEmpty subi in
  --   let reps = foldl (lam m. lam inner. foldl (lam im. lam kv. match kv with (k, v) in mapInsertOrAppend k v im) m (mapToSeq inner.reps)) reps res.samples in
  --   mapMapWithKey (lam k. lam v.
  --     printLn (join ["------ Node repertoire ", int2string k, " ----------"]);
  --     printLn (hist2string toString2 (mkHisto2 v))
  --   ) reps;
  --   ()
  -- else ()

 in




let run =
  setSeed (getSeed ());
  -- setSeed 1234;
  use ComposedVisi in
  -- printJsonLn (graphToJson (instantiate model (hrmInit ())));
  -- exit 0;
  use ComposedMut in
  let initialize = lam. instantiate model (hrmInit ()) in
  match initialize () with instance in
  match timeF (lam. hrmFindPointInSupport instance) with (time, instance) in
  printLn (join ["Took ", float2string time, "ms to find point in the support"]);
  printLn (join ["Starting weight: ", float2string (getWeight instance)]);
  -- printJsonLn (hrmStateToDebugJson instance (getSt instance));
  -- match getSt instance with HRMState st in
  -- printLn (join [int2string (length st.here), ", ", int2string (length st.below)]);
  let printer = hrmPrintState
    -- lam x.
    -- -- lam. lam. ()
    -- if eqi (modi x 10) 0 then
    --   printLn (join ["Iteration", int2string x]); hrmPrintState
    -- else
    --   lam. lam. ()
  in
  -- printLn (join ["Took ", float2string time, "ms to find good instance."]);
  lam.
    -- let conts = usePigeons samplingPeriod samplingPeriod in
    let conts = useSingleChain iterations samplingPeriod in
    let config = mkMCMCConfig conts.init conts.continue conts.temp in
    let r = mcmc printer config instance in
    fileWriteClose conts.wc;
    printLn "---- Finalize step JSON ----";
    hrmPrintState true instance; 
    printLn "----------------------------";
    let w = getWeight instance in
    println (join ["Final model weight: ", float2string w]);
    r
  in
summarizePVal "mut" (timeF run);

()
