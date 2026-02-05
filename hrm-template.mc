include "coreppl::coreppl-to-mexpr/pval-graph/host-rep-mcmc.mc"
include "coreppl::coreppl-to-mexpr/pval-graph/pval-mut.mc"
include "coreppl::coreppl-to-mexpr/pval-graph/pval-debug.mc"
include "ext/mat-ext.mc"
include "common.mc"
include "json.mc"

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

mexpr

let showHistogram : Bool = true in

let globalProb = 0.0 in
let iterations = 4000 in
-- let toString = lam. "()" in
let mkHisto2 = histogram (lam. lam. 0) in
let toString2 = int2string in
let toString = interval2string in
let mkHisto = bucket 10 0.0 1. in
let summarizePVal = lam label. lam pair.
  match pair with (time, res) in
  printLn (join [float2string time, "ms (", label, ")"]);
  printLn (join ["Acceptance ratio: ", float2string res.acceptanceRatio]);
  -- printLn (join (map (lam x. join [float2string x, "\t"]) res.samples));
  if showHistogram then
    -- (map (lam s. printLn (join
    --   [ "mu:", float2string s.mu
    --   , ", beta: ", float2string s.beta
    --   , ", lambda:[", (strJoin "," (map float2string s.lambda)), "]"
    --   ]))
    -- res.samples);
    let muSamples = map (lam s. s.mu) res.samples in
    printLn "------ Mu ------";
    printLn (hist2string toString (mkHisto muSamples));
    let betaSamples = map (lam s. s.beta) res.samples in
    printLn "------ Beta ------";
    printLn (hist2string toString (mkHisto betaSamples));
    let lambdaSamples = map (lam s. s.lambda) res.samples in
    map (lam i. 
      let lamiSamples = map (lam s. get s i) lambdaSamples in
      printLn (join ["------ Lambda ", int2string i, " ------"]);
      printLn (hist2string toString (mkHisto lamiSamples))
    ) [0, 1, 2, 3];
    let rootRepSamples = map (lam s. s.rootRep) res.samples in
    map (lam i. 
      let rriSamples = map (lam s. get s i) rootRepSamples in
      printLn (join ["------ Rootrep ", int2string i, " ------"]);
      printLn (hist2string toString2 (mkHisto2 rriSamples))
    ) [0, 1];
    ()
  else () in
let run =
  setSeed 1234;
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
  -- printLn (join ["Took ", float2string time, "ms to find good instance."]);
  lam.
    let r = mcmc (lam x. if eqi (modi x 100) 0 then hrmPrintState else (lam. lam. ())) (mkMCMCConfig iterations globalProb) instance in
    printLn "---- Finalize step JSON ----";
    hrmPrintState true instance; 
    printLn "----------------------------";
    let w = getWeight instance in
    println (join ["Final model weight: ", float2string w]);
    r in
summarizePVal "mut" (timeF run);

()
