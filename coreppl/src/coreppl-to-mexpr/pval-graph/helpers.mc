include "ext/mat-ext.mc"
include "either.mc"

-- === Misc. seq./iteration === --

let _iterateni = lam bound. lam f.
  recursive let work = lam i. lam acc.
    if lti i bound
    then work (addi i 1) (f i acc)
    else acc
  in work 0

let maybeFoldl : all a. all b. all c. (a -> b -> (a, Bool)) -> a -> [b] -> (a, Bool) =
    lam f. lam init. lam arr. 
    foldl (lam acc. lam a. match acc with (_, false) then acc else f acc.0 a) (init, true) arr

let take : all a. Int -> [a] -> [a] = 
  lam n. lam s.
    (foldl (lam acc. lam s. if leqi acc.0 0 then acc else (subi acc.0 1, snoc acc.1 s)) (n, []) s).1
  
let normalize : [Float] -> [Float] = lam ws.
  let s = foldl addf 0. ws in
  map ((flip divf) s) ws

--- === Printing === --

let roundf = lam f. lam d.
    let p = pow 10. (int2float d) in
    let iPart = int2float (roundfi f) in
    addf iPart (divf (int2float (roundfi (mulf (subf f iPart) p))) p)

let truncf = lam f. lam d. string2float (take d (float2string f))

let float2stringFixed = lam f. lam d. 
    let s1 = float2string f in 
    if gti (length s1) d then take d s1
    else join [s1, make (subi d (length s1)) '0']

-- === Maps === --

let mapInsertOrAdd  =
 lam k. lam v. lam m.  
    match mapLookup k m with Some (a, n) then
      mapInsert k (addi a v, addi n 1) m
    else
      mapInsert k (v, 1) m

let cmpTup : (Int, Int) -> (Int, Int) -> Int = lam kva. lam kvb. 
  let cmp1 = subi kva.0 kvb.0 in
  if eqi cmp1 0 then subi kva.1 kvb.1 else cmp1 

let mapInsertOrMod : all k. all v. (v -> v -> v) -> k -> v -> Map k v -> Map k v = 
  lam f. lam k. lam v. lam m.  
    match mapLookup k m with Some prev then
      mapInsert k (f prev v) m
    else
      mapInsert k v m

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


-- === Matrix stuff === --

let matGetRowAsSeq : all a. Int -> Mat a -> [a] = lam row. lam mtx.
  map (lam i. matGetExn mtx row i) (range 0 mtx.n 1) 

let _matElemMul = lam m1. lam m2.
  match matElemMul m1 m2 with Right m in
  m

let matNormalize = lam mtx.
  let sum = _iterateni (muli mtx.m mtx.n) (lam i. lam acc. addf acc (extArrGetExn mtx.arr i)) 0.0 in
  let mtx = matCopy mtx in
  repeati (lam i. extArrSetExn mtx.arr i (divf (extArrGetExn mtx.arr i) sum)) (muli mtx.m mtx.n);
  mtx

-- === Sampling === --
let _chooseUniform : all a. [a] -> a
  = lam l. get l (uniformDiscreteSample 0 (subi (length l) 1))

let _sampleNonUniform : all a. [Float] -> Int =
  lam ws. categoricalSample (normalize ws)

let _chooseNonUniform : all a. [a] -> [Float] -> a
  = lam l. lam ws.
    let c = _sampleNonUniform ws in
    get l c