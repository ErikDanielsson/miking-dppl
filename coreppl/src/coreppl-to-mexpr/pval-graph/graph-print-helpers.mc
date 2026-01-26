include "json.mc"
include "map.mc"
include "option.mc"

let showFloat : Float -> JsonValue = lam v. JsonFloat v
let showInt : Int -> JsonValue = lam v. JsonInt v
let showBool : Bool -> JsonValue = lam v. JsonBool v

let showOpt = lam show. lam opt. match opt with Some v then show v else JsonNull ()

let showSeq : all a. (a -> JsonValue) -> [a] -> JsonValue =
  lam show. lam seq.
    JsonArray (map show seq)

let showMap : all k. all v.
  (k -> String) -> (v -> JsonValue) -> Map k v -> JsonValue =
  lam convKey. lam showVal. lam m. 
    let show = (lam kv. (convKey kv.0, showVal kv.1)) in
    JsonObject (mapFromSeq cmpString (map show (mapToSeq m)))


let showEither : all a. all b. (a -> JsonValue) -> (b -> JsonValue) -> Either a b -> JsonValue =
  lam showLeft. lam showRight. lam val.
  match val with Left a then showLeft a else 
  match val with Right b in showRight b


let maybeShowVal : all a. (a -> Bool) -> (a -> JsonValue) -> String -> a -> [(String, JsonValue)] =
  lam pred. lam show. lam name. lam val.
  if pred val then [(name, show val)] else []

let maybeShowOpt : all a. (a -> JsonValue) -> String -> Option a -> [(String, JsonValue)] = lam show. lam name. lam val.
  let pred = lam v. match v with Some _ then true else false in
  let unpackShow = lam v. match v with Some p then show p else JsonArray [] in
  maybeShowVal pred unpackShow name val

let maybeShowSeq : all a. (a -> JsonValue) -> String -> [a] -> [(String, JsonValue)] = lam show. lam name. lam val.
  let pred = lam s. neqi 0 (length s) in
  maybeShowVal pred (showSeq show) name val

let maybeShowMap : all k. all v. (k -> String) -> (v -> JsonValue) -> String -> Map k v -> [(String, JsonValue)] =
  lam convKey. lam convVal. lam name. lam val.
    let pred = lam s. neqi 0 (mapLength s) in
    maybeShowVal pred (showMap convKey convVal) name val

let pruneSubmodels = lam submodels. 
  let nonemptyModels = foldr (
    lam v. lam acc.
      match v with Some a then cons a acc else acc
  ) [] submodels in
  if eqi (length nonemptyModels) 0 then [] else [("submodels", JsonArray nonemptyModels)]
