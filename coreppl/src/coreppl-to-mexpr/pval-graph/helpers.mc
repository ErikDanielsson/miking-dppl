let maybeFoldl : all a. all b. all c. (a -> b -> (a, Bool)) -> a -> [b] -> (a, Bool) =
    lam f. lam init. lam arr. 
    foldl (lam acc. lam a. match acc with (_, false) then acc else f acc.0 a) (init, true) arr

let take : all a. Int -> [a] -> [a] = 
  lam n. lam s.
    (foldl (lam acc. lam s. if leqi acc.0 0 then acc else (subi acc.0 1, snoc acc.1 s)) (n, []) s).1

let roundf = lam f. lam d.
    let p = pow 10. (int2float d) in
    let iPart = int2float (roundfi f) in
    addf iPart (divf (int2float (roundfi (mulf (subf f iPart) p))) p)

let truncf = lam f. lam d. string2float (take d (float2string f))
