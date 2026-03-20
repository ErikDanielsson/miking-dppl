mexpr
let x = assume (Gaussian 0.0 10.) in
-- let bimodal = lam x.
--     let sq = lam x. mulf x x in
--     let g = lam x. lam y. exp (divf (sq (subf x y)) -0.1) in
--     addf (g 3. x) (g -3. x)
-- in
-- weight (log (bimodal x));
(observe 1.0 (Gaussian x 0.1));
x
