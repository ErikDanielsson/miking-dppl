include "stdlib::ext/mat-ext.mc"
mexpr
-- assume (Gaussian 0.0 1.0)

-- let x = 0.0 in
-- assume (Gaussian x 1.0)

-- let x = assume (Gaussian 0.0 1.0) in
-- assume (Gaussian x 1.0)

-- addf (assume (Gaussian 0.0 1.0)) (assume (Gaussian 1.0 1.0))

-- addf (addf (assume (Gaussian 0.0 1.0)) (assume (Gaussian 1.0 1.0))) 2.0

-- let f = lam a. addf a 1.0 in
-- f 1.0

-- let f = lam a. addf a 1.0 in
-- addf (f 1.0) (f (assume (Gaussian 0.0 1.0)))

-- let f = lam a. assume (Gaussian a 1.0) in
-- let g = lam a. f a in
-- addf (g 1.0) (g (assume (Gaussian 0.0 1.0)))

-- recursive let sum : Float -> Float = lam x. sum (assume (Gaussian x 1.0)) in
-- sum 1.0

-- recursive
--   let odd : Float -> Bool = lam x. even (assume (Gaussian x 1.0))
--   let even = lam x. odd x
-- in even 1.0

-- [1.0, 2.0]

-- [1.0, assume (Gaussian 0.0 1.0)]

-- if true then 1 else 2

-- if true then assume (Gaussian 0.0 1.0) else 42.0

-- match (assume (Gaussian 0.0 1.0), 2.0) with (a, b) in addf a b

-- if assume (Bernoulli 0.5) then false else true

-- if assume (Bernoulli 0.5) then assume (Bernoulli 0.9) else false

-- if true then (1, 2.0) else (2, assume (Gaussian 0.0 1.0))

-- if assume (Bernoulli 0.5) then [1.0, 2.0] else [assume (Gaussian 0.0 1.0)]

-- if true then [1., 2.] else [assume (Gaussian 0.0 1.0)]

-- type Either a b in
-- con Left : all a. all b. a -> Either a b in
-- con Right : all a. all b. b -> Either a b in
-- if true then Left 1 else Right 2.0

-- type Either a b in
-- con Left : all a. all b. a -> Either a b in
-- con Right : all a. all b. b -> Either a b in
-- if true then Left 1.0 else let x = assume (Gaussian 1.0 0.0) in Left x

-- type Either a b in
-- con Left : all a. all b. a -> Either a b in
-- con Right : all a. all b. b -> Either a b in
-- if true then Left 1.0 else if assume (Bernoulli 0.5) then Left 2.0 else Left 3.0

-- type Either a b in
-- con Left : all a. all b. a -> Either a b in
-- con Right : all a. all b. b -> Either a b in
-- if true then
--   let x = assume (Gaussian 1.0 0.0) in
--   Left x
-- else
--   if assume (Bernoulli 0.5) then Left 2.0 else Left 3.0

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- Node {x = 1.0, left = Leaf {x = 2.0}, right = Leaf {x = 3.0}}

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- let x = assume (Gaussian 0.0 1.0) in
-- Node {x = 1.0, left = Leaf {x = x}, right = Leaf {x = 3.0}}

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- let x = assume (Gaussian 0.0 1.0) in
-- let l = if assume (Bernoulli 0.5) then Leaf {x = x} else Leaf {x = 2.0} in
-- Node {x = 1.0, left = l, right = Leaf {x = 3.0}}

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- let merge = lam l. lam r.
--   let x = assume (Gaussian 0.0 1.0) in
--   Node {x = x, left = l, right = r} in
-- merge (merge (Leaf {x = 1.0}) (Leaf {x = 2.0})) (Leaf {x = 3.0})

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- if assume (Bernoulli 0.5)
-- then let x = assume (Gaussian 0.0 1.0) in Node {x = x, left = Leaf {x = 1.0}, right = Leaf {x = 2.0}}
-- else Leaf {x = 1.0}

-- This is manually written to use shallow patterns
-- type List a in
-- con Nil : all a. () -> List a in
-- con Cons : all a. (a, List a) -> List a in
-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- recursive let cluster = lam trees.
--   match trees with Cons tmp in
--   match tmp with (tree, rest) in
--   match rest with Cons tmp then
--     match tmp with (r, trees) in
--     let newX = assume (Gaussian 0.0 1.0) in
--     cluster (Cons (Node {x = newX, left = tree, right = r}, trees))
--   else tree in
-- cluster (Cons (Leaf {x = 0.0}, Cons (Leaf {x = 1.0}, Cons (Leaf {x = 2.0}, Nil ()))));

---- TODO ----
-- * Figure out why the manual shallow example drops a let binding (probably something about a specialization request being removed when it's passed in one instance)
-- * Ensure `lowerAll` preserves enough types.
-- * Ensure we handle polymorphic constants properly:
--   * See if there's wrappedness that can't be swallowed by polymorphism
--   * Find all occurrences of each type variable in the inputs, `lub` them
--   * Reconstruct arguments _and return_ with new versions of type variables
--   * If unswallowed wrappedness, `ensureWrapped` on all arguments and return, `pure` on const, `apply` arguments
--   * Otherwise normal app

-- -- This is written with nested patterns
-- type List a in
-- con Nil : all a. () -> List a in
-- con Cons : all a. (a, List a) -> List a in
-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- recursive let cluster = lam trees.
--   match trees with Cons (tree, Nil ()) then tree else
--   match trees with Cons (l, Cons (r, trees)) in
--   let newX = assume (Gaussian 0.0 1.0) in
--   cluster (Cons (Node {x = newX, left = l, right = r}, trees)) in
-- cluster (Cons (Leaf {x = 0.0}, Cons (Leaf {x = 1.0}, Cons (Leaf {x = 2.0}, Nil ()))));
-- ()

-- type Tree in
-- con Leaf : {x : Float} -> Tree in
-- con Node : {x : Float, left : Tree, right : Tree} -> Tree in
-- recursive let cluster = lam trees.
--   match trees with [tree] then tree else
--   match trees with [l, r] ++ trees in
--   let newX = assume (Gaussian 0.0 1.0) in
--   cluster (cons (Node {x = newX, left = l, right = r}) trees) in
-- cluster [Leaf {x = 0.0}, Leaf {x = 1.0}, Leaf {x = 2.0}]

type STree in
-- Each leaf is at time 0.0 and contains a state
con SLeaf : Int -> STree in
-- Each node contains its time 
con SNode : {left : STree, right : STree, t: Float} -> STree in

type MsgTree in
con MsgLeaf : Mat Float -> MsgTree in
con MsgNode :
  { left : MsgTree
  , leftKernel: Mat Float -- The Markov kernel describing the transition probility from this node to the left node
  , right : MsgTree
  , rightKernel: Mat Float -- The Markov kernel describing the transition probility from this node to the right node
  , t: Float
  , msg: Mat Float
  } -> MsgTree in

let stree = SNode {
  left = SNode {
    left = SLeaf 1,
    right = SLeaf 2,
    t = 0.3
  },
  right = SNode {
    left = SLeaf 2,
    right = SLeaf 2,
    t = 0.5
  },
  t = 1.
} in
-- let stree = SNode {
--   left = SLeaf 1,
--   right = SLeaf 2,
--   t = 1.
-- }

let sKronecker = lam n. lam i. map (lam j. if eqi i j then 1. else 0.) (range 0 n 1) in

let kroneckers : [Int] -> Int -> Mat Float = lam is. lam ncols.
  let nrows = length is in
  let flatMap = lam f. compose (foldl concat []) (map f) in
  let sKroneckers = flatMap (sKronecker ncols) is in
  let mat = matFromArrExn nrows ncols (extArrOfSeq extArrKindFloat64 sKroneckers) in
  -- printMat mat;
  mat in

let transKernels : Mat Float -> Float -> (Mat Float, Mat Float) = lam q. lam t.
  let forward = matExpExn (matScale t q) in
  let backward = matTranspose forward in
  (forward, backward) in

let mvMsg : Mat Float -> Mat Float -> Mat Float = lam k. lam m.
  matMulExn m k in

let matRowSums : Mat Float -> [Float] = lam mat.
  map (
    lam i. foldl (lam acc. lam j. addf acc (matGetExn mat i j)) 0. (range 0 mat.m 1)
  ) (range 0 mat.m 1)  in

-- These should really be replaced by BLAS operations -- is there an interface in OCaml?
let matNormalizeRows : Mat Float -> (Mat Float, Float) = lam mat.
  let sums = matRowSums mat in
  let mat = matCopy mat in
  iteri (lam i. lam s. repeati (lam j. matSetExn mat i j (divf (matGetExn mat i j) (get sums j))) mat.m) sums;
  let logLik = foldl (lam acc. lam s. addf acc (log s)) 0.0 sums in
  (mat, logLik) in

let seqNest : all a. [a] -> Int -> Int -> [[a]] = lam l. lam r. lam c.
  let row = lam i.
    let rs = muli i c in
    let re = addi rs c in
    subsequence l rs c in
  map row (range 0 r 1) in

let matToSeqs : Mat Float -> [[Float]] = lam mat.
  let seq = extArrToSeq mat.arr in
  seqNest seq mat.m mat.n in

let combineMsgs : Mat Float -> Mat Float -> (Mat Float, Float) = lam l. lam r.
  let unnormalized = matElemMulExn l r in
  matNormalizeRows unnormalized in

-- Compute the postorder messages 
recursive let makeMsgs : STree -> Mat Float -> (Mat Float, Float, Float, MsgTree) = 
  lam tree. lam q.
    switch tree 
      case SLeaf l then
        let lDist = kroneckers [l] 3 in
        -- printLn "MakeMsgs";
        -- printMat lDist; 
        (lDist, 0.0, 0.0, MsgLeaf lDist)
      case SNode n then
        -- Left subtree: compute state and push through backwards kernel
        match makeMsgs n.left q with (lDist, lT, logLikL, left) in
        let ldt = subf n.t lT in
        match transKernels q ldt with (lforward, lbackward) in
        let lMsg = mvMsg lbackward lDist in
        -- Right subtree: compute state and push through backwards kernel
        match makeMsgs n.right q with (rDist, rT, logLikR, right) in
        let rdt = subf n.t lT in
        match transKernels q rdt with (rforward, rbackward) in
        let rMsg = mvMsg rbackward rDist in
        match combineMsgs lMsg rMsg with (msg, localLogLik) in 
        -- Accumulate the log likelihood from the left and right trees, and the one from normalizing message.
        -- printLn (join ["Local log likelihood: ", float2string localLogLik]);
        let accLogLik = addf localLogLik (addf logLikL logLikR) in
        ( msg
        , n.t
        , accLogLik
        , MsgNode
          { left = left
          , leftKernel = lforward
          , right = right
          , rightKernel = rforward
          , t = n.t
          , msg = msg
          }
        ) 
    end
  in
-- Set up the model parameters
let params = assume (Dirichlet [1., 1., 1., 1.]) in
let l01 = get params 0 in
let l10 = get params 1 in
let l12 = get params 2 in
let l21 = get params 3 in
let rates = [l01, addf l10 l12, l21] in
let embeddedMC = [
  [0., 1., 0.], 
  [divf l10 (get rates 1), 0., divf l21 (get rates 1)], 
  [0., 1., 0.] 
] in
let q = matFromArrExn 3 3 (extArrOfSeq extArrKindFloat64 [
  negf l01, l01                , 0.       , 
  l10     , negf (addf l10 l12), l12      , 
  0.      , l21                , negf l21
]) in

-- Simulate the nodes using the messages and the branches in between them
let branch : Int -> Float -> Int = lam a. lam t.
  recursive let recur = lam a. lam t.
    if geqf t 0. then 
      let b = assume (Categorical (get embeddedMC a)) in
      let t0 = assume (Exponential (get rates a)) in
      let t = subf t t0 in
      recur b t
    else a in
  let t0 = assume (Exponential (get rates a)) in
  let t = subf t t0 in
  recur a t in

-- A branch with fixed endpoint
let clamped_branch : Float -> Int -> Int -> () = lam t. lam a. lam b. 
  let e = branch a t in
  weight (if eqi e b then 0. else log 0.) in

-- Simulate from the root and check if we sampled the tip states correctly
recursive let walk : MsgTree -> Float -> Mat Float -> [Int] -> () = lam tree. lam t. lam msg. lam as.
  switch tree 
    case MsgLeaf l then 
      let ls = map (lam p. assume (Categorical p)) (matToSeqs l) in
      -- Simulate what happens on the branch
      zipWith (clamped_branch t) as ls;
      ()
    case MsgNode n then
      -- Combine the current message at this node with the message coming from 
      -- the parent node
      -- printLn (join ["Node ", int2string n.msg.n, ",", int2string n.msg.m, " Incoming", int2string msg.n, ",", int2string msg.m]);
      match combineMsgs n.msg msg with (msg, _) in
      let ns = map (lam p. assume (Categorical p)) (matToSeqs msg) in
      -- Simulate what happens on the branch
      (zipWith (clamped_branch t) as ns);
      -- Simulate the left subtree
      let leftMsg = matMulExn (kroneckers ns 3) n.leftKernel in
      -- printLn "LeftMsg";
      walk n.left n.t leftMsg ns; 
      -- Simulate the right subtree
      let rightMsg = matMulExn (kroneckers ns 3) n.rightKernel in
      -- printLn "rightmsg";
      walk n.right n.t rightMsg ns 
  end
in
-- Compute the postorder messages
match makeMsgs stree q with (rootMsg, rootT, accLogLik, msgTree) in

(switch msgTree 
  case MsgLeaf _ then () -- Trivial case nothing to do
  case MsgNode n then
    -- Weight the program according to the BP likelihood
    let rootSum = foldl addf 0. (matRowSums rootMsg) in
    let rootLogLik = subf (log rootSum) (log (int2float (muli rootMsg.m rootMsg.n))) in
    let totalLogLik = addf rootLogLik accLogLik in
    weight totalLogLik;

    -- Sample the root and prepare the message
    let rootState = map (lam p. assume (Categorical p)) (matToSeqs rootMsg) in
    let rootMsg = kroneckers rootState 3 in
    -- Walk the left tree
    let leftMsg = matMulExn rootMsg n.leftKernel in
    walk n.left n.t leftMsg rootState; 
    -- Walk the right tree
    let rightMsg = matMulExn rootMsg n.rightKernel in
    walk n.right n.t rightMsg rootState
end);


()