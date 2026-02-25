let input =
  { symbiontTree = Node
    { age = 1.0
    , label = 3
    , left = Leaf
        { label = 1
        , age = 0.0
        }
    , right = Leaf
        { label = 2
        , age = 0.0
        }
    }
  , interactions = [[2, 1], [1, 2]]
  , hostDistances = [[0., 1.], [1., 0.]]
  , dMean = 1.
  } in
let tmp = anonPLACEHOLDER input {} in
dprint tmp
