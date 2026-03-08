let input = { symbiontTree = Node
    { age = 6.839526974
    , label = 9
    , left = Leaf
      { label = 1
      , age = 0.0
      }
    , right = Node
      { label = 8
      , age = 4.842443202
      , left = Leaf
        { label = 2
        , age = 0.0
        }
      , right = Node
        { label = 7
        , age = 3.501720109
        , left = Leaf
          { label = 3
          , age = 0.0
          }
        , right = Node
          { label = 6
          , age = 3.127609164
          , left = Leaf
            { label = 4
            , age = 0.0
            }
          , right = Leaf
            { label = 5
            , age = 0.0
            }
          }
        }
      }
    }
  , interactions =
      [ [0, 0, 2, 0, 2]
      , [0, 0, 2, 0, 1]
      , [0, 0, 2, 0, 1]
      , [0, 0, 2, 0, 2]
      , [0, 0, 2, 0, 1]
      ]
  , hostDistances =
      [ [0., 1., 2., 2., 1.]
      , [1., 0., 1., 1., 1.]
      , [2., 2., 0., 1., 1.]
      , [2., 2., 1., 0., 1.]
      , [1., 1., 1., 1., 0.]
      ]
  } in
let tmp = anonPLACEHOLDER input {} in
dprint tmp
