let input = { symbiontTree = Node
      { age = 5.0
      , label = 33
      , left = Node
        { age = 4.0
        , label = 34
        , left = Node
          { age = 3.0
          , label = 35
          , left = Node
            { age = 2.0
            , label = 36
            , left = Node
              { age = 0.0
              , label = 37
              , left = Leaf
                { label = 1
                , age = 0.0
                }
              , right = Leaf
                { label = 2
                , age = 0.0
                }
              }
            , right = Node
              { age = 0.0
              , label = 38
              , left = Leaf
                { label = 3
                , age = 0.0
                }
              , right = Leaf
                { label = 4
                , age = 0.0
                }
              }
            }
          , right = Node
            { age = 2.0
            , label = 39
            , left = Node
              { age = 0.0
              , label = 40
              , left = Leaf
                { label = 5
                , age = 0.0
                }
              , right = Leaf
                { label = 6
                , age = 0.0
                }
              }
            , right = Node
              { age = 0.0
              , label = 41
              , left = Leaf
                { label = 7
                , age = 0.0
                }
              , right = Leaf
                { label = 8
                , age = 0.0
                }
              }
            }
          }
        , right = Node
          { age = 3.0
          , label = 42
          , left = Node
            { age = 2.0
            , label = 43
            , left = Node
              { age = 0.0
              , label = 44
              , left = Leaf
                { label = 9
                , age = 0.0
                }
              , right = Leaf
                { label = 10
                , age = 0.0
                }
              }
            , right = Node
              { age = 0.0
              , label = 45
              , left = Leaf
                { label = 11
                , age = 0.0
                }
              , right = Leaf
                { label = 12
                , age = 0.0
                }
              }
            }
          , right = Node
            { age = 2.0
            , label = 46
            , left = Node
              { age = 0.0
              , label = 47
              , left = Leaf
                { label = 13
                , age = 0.0
                }
              , right = Leaf
                { label = 14
                , age = 0.0
                }
              }
            , right = Node
              { age = 0.0
              , label = 48
              , left = Leaf
                { label = 15
                , age = 0.0
                }
              , right = Leaf
                { label = 16
                , age = 0.0
                }
              }
            }
          }
        }
      , right = Node
        { age = 4.0
        , label = 49
        , left = Node
          { age = 3.0
          , label = 50
          , left = Node
            { age = 2.0
            , label = 51
            , left = Node
              { age = 0.0
              , label = 52
              , left = Leaf
                { label = 17
                , age = 0.0
                }
              , right = Leaf
                { label = 18
                , age = 0.0
                }
              }
            , right = Node
              { age = 0.0
              , label = 53
              , left = Leaf
                { label = 19
                , age = 0.0
                }
              , right = Leaf
                { label = 20
                , age = 0.0
                }
              }
            }
          , right = Node
            { age = 2.0
            , label = 54
            , left = Node
              { age = 0.0
              , label = 55
              , left = Leaf
                { label = 21
                , age = 0.0
                }
              , right = Leaf
                { label = 22
                , age = 0.0
                }
              }
            , right = Node
              { age = 0.0
              , label = 56
              , left = Leaf
                { label = 23
                , age = 0.0
                }
              , right = Leaf
                { label = 24
                , age = 0.0
                }
              }
            }
          }
        , right = Node
          { age = 3.0
          , label = 57
          , left = Node
            { age = 2.0
            , label = 58
            , left = Node
              { age = 0.0
              , label = 59
              , left = Leaf
                { label = 25
                , age = 0.0
                }
              , right = Leaf
                { label = 26
                , age = 0.0
                }
              }
            , right = Node
              { age = 0.0
              , label = 60
              , left = Leaf
                { label = 27
                , age = 0.0
                }
              , right = Leaf
                { label = 28
                , age = 0.0
                }
              }
            }
          , right = Node
            { age = 2.0
            , label = 61
            , left = Node
              { age = 0.0
              , label = 62
              , left = Leaf
                { label = 29
                , age = 0.0
                }
              , right = Leaf
                { label = 30
                , age = 0.0
                }
              }
            , right = Node
              { age = 0.0
              , label = 63
              , left = Leaf
                { label = 31
                , age = 0.0
                }
              , right = Leaf
                { label = 32
                , age = 0.0
                }
              }
            }
          }
        }
      }
, interactions =
    [ [2, 0]
    , [2, 0]
    , [2, 0]
    , [2, 0]
    , [2, 0]
    , [2, 0]
    , [2, 0]
    , [2, 0]
    , [2, 1]
    , [2, 1]
    , [2, 1]
    , [2, 1]
    , [2, 1]
    , [2, 1]
    , [2, 1]
    , [2, 1]
    , [2, 2]
    , [2, 2]
    , [2, 2]
    , [2, 2]
    , [2, 2]
    , [2, 2]
    , [2, 2]
    , [2, 2]
    , [1, 2]
    , [1, 2]
    , [1, 2]
    , [1, 2]
    , [1, 2]
    , [1, 2]
    , [1, 2]
    , [1, 2]
    ]
, hostDistances =
    [ [0.0, 2.0]
    , [2.0, 0.0]
    ]
, subrootLength = 5.0
, subrootLabel = -1
} in
let tmp = anonPLACEHOLDER input {} in
dprint tmp
