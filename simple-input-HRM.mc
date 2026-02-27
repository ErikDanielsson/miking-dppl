  type TreeLabeled p18 p19 p20 in
  con Leaf: all p21. all p22. all p23. p21 -> TreeLabeled p21 p22 p23
  in
  con Node: all p24. all p25. all p26. {age: p25, left: TreeLabeled p24 p25 p26, label: p26, right: TreeLabeled p24 p25 p26} -> TreeLabeled p24 p25 p26
  in
let input1 =
  { symbiontTree =
      Node
        { age = 1.,
          label = 3,
          left = Leaf
              { age = 0., label = 1 },
          right = Leaf
              { age = 0., label = 2 } }
    , interactions =
      [ [2, 1, 2, 1, 2]
      , [1, 2, 1, 2, 1]
      ]
  , hostDistances =
      [ [0., 1., 1., 1., 1.]
      , [1., 0., 1., 1., 1.]
      , [1., 1., 0., 1., 1.]
      , [1., 1., 1., 0., 1.]
      , [1., 1., 1., 1., 0.]
      ]
  }
in

lam st.
  type Option p p1 in
  con Some: all p2. all p3. p2 -> Option p2 p3 in
  con None: all p4. all p5. p5 -> Option p4 p5 in
  type Either p6 p7 in
  con Left: all p8. all p9. p8 -> Either p8 p9 in
  con Right: all p10. all p11. p11 -> Either p10 p11 in
  type ExtArrKind in
  type ExtArr in
  type CBLASLayout in
  type CBLASTranspose in
  type MatError p12 p13 in
  con DimensionMismatch: all p14. all p15. p14 -> MatError p14 p15
  in
  con NotSquare: all p16. all p17. p17 -> MatError p16 p17 in

  type MsgTree p27 p28 p29 p30 p31 p32 p33 p34 in
  con MsgLeaf: all p35. all p36. all p37. all p38. all p39. all p40. all p41. all p42. p35 -> MsgTree p35 p36 p37 p38 p39 p40 p41 p42
  in
  con MsgNode: all p43. all p44. all p45. all p46. all p47. all p48. all p49. all p50. {age: p44, left: MsgTree p43 p44 p45 p46 p47 p48 p49 p50, label: p45, right: MsgTree p43 p44 p45 p46 p47 p48 p49 p50, outMsg: p48, leftInMsg: p49, leftKernel: p47, rightInMsg: p50, rightKernel: p46} -> MsgTree p43 p44 p45 p46 p47 p48 p49 p50
  in
  type HistoryTree p51 p52 p53 p54 p55 in
  con HistoryLeaf: all p56. all p57. all p58. all p59. all p60. p56 -> HistoryTree p56 p57 p58 p59 p60
  in
  con HistoryNode: all p61. all p62. all p63. all p64. all p65. {age: p62, left: HistoryTree p61 p62 p63 p64 p65, label: p63, right: HistoryTree p61 p62 p63 p64 p65, history: p64, repertoire: p65} -> HistoryTree p61 p62 p63 p64 p65
  in
  type Event p66 in
  con Event1: all p67. p67 -> Event p67 in
  type CorrectedBranchSample p68 in
  con CorrectedBranchSample1: all p69. p69 -> CorrectedBranchSample p69
  in
  type ModelParams p70 in
  con ModelParams1: all p71. p71 -> ModelParams p71 in
  type EmbeddedMarkovChainMatrix p72 in
  con EmbeddedMarkovChainMatrix1: all p73. p73 -> EmbeddedMarkovChainMatrix p73
  in
  type ReturnType p74 in
  con ReturnType1: all p75. p75 -> ReturnType p75 in
  type Bridge p76 in
  con Bridge1: all p77. p77 -> Bridge p77 in
  let and =
    lam a961.
      lam b331.
        match a961 with true
        then
          b331
        else
          false
  in
  let and1 =
    lam st940.
      lam a96.
        lam b33.
          p_select
            st940
            (lam x1505.
               match x1505 with true
               then
                 b33
               else
                 p_pure false)
            a96
  in
  let pow = lam x1723.
      lam y2.
        externalPow x1723 y2
  in
  let pow1 =
    lam st939.
      lam x1722.
        lam y1.
          p_map
            st939 (lam x1504.
               externalPow x1722 x1504) y1
  in
  let pow2 =
    lam st937.
      lam x1721.
        lam y.
          match
            p_map
              st937
              (lam x1501.
                 lam x1502.
                   externalPow x1501 x1502)
              x1721
          with
            (st938, x1503)
          in
          p_apply st938 x1503 y
  in
  recursive
    let rec2 =
      lam acc.
        lam s2.
          match s2 with [ _ ] ++ _
          then
            match splitAt s2 1 with {#label"1" = x}
            in
            rec2 (concat acc (get s2 0)) x
          else match s2 with ""
          in
          acc
    let rec21 =
      lam acc1.
        lam s21.
          match s21 with [ _ ] ++ _
          then
            match splitAt s21 1 with {#label"1" = x1}
            in
            rec21 (concat acc1 (get s21 0)) x1
          else match s21 with ""
          in
          acc1
    let rec22 =
      lam st1.
        lam acc2.
          lam s22.
            match s22 with [ _ ] ++ _
            then
              match p_map st1 concat acc2 with (st2, x2)
              in
              match p_apply st2 x2 (get s22 0) with (st3, x3)
              in
              match splitAt s22 1 with {#label"1" = x4}
              in
              rec22 st3 x3 x4
            else match s22 with ""
            in
            (st1, acc2)
    let rec23 =
      lam st4.
        lam acc3.
          lam s23.
            match s23 with [ _ ] ++ _
            then
              match p_map st4 concat acc3 with (st5, x5)
              in
              match p_apply st5 x5 (get s23 0) with (st6, x6)
              in
              match splitAt s23 1 with {#label"1" = x7}
              in
              rec23 st6 x6 x7
            else match s23 with ""
            in
            (st4, acc3)
  in
  let anon = lam v3.
      lam x1500.
        v3 in
  recursive
    let rec3 =
      lam c.
        lam i1.
          lam acc11.
            match geqi i1 0 with true
            then
              rec3 c (subi i1 1) (cons (anon c i1) acc11)
            else
              acc11
  in
  recursive
    let rec31 =
      lam st7.
        lam c1.
          lam i11.
            lam acc12.
              match geqi i11 0 with true
              then
                match
                  p_map
                    st7
                    (lam x8.
                       externalExtArrGet x8 i11)
                    c1
                with
                  (st8, x9)
                in
                rec31 st8 c1 (subi i11 1) (cons x9 acc12)
              else
                (st7, acc12)
  in
  let extArrMakeUninit =
    lam kind2.
      lam n8.
        externalExtArrMakeUninit kind2 n8
  in
  let extArrGetExn =
    lam st936.
      lam a79.
        lam i23.
          p_map
            st936
            (lam x1499.
               externalExtArrGet x1499 i23)
            a79
  in
  let matErrorToString =
    lam err3.
      match err3 with DimensionMismatch carried75
      in
      "Dimension mismatch"
  in
  let matMakeUninit =
    lam kind1.
      lam m41.
        lam n71.
          { arr = externalExtArrMakeUninit kind1 (muli m41 n71),
            n = n71,
            m = m41 }
  in
  let matMakeUninit1 =
    lam st934.
      lam kind.
        lam m4.
          lam n7.
            match
              p_map
                st934
                (lam x1497.
                   externalExtArrMakeUninit kind (muli m4 x1497))
                n7
            with
              (st935, x1498)
            in
            (st935, { arr = x1498, n = n7, m = m4 })
  in
  let matGetExn =
    lam a701.
      lam i201.
        lam j21.
          match a701 with {arr = #var"X69"}
          in
          match a701 with {n = #var"X70"}
          in
          externalExtArrGet #var"X69" (addi (muli i201 #var"X70") j21)
  in
  let matGetExn1 =
    lam st931.
      lam a70.
        lam i20.
          lam j2.
            match
              p_map
                st931
                (lam x1492.
                   lam x1493.
                     match x1492 with {arr = #var"X67"}
                     in
                     externalExtArrGet #var"X67" x1493)
                a70
            with
              (st932, x1494)
            in
            match
              p_map
                st932
                (lam x1495.
                   match x1495 with {n = #var"X68"}
                   in
                   addi (muli i20 #var"X68") j2)
                a70
            with
              (st933, x1496)
            in
            p_apply st933 x1494 x1496
  in
  let matCopy =
    lam st924.
      lam a64.
        match
          p_map
            st924
            (lam x1478.
               lam x1479.
                 { x1478 with arr = x1479 })
            a64
        with
          (st925, x1480)
        in
        match
          p_map
            st925
            (lam x1481.
               lam x1482.
                 tmOpaque (let b24 = extArrMakeUninit (externalExtArrKind x1481.arr) x1482
                  in
                  let #var"20" = externalCblasCopy x1482 x1481.arr 1 b24 1 in
                  b24))
            a64
        with
          (st926, x1483)
        in
        match
          p_map
            st926
            (lam x1484.
               lam x1485.
                 match x1484 with {m = #var"X66"}
                 in
                 muli #var"X66" x1485)
            a64
        with
          (st927, x1486)
        in
        match
          p_map st927 (lam x1487.
               x1487.n) a64
        with
          (st928, x1488)
        in
        match p_apply st928 x1486 x1488 with (st929, x1489)
        in
        match p_apply st929 x1483 x1489 with (st930, x1490)
        in
        p_apply st930 x1480 x1490
  in
  let matHasSameShape2 =
    lam a62.
      lam b22.
        match a62 with {m = #var"X62"}
        in
        match b22 with {m = #var"X63"}
        in
        match a62 with {n = #var"X64"}
        in
        match b22 with {n = #var"X65"}
        in
        and (eqi #var"X62" #var"X63") (eqi #var"X64" #var"X65")
  in
  let matTranposeNoAlloc =
    lam a59.
      lam b20.
        match a59 with {m = #var"X54"}
        in
        match b20 with {n = #var"X55"}
        in
        match a59 with {n = #var"X56"}
        in
        match b20 with {m = #var"X57"}
        in
        match and (eqi #var"X54" #var"X55") (eqi #var"X56" #var"X57") with true
        then
          match a59 with {m = #var"X58"}
          in
          match a59 with {n = #var"X59"}
          in
          match a59 with {arr = #var"X60"}
          in
          match b20 with {arr = #var"X61"}
          in
          let #var"19" = externalMatTranspose #var"X58" #var"X59" #var"X60" #var"X61"
          in
          Right
            {}
        else
          Left
            (DimensionMismatch
               {})
  in
  let matElemMulNoAlloc =
    lam a58.
      lam b19.
        lam c410.
          match
            and (matHasSameShape2 a58 b19) (matHasSameShape2 b19 c410)
          with
            true
          then
            match a58 with {m = #var"X49"}
            in
            match a58 with {n = #var"X50"}
            in
            match a58 with {arr = #var"X51"}
            in
            match b19 with {arr = #var"X52"}
            in
            match c410 with {arr = #var"X53"}
            in
            let #var"18" =
              externalMatElemMul #var"X49" #var"X50" #var"X51" #var"X52" #var"X53"
            in
            Right
              {}
          else
            Left
              (DimensionMismatch
                 {})
  in
  let matMulExn =
    lam st910.
      lam a52.
        lam b13.
          match
            p_map st910 (lam x1449.
                 x1449.n) a52
          with
            (st911, x1450)
          in
          match
            p_map
              st911
              (lam x1451.
                 lam x1452.
                   lam st912.
                     match
                       match eqi x1451 x1452 with true
                       then
                         match
                           p_map
                             st912
                             (lam x1453.
                                x1453.m)
                             a52
                         with
                           (st913, x1454)
                         in
                         match
                           p_map
                             st913
                             (lam x1455.
                                lam x1456.
                                  lam x1457.
                                    lam x1458.
                                      tmOpaque (let c210 = matMakeUninit (externalExtArrKind x1458.arr) x1455 x1456
                                       in
                                       let #var"13" =
                                         externalCblasGemm
                                           cblasRowMajor
                                           cblasNoTrans
                                           cblasNoTrans
                                           x1455
                                           x1456
                                           x1451
                                           1.
                                           x1457.arr
                                           x1451
                                           x1458.arr
                                           x1456
                                           0.
                                           c210.arr
                                           x1456
                                       in
                                       c210))
                             x1454
                         with
                           (st914, x1459)
                         in
                         match
                           p_map
                             st914
                             (lam x1460.
                                x1460.n)
                             b13
                         with
                           (st915, x1463)
                         in
                         match p_apply st915 x1459 x1463 with (st916, x1464)
                         in
                         match p_apply st916 x1464 a52 with (st917, x1465)
                         in
                         match p_apply st917 x1465 b13 with (st918, x1466)
                         in
                         (st918, Right
                           x1466)
                       else
                         (st912, Left
                           (DimensionMismatch
                              {}))
                     with
                       (st919, n6)
                     in
                     match n6 with Right x1467
                     then
                       p_map
                         st919
                         (lam x1468.
                            Right
                              x1468)
                         x1467
                     else match n6 with Left x1469
                     in
                     (st919, p_pure (Left
                          x1469)))
              x1450
          with
            (st920, x1470)
          in
          match
            p_map st920 (lam x1473.
                 x1473.m) b13
          with
            (st921, x1474)
          in
          match
            p_subApply st921 hrmStoreSubmodel (hrmInit {}) x1470 x1474
          with
            (st922, x1475)
          in
          match p_join st922 x1475 with (st923, x1476)
          in
          p_map
            st923
            (lam x1477.
               match x1477 with Left carried73
               then
                 error (matErrorToString carried73)
               else match x1477 with Right carried74
               in
               carried74)
            x1476
  in
  let exp1 = lam x1591.
      externalExp x1591 in
  let log1 = lam x1582.
      externalLog x1582 in
  let log11 =
    lam st909.
      lam x1581.
        p_map st909 (lam x1448.
             externalLog x1448) x1581
  in
  let cons1 = lam e24.
      lam s103.
        cons e24 s103 in
  let cons11 =
    lam st905.
      lam e23.
        lam s102.
          match e23 with Event1 x1438
          in
          match x1438 with {toState = x1439}
          in
          match
            p_map
              st905
              (lam x1440.
                 lam x1441.
                   match x1438 with {host = x1442}
                   in
                   match x1438 with {eventTime = x1443}
                   in
                   Event1
                     { host = x1442,
                       toState = x1440,
                       eventTime = x1443,
                       fromState = x1441 })
              x1439
          with
            (st906, x1444)
          in
          match x1438 with {fromState = x1445}
          in
          match p_apply st906 x1444 x1445 with (st907, x1446)
          in
          match p_map st907 cons x1446 with (st908, x1447)
          in
          p_apply st908 x1447 s102
  in
  let cons12 = lam e22.
      lam s101.
        cons e22 s101 in
  let rep =
    lam count.
      lam elem1.
        let i114 = subi count 1 in
        match geqi i114 0 with true
        then
          rec3 elem1 (subi i114 1) (cons (anon elem1 i114) "")
        else
          ""
  in
  let paste0 =
    lam l52.
      match l52 with [ _ ] ++ _
      then
        match splitAt l52 1 with {#label"1" = x1437}
        in
        rec2 (concat "" (get l52 0)) x1437
      else match l52 with ""
      in
      ""
  in
  let paste01 =
    lam st899.
      lam l51.
        match l51 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st899
              (lam st900.
                 lam x1427.
                   (st900, x1427))
              ""
          with
            (st901, x1428)
          in
          match p_map st901 concat x1428 with (st902, x1429)
          in
          match p_apply st902 x1429 (get l51 0) with (st903, x1430)
          in
          match splitAt l51 1 with {#label"1" = x1435}
          in
          rec22 st903 x1430 x1435
        else match l51 with ""
        in
        p_traverseSeq
          st899
          (lam st904.
             lam x1436.
               (st904, x1436))
          ""
  in
  let paste02 =
    lam st893.
      lam l5.
        match l5 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st893
              (lam st894.
                 lam x1417.
                   (st894, x1417))
              ""
          with
            (st895, x1418)
          in
          match p_map st895 concat x1418 with (st896, x1419)
          in
          match p_apply st896 x1419 (get l5 0) with (st897, x1420)
          in
          match splitAt l5 1 with {#label"1" = x1425}
          in
          rec23 st897 x1420 x1425
        else match l5 with ""
        in
        p_traverseSeq
          st893
          (lam st898.
             lam x1426.
               (st898, x1426))
          ""
  in
  let slice =
    lam l4.
      lam first2.
        lam last.
          subsequence l4 (subi first2 1) (subi last first2)
  in
  let length1 = lam l34.
      length l34 in
  let length11 = lam l33.
      length l33 in
  let length12 = lam l32.
      length l32 in
  let length13 = lam st892.
      lam l31.
        p_map st892 length l31
  in
  let anon1 =
    lam x1410.
      lam x1415.
        lam x1416.
          match x1416 with true
          then
            snoc x1410 (addi x1415 1)
          else
            x1410
  in
  recursive
    let work =
      lam acc21.
        lam i2.
          lam s3.
            match s3 with [ e ] ++ rest
            then
              work
                (match e with true
                 then
                   snoc acc21 (addi i2 1)
                 else
                   acc21)
                (addi i2 1)
                rest
            else
              acc21
    let work1 =
      lam st9.
        lam acc22.
          lam i21.
            lam s31.
              match s31 with [ e1 ] ++ rest1
              then
                match
                  p_bind
                    st9
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st10.
                       lam x10.
                         match x10 with true
                         then
                           p_map
                             st10
                             (lam x11.
                                snoc x11 (addi i21 1))
                             acc22
                         else
                           (st10, acc22))
                    e1
                with
                  (st11, x12)
                in
                work1 st11 x12 (addi i21 1) rest1
              else
                (st9, acc22)
  in
  let whichTrue =
    lam s73.
      match s73 with [ e21 ] ++ rest4
      then
        work (anon1 "" 0 e21) (addi 0 1) rest4
      else
        ""
  in
  let whichTrue1 =
    lam st889.
      lam s72.
        match s72 with [ e20 ] ++ rest3
        then
          match
            p_map
              st889
              (lam x1407.
                 match x1407 with true
                 then
                   snoc "" (addi 0 1)
                 else
                   "")
              e20
          with
            (st890, x1408)
          in
          work1 st890 x1408 (addi 0 1) rest3
        else
          p_traverseSeq
            st889
            (lam st891.
               lam x1409.
                 (st891, x1409))
            ""
  in
  let whichTrue2 =
    lam st888.
      lam s71.
        p_map
          st888
          (lam x1406.
             match x1406 with [ e19 ] ++ rest2
             then
               work (anon1 "" 0 e19) (addi 0 1) rest2
             else
               "")
          s71
  in
  let bool2real =
    lam st887.
      lam v.
        p_map
          st887
          (lam x1405.
             match x1405 with true
             then
               1.
             else
               0.)
          v
  in
  let mtxCreate =
    lam rows1.
      lam cols12.
        lam data1.
          let a661 =
            tmOpaque (let len2 = length data1 in
             let a752 = externalExtArrMakeUninit extArrKindFloat64 len2 in
             recursive
               let work32 =
                 lam i213.
                   match eqi i213 len2 with true
                   then
                     {}
                   else
                     let #var"2157" = externalExtArrSet a752 i213 (get data1 i213)
                     in
                     work32 (addi i213 1)
             in
             let #var"2212" = work32 0 in
             a752)
          in
          match eqi (muli rows1 cols12) (externalExtArrLength a661) with true
          then
            { arr = a661, n = cols12, m = rows1 }
          else
            error "matFromArrExn: dimensions mismatch"
  in
  let mtxCreate1 =
    lam st883.
      lam rows.
        lam cols11.
          lam data.
            match
              p_traverseSeq
                st883
                (lam st884.
                   lam x1396.
                     (st884, x1396))
                data
            with
              (st885, x1397)
            in
            match
              p_map
                st885
                (lam x1398.
                   tmOpaque (let len1 = length x1398 in
                    let a751 = externalExtArrMakeUninit extArrKindFloat64 len1 in
                    recursive
                      let work31 =
                        lam i212.
                          match eqi i212 len1 with true
                          then
                            {}
                          else
                            let #var"2156" = externalExtArrSet a751 i212 (get x1398 i212)
                            in
                            work31 (addi i212 1)
                    in
                    let #var"2211" = work31 0 in
                    a751))
                x1397
            with
              (st886, x1399)
            in
            p_map
              st886
              (lam x1400.
                 match eqi (muli rows cols11) (externalExtArrLength x1400) with true
                 then
                   { arr = x1400, n = cols11, m = rows }
                 else
                   error "matFromArrExn: dimensions mismatch")
              x1399
  in
  let mtxGet =
    lam st882.
      lam row13.
        lam col2.
          lam mtx62.
            matGetExn1 st882 mtx62 (subi row13 1) (subi col2 1)
  in
  let mtxGet1 =
    lam st876.
      lam row12.
        lam col1.
          lam mtx61.
            match
              p_map
                st876
                (lam x1377.
                   lam x1378.
                     match x1377 with {arr = #var"X48"}
                     in
                     externalExtArrGet #var"X48" x1378)
                mtx61
            with
              (st877, x1379)
            in
            match
              p_map st877 (lam x1380.
                   subi x1380 1) row12
            with
              (st878, x1385)
            in
            match
              p_map
                st878
                (lam x1386.
                   lam x1387.
                     addi (muli x1386 x1387) (subi col1 1))
                x1385
            with
              (st879, x1388)
            in
            match
              p_map st879 (lam x1389.
                   x1389.n) mtx61
            with
              (st880, x1390)
            in
            match p_apply st880 x1388 x1390 with (st881, x1395)
            in
            p_apply st881 x1379 x1395
  in
  let mtxGet2 =
    lam st868.
      lam row11.
        lam col.
          lam mtx6.
            match
              p_map
                st868
                (lam x1358.
                   lam x1359.
                     match x1358 with {arr = #var"X47"}
                     in
                     externalExtArrGet #var"X47" x1359)
                mtx6
            with
              (st869, x1360)
            in
            match
              p_map st869 (lam x1365.
                   subi x1365 1) row11
            with
              (st870, x1366)
            in
            match
              p_map
                st870
                (lam x1367.
                   lam x1368.
                     lam x1369.
                       addi (muli x1367 x1368) x1369)
                x1366
            with
              (st871, x1370)
            in
            match
              p_map st871 (lam x1371.
                   x1371.n) mtx6
            with
              (st872, x1372)
            in
            match p_apply st872 x1370 x1372 with (st873, x1373)
            in
            match
              p_map st873 (lam x1374.
                   subi x1374 1) col
            with
              (st874, x1375)
            in
            match p_apply st874 x1373 x1375 with (st875, x1376)
            in
            p_apply st875 x1360 x1376
  in
  let anon2 =
    lam new5.
      lam mtx55.
        lam row5.
          lam x1356.
            lam x1357.
              match new5 with {arr = #var"X45"}
              in
              match new5 with {n = #var"X46"}
              in
              externalExtArrSet
                #var"X45"
                (addi (muli 0 #var"X46") x1356)
                (matGetExn mtx55 (subi row5 1) (subi x1357 1))
  in
  let anon3 =
    lam st865.
      lam new4.
        lam mtx54.
          lam row4.
            lam x1345.
              lam x1346.
                match new4 with {arr = #var"X43"}
                in
                match
                  p_map
                    st865
                    (lam x1347.
                       lam x1348.
                         externalExtArrSet x1347 x1348 (matGetExn mtx54 (subi row4 1) (subi x1346 1)))
                    #var"X43"
                with
                  (st866, x1349)
                in
                match new4 with {n = #var"X44"}
                in
                match
                  p_map
                    st866
                    (lam x1350.
                       addi (muli 0 x1350) x1345)
                    #var"X44"
                with
                  (st867, x1355)
                in
                p_apply st867 x1349 x1355
  in
  let anon4 =
    lam st859.
      lam new3.
        lam mtx53.
          lam row3.
            lam x1329.
              lam x1330.
                match new3 with {arr = #var"X39"}
                in
                match
                  p_map
                    st859
                    (lam x1334.
                       lam x1335.
                         lam x1336.
                           externalExtArrSet x1334 x1335 x1336)
                    #var"X39"
                with
                  (st860, x1337)
                in
                match new3 with {n = #var"X40"}
                in
                match
                  p_map
                    st860
                    (lam x1338.
                       addi (muli 0 x1338) x1329)
                    #var"X40"
                with
                  (st861, x1339)
                in
                match p_apply st861 x1337 x1339 with (st862, x1340)
                in
                match
                  p_map st862 (lam x1341.
                       subi x1341 1) row3
                with
                  (st863, x1342)
                in
                match
                  p_map
                    st863
                    (lam x1343.
                       match mtx53 with {arr = #var"X41"}
                       in
                       match mtx53 with {n = #var"X42"}
                       in
                       externalExtArrGet #var"X41" (addi (muli x1343 #var"X42") (subi x1330 1)))
                    x1342
                with
                  (st864, x1344)
                in
                p_apply st864 x1340 x1344
  in
  recursive
    let rec1 =
      lam c2.
        lam c3.
          lam c4.
            lam i.
              lam s1.
                match s1 with [ _,
                    _ ] ++ _
                then
                  match splitAt s1 1 with {#label"1" = x13}
                  in
                  cons
                    (anon2 c2 c3 c4 i (get s1 0)) (rec1 c2 c3 c4 (addi i 1) x13)
                else match s1 with [ e2 ]
                then
                  match splitAt s1 1 with {#label"1" = x14}
                  in
                  let slice1 = x14 in
                  [ anon2 c2 c3 c4 i e2 ]
                else match s1 with ""
                in
                ""
    let rec11 =
      lam st12.
        lam c5.
          lam c6.
            lam c7.
              lam i3.
                lam s11.
                  match s11 with [ _,
                      _ ] ++ _
                  then
                    match anon3 st12 c5 c6 c7 i3 (get s11 0) with (st13, x15)
                    in
                    match splitAt s11 1 with {#label"1" = x16}
                    in
                    match rec11 st13 c5 c6 c7 (addi i3 1) x16 with (st14, x17)
                    in
                    (st14, cons x15 x17)
                  else match s11 with [ e3 ]
                  then
                    match splitAt s11 1 with {#label"1" = x18}
                    in
                    let slice2 = x18 in
                    match anon3 st12 c5 c6 c7 i3 e3 with (st15, x19)
                    in
                    (st15, [ x19 ])
                  else match s11 with ""
                  in
                  (st12, "")
    let rec12 =
      lam st16.
        lam c8.
          lam c9.
            lam c10.
              lam i4.
                lam s12.
                  match s12 with [ _,
                      _ ] ++ _
                  then
                    match anon4 st16 c8 c9 c10 i4 (get s12 0) with (st17, x20)
                    in
                    match splitAt s12 1 with {#label"1" = x21}
                    in
                    match rec12 st17 c8 c9 c10 (addi i4 1) x21 with (st18, x22)
                    in
                    (st18, cons x20 x22)
                  else match s12 with [ e4 ]
                  then
                    match splitAt s12 1 with {#label"1" = x23}
                    in
                    let slice3 = x23 in
                    match anon4 st16 c8 c9 c10 i4 e4 with (st19, x24)
                    in
                    (st19, [ x24 ])
                  else match s12 with ""
                  in
                  (st16, "")
  in
  let mtxRowCols =
    lam mtx52.
      lam row2.
        lam cols2.
          match mtx52 with {arr = #var"X38"}
          in
          let new2 =
            matMakeUninit (externalExtArrKind #var"X38") 1 (length cols2)
          in
          let #var"2412" = rec1 new2 mtx52 row2 0 cols2 in
          let #var"102" = {} in
          new2
  in
  let mtxRowCols1 =
    lam st849.
      lam mtx51.
        lam row1.
          lam cols1.
            match mtx51 with {arr = #var"X37"}
            in
            match p_map st849 length cols1 with (st850, x1317)
            in
            match
              matMakeUninit1 st850 (externalExtArrKind #var"X37") 1 x1317
            with
              (st851, new1)
            in
            match
              p_bind
                st851
                hrmStoreSubmodel
                (hrmInit {})
                (lam st852.
                   lam x1318.
                     match
                       match x1318 with [ _,
                           _ ] ++ _
                       then
                         match anon3 st852 new1 mtx51 row1 0 (get x1318 0) with (st853, x1319)
                         in
                         match splitAt x1318 1 with {#label"1" = x1320}
                         in
                         match rec11 st853 new1 mtx51 row1 (addi 0 1) x1320 with (st854, x1324)
                         in
                         (st854, cons x1319 x1324)
                       else match x1318 with [ e18 ]
                       then
                         match splitAt x1318 1 with {#label"1" = x1325}
                         in
                         let slice17 = x1325 in
                         match anon3 st852 new1 mtx51 row1 0 e18 with (st855, x1326)
                         in
                         (st855, [ x1326 ])
                       else match x1318 with ""
                       in
                       (st852, "")
                     with
                       (st856, x1327)
                     in
                     p_traverseSeq
                       st856
                       (lam st857.
                          lam x1328.
                            (st857, x1328))
                       x1327)
                cols1
            with
              (st858, #var"2411")
            in
            let #var"101" = {} in
            (st858, new1)
  in
  let mtxRowCols2 =
    lam st839.
      lam mtx5.
        lam row.
          lam cols.
            match mtx5 with {arr = #var"X36"}
            in
            match p_map st839 length cols with (st840, x1305)
            in
            match
              matMakeUninit1 st840 (externalExtArrKind #var"X36") 1 x1305
            with
              (st841, new)
            in
            match
              p_bind
                st841
                hrmStoreSubmodel
                (hrmInit {})
                (lam st842.
                   lam x1306.
                     match
                       match x1306 with [ _,
                           _ ] ++ _
                       then
                         match anon4 st842 new mtx5 row 0 (get x1306 0) with (st843, x1307)
                         in
                         match splitAt x1306 1 with {#label"1" = x1308}
                         in
                         match rec12 st843 new mtx5 row (addi 0 1) x1308 with (st844, x1309)
                         in
                         (st844, cons x1307 x1309)
                       else match x1306 with [ e17 ]
                       then
                         match splitAt x1306 1 with {#label"1" = x1310}
                         in
                         let slice16 = x1310 in
                         match anon4 st842 new mtx5 row 0 e17 with (st845, x1314)
                         in
                         (st845, [ x1314 ])
                       else match x1306 with ""
                       in
                       (st842, "")
                     with
                       (st846, x1315)
                     in
                     p_traverseSeq
                       st846
                       (lam st847.
                          lam x1316.
                            (st847, x1316))
                       x1315)
                cols
            with
              (st848, #var"2410")
            in
            let #var"10" = {} in
            (st848, new)
  in
  let mtxSclrMul =
    lam st831.
      lam scalar.
        lam mtx41.
          match
            p_map st831 (lam x1292.
                 x1292.m) mtx41
          with
            (st832, m21)
          in
          match
            p_map st832 (lam x1293.
                 x1293.n) mtx41
          with
            (st833, n51)
          in
          match
            p_map
              st833
              (lam x1294.
                 lam x1295.
                   lam x1296.
                     lam x1297.
                       tmOpaque (let b151 = matMakeUninit (externalExtArrKind x1297.arr) x1294 x1295
                        in
                        let #var"141" = externalCblasCopy x1296 x1297.arr 1 b151.arr 1
                        in
                        let #var"151" = externalCblasScal x1296 scalar b151.arr 1 in
                        b151))
              m21
          with
            (st834, x1298)
          in
          match p_apply st834 x1298 n51 with (st835, x1299)
          in
          match
            p_map
              st835
              (lam x1300.
                 lam x1301.
                   muli x1300 x1301)
              m21
          with
            (st836, x1302)
          in
          match p_apply st836 x1302 n51 with (st837, x1303)
          in
          match p_apply st837 x1299 x1303 with (st838, x1304)
          in
          p_apply st838 x1304 mtx41
  in
  let mtxTrans =
    lam st830.
      lam mtx3.
        p_map
          st830
          (lam x1291.
             tmOpaque (let b18 = matMakeUninit (externalExtArrKind x1291.arr) x1291.n x1291.m
              in
              let #var"17" = matTranposeNoAlloc x1291 b18 in
              b18))
          mtx3
  in
  let anon5 =
    lam st825.
      lam mtx112.
        lam mtx241.
          lam x1282.
            match
              p_map
                st825
                (lam x1283.
                   lam x1284.
                     match x1283 with {arr = #var"X35"}
                     in
                     externalExtArrSet #var"X35" x1282 x1284)
                mtx241
            with
              (st826, x1285)
            in
            match
              p_map st826 (lam x1286.
                   x1286.arr) mtx112
            with
              (st827, x1287)
            in
            match extArrGetExn st827 x1287 x1282 with (st828, x1288)
            in
            match
              p_map
                st828
                (lam x1289.
                   match gtf x1289 0. with true
                   then
                     x1289
                   else
                     0.)
                x1288
            with
              (st829, x1290)
            in
            p_apply st829 x1285 x1290
  in
  recursive
    let rec4 =
      lam st20.
        lam c11.
          lam c12.
            lam n.
              lam i31.
                match geqi i31 n with true
                then
                  (st20, {})
                else match anon5 st20 c11 c12 i31 with (st21, #var"")
                in
                rec4 st21 c11 c12 n (addi i31 1)
  in
  let anon6 =
    lam st798.
      lam mtx82.
        lam mtx212.
          lam x1229.
            lam x1230.
              match
                p_map
                  st798
                  (lam x1231.
                     lam x1232.
                       lam x1233.
                         match x1231 with {arr = #var"X33"}
                         in
                         externalExtArrSet #var"X33" x1232 x1233)
                  mtx212
              with
                (st799, x1234)
              in
              match
                p_map
                  st799
                  (lam x1235.
                     match x1235 with {n = #var"X34"}
                     in
                     addi (muli x1229 #var"X34") x1230)
                  mtx212
              with
                (st800, x1236)
              in
              match p_apply st800 x1234 x1236 with (st801, x1237)
              in
              match matGetExn1 st801 mtx82 x1229 x1230 with (st802, x1238)
              in
              match
                p_map
                  st802
                  (lam x1239.
                     lam x1240.
                       divf x1239 x1240)
                  x1238
              with
                (st803, x1241)
              in
              match
                p_map st803 (lam x1242.
                     x1242.m) mtx82
              with
                (st804, x1243)
              in
              match
                p_map st804 (lam x1244.
                     subi x1244 1) x1243
              with
                (st805, x1245)
              in
              match
                p_map
                  st805
                  (lam x1246.
                     match geqi x1246 0 with true
                     then
                       rec3 1. (subi x1246 1) (cons (anon 1. x1246) "")
                     else
                       "")
                  x1245
              with
                (st806, x1247)
              in
              match
                p_map
                  st806
                  (lam x1248.
                     tmOpaque (let len = length x1248 in
                      let a75 = externalExtArrMakeUninit extArrKindFloat64 len in
                      recursive
                        let work3 =
                          lam i211.
                            match eqi i211 len with true
                            then
                              {}
                            else
                              let #var"2155" = externalExtArrSet a75 i211 (get x1248 i211) in
                              work3 (addi i211 1)
                      in
                      let #var"2210" = work3 0 in
                      a75))
                  x1247
              with
                (st807, a66)
              in
              match
                p_map st807 (lam x1249.
                     x1249.m) mtx82
              with
                (st808, x1250)
              in
              match
                p_map
                  st808
                  (lam x1251.
                     lam x1252.
                       lam st809.
                         let x1253 =
                           match eqi (muli x1251 1) x1252 with true
                           then
                             { arr = a66, n = 1, m = x1251 }
                           else
                             let x1258 = error "matFromArrExn: dimensions mismatch" in
                             match x1258 with {arr = x1259}
                             in
                             match x1258 with {n = x1260}
                             in
                             match x1258 with {m = x1261}
                             in
                             { arr = p_pure x1259, n = x1260, m = x1261 }
                         in
                         match x1253 with {arr = x1254}
                         in
                         p_map
                           st809
                           (lam x1255.
                              match x1253 with {n = x1256}
                              in
                              match x1253 with {m = x1257}
                              in
                              { arr = x1255, n = x1256, m = x1257 })
                           x1254)
                  x1250
              with
                (st810, x1262)
              in
              match
                p_map
                  st810
                  (lam x1263.
                     externalExtArrLength x1263)
                  a66
              with
                (st811, x1264)
              in
              match
                p_subApply st811 hrmStoreSubmodel (hrmInit {}) x1262 x1264
              with
                (st812, x1265)
              in
              match p_join st812 x1265 with (st813, x1266)
              in
              match matMulExn st813 mtx82 x1266 with (st814, x1267)
              in
              match
                p_map
                  st814
                  (lam x1268.
                     match x1268 with {arr = field26, n = field27, m = field28}
                     in
                     field26)
                  x1267
              with
                (st815, a73)
              in
              match
                p_map
                  st815
                  (lam x1269.
                     externalExtArrLength x1269)
                  a73
              with
                (st816, x1270)
              in
              match
                p_map st816 (lam x1271.
                     subi x1271 1) x1270
              with
                (st817, x1272)
              in
              match
                p_bind
                  st817
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st818.
                     lam x1273.
                       match
                         match geqi x1273 0 with true
                         then
                           match
                             p_map
                               st818
                               (lam x1274.
                                  externalExtArrGet x1274 x1273)
                               a73
                           with
                             (st819, x1275)
                           in
                           rec31 st819 a73 (subi x1273 1) (cons x1275 "")
                         else
                           (st818, "")
                       with
                         (st820, x1276)
                       in
                       p_traverseSeq
                         st820
                         (lam st821.
                            lam x1277.
                              (st821, x1277))
                         x1276)
                  x1272
              with
                (st822, x1278)
              in
              match
                p_map
                  st822 (lam x1279.
                     get x1279 x1229) x1278
              with
                (st823, x1280)
              in
              match p_apply st823 x1241 x1280 with (st824, x1281)
              in
              p_apply st824 x1237 x1281
  in
  recursive
    let rec41 =
      lam st22.
        lam c13.
          lam c14.
            lam c15.
              lam n1.
                lam i32.
                  match geqi i32 n1 with true
                  then
                    (st22, {})
                  else match anon6 st22 c13 c14 c15 i32 with (st23, #var"1")
                  in
                  rec41 st23 c13 c14 c15 n1 (addi i32 1)
  in
  let anon7 =
    lam st794.
      lam mtx81.
        lam mtx211.
          lam x1225.
            match
              p_map st794 (lam x1226.
                   x1226.n) mtx81
            with
              (st795, x1227)
            in
            p_subMap
              st795
              hrmStoreSubmodel
              (hrmInit {})
              (lam x1228.
                 lam st796.
                   match geqi 0 x1228 with true
                   then
                     (st796, {})
                   else match anon6 st796 mtx81 mtx211 #frozen"x1225" 0 with (st797, #var"6")
                   in
                   rec41 st797 mtx81 mtx211 #frozen"x1225" x1228 (addi 0 1))
              x1227
  in
  recursive
    let rec42 =
      lam st24.
        lam c16.
          lam c17.
            lam n2.
              lam i33.
                match geqi i33 n2 with true
                then
                  (st24, {})
                else match anon7 st24 c16 c17 i33 with (st25, #var"2")
                in
                rec42 st25 c16 c17 n2 (addi i33 1)
  in
  let mtxExpRateSafe =
    lam st777.
      lam mtx2.
        match
          p_map
            st777
            (lam x1208.
               lam x1209.
                 match x1208 with {m = #var"X28"}
                 in
                 match eqi #var"X28" x1209 with true
                 then
                   match x1208 with {m = #var"X29"}
                   in
                   match x1208 with {n = #var"X30"}
                   in
                   match x1208 with {arr = #var"X31"}
                   in
                   Right
                     { x1208 with arr = externalMatExp #var"X29" #var"X30" #var"X31" }
                 else
                   Left
                     (NotSquare
                        {}))
            mtx2
        with
          (st778, x1210)
        in
        match
          p_map st778 (lam x1211.
               x1211.n) mtx2
        with
          (st779, x1212)
        in
        match p_apply st779 x1210 x1212 with (st780, x1213)
        in
        match
          p_map
            st780
            (lam x1214.
               match x1214 with Left carried70
               then
                 match carried70 with NotSquare carried71
                 in
                 error "Not square"
               else match x1214 with Right carried72
               in
               carried72)
            x1213
        with
          (st781, mtx111)
        in
        match matCopy st781 mtx111 with (st782, mtx24)
        in
        match
          p_map
            st782
            (lam x1215.
               lam x1216.
                 match x1215 with {m = #var"X32"}
                 in
                 muli #var"X32" x1216)
            mtx111
        with
          (st783, x1217)
        in
        match
          p_map st783 (lam x1218.
               x1218.n) mtx111
        with
          (st784, x1219)
        in
        match p_apply st784 x1217 x1219 with (st785, x1220)
        in
        match
          p_subMap
            st785
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1221.
               lam st786.
                 match geqi 0 x1221 with true
                 then
                   (st786, {})
                 else match anon5 st786 mtx111 mtx24 0 with (st787, #var"4")
                 in
                 rec4 st787 mtx111 mtx24 x1221 (addi 0 1))
            x1220
        with
          (st788, #var"12")
        in
        let mtx8 = mtx24 in
        match matCopy st788 mtx8 with (st789, mtx21)
        in
        match
          p_map st789 (lam x1222.
               x1222.m) mtx8
        with
          (st790, x1223)
        in
        match
          p_subMap
            st790
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1224.
               lam st791.
                 match geqi 0 x1224 with true
                 then
                   (st791, {})
                 else match anon7 st791 mtx8 mtx21 0 with (st792, #var"5")
                 in
                 rec42 st792 mtx8 mtx21 x1224 (addi 0 1))
            x1223
        with
          (st793, #var"11")
        in
        (st793, mtx21)
  in
  let mtxMul =
    lam st776.
      lam a37.
        lam b5.
          matMulExn st776 a37 b5
  in
  let eitherEither =
    lam st775.
      lam e31.
        p_map
          st775
          (lam x1207.
             match x1207 with Left carried68
             then
               error (matErrorToString carried68)
             else match x1207 with Right carried69
             in
             carried69)
          e31
  in
  let mtxElemMul =
    lam st762.
      lam a361.
        lam b41.
          match
            p_map
              st762
              (lam x1181.
                 lam x1182.
                   match x1181 with {m = #var"X26"}
                   in
                   eqi #var"X26" x1182)
              a361
          with
            (st763, x1183)
          in
          match
            p_map st763 (lam x1184.
                 x1184.m) b41
          with
            (st764, x1185)
          in
          match p_apply st764 x1183 x1185 with (st765, x1186)
          in
          match
            p_map
              st765
              (lam x1187.
                 lam x1188.
                   match x1187 with {n = #var"X27"}
                   in
                   eqi #var"X27" x1188)
              a361
          with
            (st766, x1189)
          in
          match
            p_map st766 (lam x1190.
                 x1190.n) b41
          with
            (st767, x1191)
          in
          match p_apply st767 x1189 x1191 with (st768, x1192)
          in
          match and1 st768 x1186 x1192 with (st769, x1193)
          in
          match
            p_bind
              st769
              hrmStoreSubmodel
              (hrmInit {})
              (lam st770.
                 lam x1194.
                   match
                     match x1194 with true
                     then
                       match
                         p_map
                           st770
                           (lam x1195.
                              lam x1196.
                                tmOpaque (let c311 = matMakeUninit (externalExtArrKind x1195.arr) x1195.m x1195.n
                                 in
                                 let #var"161" = matElemMulNoAlloc x1195 x1196 c311 in
                                 c311))
                           a361
                       with
                         (st771, x1197)
                       in
                       match p_apply st771 x1197 b41 with (st772, x1198)
                       in
                       (st772, Right
                         x1198)
                     else
                       (st770, Left
                         (DimensionMismatch
                            {}))
                   with
                     (st773, n4)
                   in
                   match n4 with Right x1199
                   then
                     p_map
                       st773
                       (lam x1200.
                          Right
                            x1200)
                       x1199
                   else match n4 with Left x1205
                   in
                   (st773, p_pure (Left
                        x1205)))
              x1193
          with
            (st774, x1206)
          in
          eitherEither st774 x1206
  in
  recursive
    let work2 =
      lam bound.
        lam c18.
          lam i41.
            lam acc31.
              match lti i41 bound with true
              then
                match c18 with {arr = #var"X"}
                in
                work2
                  bound
                  c18
                  (addi i41 1)
                  (addf acc31 (externalExtArrGet #var"X" i41))
              else
                acc31
    let work21 =
      lam st26.
        lam bound1.
          lam c19.
            lam i42.
              lam acc32.
                match lti i42 bound1 with true
                then
                  match
                    p_map
                      st26
                      (lam x25.
                         lam x26.
                           addf x25 x26)
                      acc32
                  with
                    (st27, x27)
                  in
                  match c19 with {arr = #var"X1"}
                  in
                  match extArrGetExn st27 #var"X1" i42 with (st28, x28)
                  in
                  match p_apply st28 x27 x28 with (st29, x29)
                  in
                  work21 st29 bound1 c19 (addi i42 1) x29
                else
                  (st26, acc32)
  in
  let mtxMean =
    lam mtx11.
      match mtx11 with {m = #var"X22"}
      in
      match mtx11 with {n = #var"X23"}
      in
      match mtx11 with {m = #var"X24"}
      in
      match mtx11 with {n = #var"X25"}
      in
      divf
        (work2 (muli #var"X22" #var"X23") mtx11 0 0.)
        (int2float (muli #var"X24" #var"X25"))
  in
  let mtxMean1 =
    lam st754.
      lam mtx1.
        match mtx1 with {n = #var"X17"}
        in
        match
          p_map
            st754
            (lam x1169.
               match mtx1 with {m = #var"X18"}
               in
               muli #var"X18" x1169)
            #var"X17"
        with
          (st755, x1170)
        in
        match
          p_bind
            st755
            hrmStoreSubmodel
            (hrmInit {})
            (lam st756.
               lam x1171.
                 match lti 0 x1171 with true
                 then
                   match mtx1 with {arr = #var"X19"}
                   in
                   match extArrGetExn st756 #var"X19" 0 with (st757, x1172)
                   in
                   match
                     p_map
                       st757
                       (lam x1173.
                          addf 0. x1173)
                       x1172
                   with
                     (st758, x1174)
                   in
                   work21 st758 x1171 mtx1 (addi 0 1) x1174
                 else
                   (st756, p_pure 0.))
            x1170
        with
          (st759, x1175)
        in
        match
          p_map
            st759
            (lam x1176.
               lam x1177.
                 divf x1176 x1177)
            x1175
        with
          (st760, x1178)
        in
        match mtx1 with {n = #var"X20"}
        in
        match
          p_map
            st760
            (lam x1179.
               match mtx1 with {m = #var"X21"}
               in
               int2float (muli #var"X21" x1179))
            #var"X20"
        with
          (st761, x1180)
        in
        p_apply st761 x1178 x1180
  in
  let isNaN1 =
    lam r21.
      match eqf r21 r21 with true
      then
        false
      else
        true
  in
  recursive
    let unfoldr =
      lam b0.
        let fb =
          match leqi 3 b0 with true
          then
            None
              {}
          else
            Some
              (b0, addi b0 1)
        in
        match fb with Some carried
        then
          match carried with (field, field1)
          in
          cons field (unfoldr field1)
        else match fb with None carried1
        in
        ""
    let rec =
      lam c20.
        lam s.
          match s with [ _,
              _ ] ++ _
          then
            match splitAt s 1 with {#label"1" = x30}
            in
            cons (anon8 c20 (get s 0)) (rec c20 x30)
          else match s with [ e5 ]
          then
            match splitAt s 1 with {#label"1" = x31}
            in
            let slice4 = x31 in
            [ anon8 c20 e5 ]
          else match s with ""
          in
          ""
    let map1 = lam c21.
        lam s16.
          rec c21 s16
    let anon8 =
      lam interaction.
        lam x32.
          match eqi (subi (addi interaction 1) 1) x32 with true
          then
            1.
          else
            0.
    let observationMessage =
      lam obsRepertoire.
        lam i5.
          lam max.
            match leqi i5 max with true
            then
              let interaction1 = get obsRepertoire (subi i5 1) in
              let stateMsg =
                match
                  match geqi interaction1 0 with true
                  then
                    leqi interaction1 2
                  else
                    false
                with
                  true
                then
                  map1 interaction1 (unfoldr 0)
                else
                  rep 3 1.
              in
              cons1
                (get stateMsg (subi 1 1))
                (cons1
                   (get stateMsg (subi 2 1))
                   (cons1
                      (get stateMsg (subi 3 1))
                      (observationMessage obsRepertoire (addi i5 1) max)))
            else
              ""
    let observationMessage1 =
      lam st30.
        lam obsRepertoire1.
          lam i51.
            lam max1.
              match leqi i51 max1 with true
              then
                match
                  p_map
                    st30
                    (lam x33.
                       match
                         match geqi x33 0 with true
                         then
                           leqi x33 2
                         else
                           false
                       with
                         true
                       then
                         map1 x33 (unfoldr 0)
                       else
                         rep 3 1.)
                    (get obsRepertoire1 (subi i51 1))
                with
                  (st31, stateMsg1)
                in
                match
                  p_map
                    st31
                    (lam x34.
                       get x34 (subi 1 1))
                    stateMsg1
                with
                  (st32, x35)
                in
                match
                  p_map
                    st32
                    (lam x36.
                       get x36 (subi 2 1))
                    stateMsg1
                with
                  (st33, x37)
                in
                match
                  p_map
                    st33
                    (lam x38.
                       get x38 (subi 3 1))
                    stateMsg1
                with
                  (st34, x39)
                in
                match
                  observationMessage1 st34 obsRepertoire1 (addi i51 1) max1
                with
                  (st35, x40)
                in
                (st35, cons12 x35 (cons12 x37 (cons12 x39 x40)))
              else
                (st30, "")
  in
  recursive
    let postorderTraverse =
      lam st36.
        lam tree1.
          lam qMatrix1.
            lam interactions1.
              lam nhosts1.
                match
                  match tree1 with Leaf _
                  then
                    true
                  else
                    false
                with
                  true
                then
                  let outmsg =
                    mtxCreate
                      nhosts1
                      3
                      (observationMessage
                         (get
                            interactions1
                            (subi
                               (match tree1 with Leaf carried6
                                then
                                  carried6.label
                                else match tree1 with Node carried7
                                then
                                  carried7.label
                                else
                                  let #var"23" =
                                    print
                                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 9:70-9:80>:\nField \'label\' not found\n[0m    let outmsg = mtxCreate(nhosts, 3, observationMessage(interactions[[31mtree.label[0m[0m], 1, nhosts));\n"
                                  in
                                  exit 1)
                               1))
                         1
                         nhosts1)
                  in
                  let ll = (match tree1 with Leaf carried4
                          then
                            carried4.label
                          else match tree1 with Node carried5
                          then
                            carried5.label
                          else
                            let #var"22" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 10:32-10:42>:\nField \'label\' not found\n[0m    let leafInts = interactions[[31mtree.label[0m[0m];\n"
                            in
                            exit 1) in

                  let leafInts =
                    get
                      interactions1
                      (subi
                         (match tree1 with Leaf carried4
                          then
                            carried4.label
                          else match tree1 with Node carried5
                          then
                            carried5.label
                          else
                            let #var"22" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 10:32-10:42>:\nField \'label\' not found\n[0m    let leafInts = interactions[[31mtree.label[0m[0m];\n"
                            in
                            exit 1)
                         1)
                  in
                  let __outMsg = mtxCreate nhosts1 3 (observationMessage leafInts 1 nhosts1) in
                  let st36 = p_export st36 (hrmStoreNodeMsg ll) (p_pure __outMsg) in
                  (st36, MsgLeaf
                    { age = 0.,
                      label =
                        match tree1 with Leaf carried2
                        then
                          carried2.label
                        else match tree1 with Node carried3
                        then
                          carried3.label
                        else
                          let #var"21" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 13:14-13:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                          in
                          exit 1,
                      interactions = leafInts,
                      outMsg =
                        mtxCreate nhosts1 3 (observationMessage leafInts 1 nhosts1) })
                else match
                  postorderTraverse
                    st36
                    (match tree1 with Node x231
                     then
                       x231.left
                     else
                       let #var"24" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 19:31-19:40>:\nField \'left\' not found\n[0m  let left = postorderTraverse([31mtree.left[0m[0m, qMatrix, interactions, nhosts);\n"
                       in
                       exit 1)
                    qMatrix1
                    interactions1
                    nhosts1
                with
                  (st37, left)
                in
                match
                  postorderTraverse
                    st37
                    (match tree1 with Node x221
                     then
                       x221.right
                     else
                       let #var"25" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 20:32-20:42>:\nField \'right\' not found\n[0m  let right = postorderTraverse([31mtree.right[0m[0m, qMatrix, interactions, nhosts);\n"
                       in
                       exit 1)
                    qMatrix1
                    interactions1
                    nhosts1
                with
                  (st38, right)
                in
                match
                  mtxSclrMul
                    st38
                    (subf
                       (match tree1 with Leaf carried8
                        then
                          carried8.age
                        else match tree1 with Node carried9
                        then
                          carried9.age
                        else
                          let #var"26" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:45-23:53>:\nField \'age\' not found\n[0m  let leftKernel = mtxExpRateSafe(mtxSclrMul([31mtree.age[0m[0m-left.age, qMatrix));\n"
                          in
                          exit 1)
                       (match left with MsgLeaf carried10
                        then
                          carried10.age
                        else match left with MsgNode carried11
                        then
                          carried11.age
                        else
                          let #var"27" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:54-23:62>:\nField \'age\' not found\n[0m  let leftKernel = mtxExpRateSafe(mtxSclrMul(tree.age-[31mleft.age[0m[0m, qMatrix));\n"
                          in
                          exit 1))
                    qMatrix1
                with
                  (st39, x41)
                in
                match mtxExpRateSafe st39 x41 with (st40, leftKernel)
                in
                match
                  mtxSclrMul
                    st40
                    (subf
                       (match tree1 with Leaf carried12
                        then
                          carried12.age
                        else match tree1 with Node carried13
                        then
                          carried13.age
                        else
                          let #var"28" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:46-24:54>:\nField \'age\' not found\n[0m  let rightKernel = mtxExpRateSafe(mtxSclrMul([31mtree.age[0m[0m-right.age, qMatrix));\n"
                          in
                          exit 1)
                       (match right with MsgLeaf carried14
                        then
                          carried14.age
                        else match right with MsgNode carried15
                        then
                          carried15.age
                        else
                          let #var"29" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:55-24:64>:\nField \'age\' not found\n[0m  let rightKernel = mtxExpRateSafe(mtxSclrMul(tree.age-[31mright.age[0m[0m, qMatrix));\n"
                          in
                          exit 1))
                    qMatrix1
                with
                  (st41, x42)
                in
                match mtxExpRateSafe st41 x42 with (st42, rightKernel)
                in
                match mtxTrans st42 leftKernel with (st43, x43)
                in
                -- Save the transition kernels
                let getLabel = lam n. match n with MsgLeaf l then l.label else match n with MsgNode n in n.label in
                let leftLabel = getLabel left in
                let rightLabel = getLabel right in
                let st43 = p_export st43 (hrmStoreTransKernel rightLabel) rightKernel in 
                let st43 = p_export st43 (hrmStoreTransKernel leftLabel) leftKernel in 
                match
                  mtxMul
                    st43
                    (match left with MsgLeaf carried16
                     then
                       match carried16 with {outMsg = #var"X2"}
                       in
                       p_pure #var"X2"
                     else match left with MsgNode carried17
                     then
                       carried17.outMsg
                     else
                       let #var"210" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:25-30:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n"
                       in
                       p_pure (exit 1))
                    x43
                with
                  (st44, leftInMsg)
                in
                match mtxTrans st44 rightKernel with (st45, x44)
                in
                match
                  mtxMul
                    st45
                    (match right with MsgLeaf carried18
                     then
                       match carried18 with {outMsg = #var"X3"}
                       in
                       p_pure #var"X3"
                     else match right with MsgNode carried19
                     then
                       carried19.outMsg
                     else
                       let #var"211" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 31:26-31:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n"
                       in
                       p_pure (exit 1))
                    x44
                with
                  (st46, rightInMsg)
                in
                match mtxElemMul st46 leftInMsg rightInMsg with (st47, x45)
                in
                (st47, MsgNode
                  { age =
                      match tree1 with Leaf carried20
                      then
                        carried20.age
                      else match tree1 with Node carried21
                      then
                        carried21.age
                      else
                        let #var"212" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:10-36:18>:\nField \'age\' not found\n[0m    age = [31mtree.age[0m[0m, label = tree.label,\n"
                        in
                        exit 1,
                    label =
                      match tree1 with Leaf carried22
                      then
                        carried22.label
                      else match tree1 with Node carried23
                      then
                        carried23.label
                      else
                        let #var"213" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:28-36:38>:\nField \'label\' not found\n[0m    age = tree.age, label = [31mtree.label[0m[0m,\n"
                        in
                        exit 1,
                    left = left,
                    right = right,
                    rightKernel = rightKernel,
                    leftKernel = leftKernel,
                    outMsg = x45,
                    leftInMsg = leftInMsg,
                    rightInMsg = rightInMsg })
  in
  let mtx3ToSeq =
    lam st741.
      lam mtx.
        lam i121.
          match mtxGet st741 i121 1 mtx with (st742, p111)
          in
          match mtxGet st742 i121 2 mtx with (st743, p210)
          in
          match mtxGet st743 i121 3 mtx with (st744, p310)
          in
          match
            p_map
              st744
              (lam x1150.
                 lam x1152.
                   lam x1153.
                     addf (addf x1150 x1152) x1153)
              p111
          with
            (st745, x1154)
          in
          match p_apply st745 x1154 p210 with (st746, x1155)
          in
          match p_apply st746 x1155 p310 with (st747, s51)
          in
          match
            p_map
              st747
              (lam x1156.
                 lam x1157.
                   divf x1156 x1157)
              p111
          with
            (st748, x1158)
          in
          match p_apply st748 x1158 s51 with (st749, x1159)
          in
          match
            p_map
              st749
              (lam x1160.
                 lam x1162.
                   divf x1160 x1162)
              p210
          with
            (st750, x1163)
          in
          match p_apply st750 x1163 s51 with (st751, x1164)
          in
          match
            p_map
              st751
              (lam x1165.
                 lam x1166.
                   divf x1165 x1166)
              p310
          with
            (st752, x1167)
          in
          match p_apply st752 x1167 s51 with (st753, x1168)
          in
          (st753, [ x1159,
            x1164,
            x1168 ])
  in
  recursive
    let rec24 =
      lam st48.
        lam c22.
          lam c23.
            lam acc4.
              lam s24.
                match s24 with [ _ ] ++ _
                then
                  let x46 = get s24 0 in
                  match
                    p_map
                      st48
                      (lam x47.
                         lam x48.
                           addf x47 x48)
                      acc4
                  with
                    (st49, x49)
                  in
                  match mtx3ToSeq st49 c23 x46 with (st50, params)
                  in
                  match
                    p_bind
                      st50
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st51.
                         lam x50.
                           match
                             match geqi x50 0 with true
                             then
                               lti x50 (length12 params)
                             else
                               false
                           with
                             true
                           then
                             log11 st51 (get params (subi (addi x50 1) 1))
                           else
                             (st51, p_pure (log1 0.)))
                      (get c22 (subi x46 1))
                  with
                    (st52, x51)
                  in
                  match p_apply st52 x49 x51 with (st53, x52)
                  in
                  match splitAt s24 1 with {#label"1" = x53}
                  in
                  rec24 st53 c22 c23 x52 x53
                else match s24 with ""
                in
                (st48, acc4)
  in
  let anon9 = lam x1149.
      addi x1149 1 in
  recursive
    let rec32 =
      lam i12.
        lam acc13.
          match geqi i12 0 with true
          then
            rec32 (subi i12 1) (cons (anon9 i12) acc13)
          else
            acc13
  in
  let getRepertoireSamplingDensity =
    lam st736.
      lam x1491.
        lam samplingProb1.
          lam nhosts8.
            let i113 = subi (addi (subi nhosts8 1) 1) 1 in
            let s226 =
              match geqi i113 0 with true
              then
                rec32 (subi i113 1) (cons (anon9 i113) "")
              else
                ""
            in
            match s226 with [ _ ] ++ _
            then
              let x1143 = get s226 0 in
              match mtx3ToSeq st736 samplingProb1 x1143 with (st737, params1)
              in
              match
                p_bind
                  st737
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st738.
                     lam x1144.
                       match
                         match geqi x1144 0 with true
                         then
                           lti x1144 (length12 params1)
                         else
                           false
                       with
                         true
                       then
                         log11 st738 (get params1 (subi (addi x1144 1) 1))
                       else
                         (st738, p_pure (log1 0.)))
                  (get x1491 (subi x1143 1))
              with
                (st739, x1145)
              in
              match
                p_map st739 (lam x1146.
                     addf 0. x1146) x1145
              with
                (st740, x1147)
              in
              match splitAt s226 1 with {#label"1" = x1148}
              in
              rec24 st740 x1491 samplingProb1 x1147 x1148
            else match s226 with ""
            in
            (st736, p_pure 0.)
  in
  let anon10 =
    lam x1140.
      lam x1142.
        match eqi x1142 2 with true
        then
          addi x1140 1
        else
          x1140
  in
  recursive
    let rec25 =
      lam acc5.
        lam s25.
          match s25 with [ _ ] ++ _
          then
            match splitAt s25 1 with {#label"1" = x54}
            in
            rec25 (anon10 acc5 (get s25 0)) x54
          else match s25 with ""
          in
          acc5
    let rec26 =
      lam st54.
        lam acc6.
          lam s26.
            match s26 with [ _ ] ++ _
            then
              match
                p_bind
                  st54
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st55.
                     lam x55.
                       match eqi x55 2 with true
                       then
                         p_map
                           st55 (lam x56.
                              addi x56 1) acc6
                       else
                         (st55, acc6))
                  (get s26 0)
              with
                (st56, x57)
              in
              match splitAt s26 1 with {#label"1" = x58}
              in
              rec26 st56 x57 x58
            else match s26 with ""
            in
            (st54, acc6)
  in
  let count2s =
    lam st734.
      lam repertoire21.
        match repertoire21 with [ _ ] ++ _
        then
          match
            p_map
              st734
              (lam x1137.
                 match eqi x1137 2 with true
                 then
                   addi 0 1
                 else
                   0)
              (get repertoire21 0)
          with
            (st735, x1138)
          in
          match splitAt repertoire21 1 with {#label"1" = x1139}
          in
          rec26 st735 x1138 x1139
        else match repertoire21 with ""
        in
        (st734, p_pure 0)
  in
  let updateRepertoire =
    lam st716.
      lam currRep81.
        lam event31.
          lam nhosts71.
            match
              p_map
                st716
                (lam x1115.
                   match x1115 with Event1 x1472
                   then
                     x1472.host
                   else
                     let #var"2153" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 171:18-171:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event31
            with
              (st717, hostIndex42)
            in
            match
              p_traverseSeq
                st717
                (lam st718.
                   lam x1116.
                     (st718, x1116))
                currRep81
            with
              (st719, x1117)
            in
            match
              p_map
                st719
                (lam x1118.
                   subsequence x1118 (subi 1 1))
                x1117
            with
              (st720, x1119)
            in
            match
              p_map
                st720
                (lam x1120.
                   subi x1120 1)
                hostIndex42
            with
              (st721, x1121)
            in
            match p_apply st721 x1119 x1121 with (st722, x1122)
            in
            match
              p_map
                st722
                (lam x1123.
                   match x1123 with Event1 x1462
                   then
                     x1462.toState
                   else
                     let #var"2154" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 175:7-175:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event31
            with
              (st723, x1124)
            in
            match
              p_traverseSeq
                st723
                (lam st724.
                   lam x1125.
                     (st724, x1125))
                [ x1124 ]
            with
              (st725, x1126)
            in
            match
              p_map
                st725
                (lam x1127.
                   addi x1127 1)
                hostIndex42
            with
              (st726, first1)
            in
            match
              p_traverseSeq
                st726
                (lam st727.
                   lam x1128.
                     (st727, x1128))
                currRep81
            with
              (st728, x1129)
            in
            match p_map st728 subsequence x1129 with (st729, x1130)
            in
            match
              p_map st729 (lam x1131.
                   subi x1131 1) first1
            with
              (st730, x1132)
            in
            match p_apply st730 x1130 x1132 with (st731, x1133)
            in
            match
              p_map
                st731
                (lam x1134.
                   subi (addi nhosts71 1) x1134)
                first1
            with
              (st732, x1135)
            in
            match p_apply st732 x1133 x1135 with (st733, x1136)
            in
            paste02
              st733
              [ x1122,
                x1126,
                x1136 ]
  in
  let updateRepertoire1 =
    lam st702.
      lam currRep8.
        lam event3.
          lam nhosts7.
            match
              p_map
                st702
                (lam x1096.
                   match x1096 with Event1 x1471
                   then
                     x1471.host
                   else
                     let #var"2151" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 171:18-171:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event3
            with
              (st703, hostIndex41)
            in
            match
              p_map
                st703
                (lam x1097.
                   subsequence x1097 (subi 1 1))
                currRep8
            with
              (st704, x1098)
            in
            match
              p_map
                st704
                (lam x1099.
                   subi x1099 1)
                hostIndex41
            with
              (st705, x1100)
            in
            match p_apply st705 x1098 x1100 with (st706, x1102)
            in
            match
              p_map
                st706
                (lam x1103.
                   match x1103 with Event1 x1461
                   then
                     x1461.toState
                   else
                     let #var"2152" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 175:7-175:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event3
            with
              (st707, x1104)
            in
            match
              p_traverseSeq
                st707
                (lam st708.
                   lam x1105.
                     (st708, x1105))
                [ x1104 ]
            with
              (st709, x1106)
            in
            match
              p_map
                st709
                (lam x1107.
                   addi x1107 1)
                hostIndex41
            with
              (st710, first)
            in
            match p_map st710 subsequence currRep8 with (st711, x1108)
            in
            match
              p_map st711 (lam x1109.
                   subi x1109 1) first
            with
              (st712, x1110)
            in
            match p_apply st712 x1108 x1110 with (st713, x1111)
            in
            match
              p_map
                st713
                (lam x1112.
                   subi (addi nhosts7 1) x1112)
                first
            with
              (st714, x1113)
            in
            match p_apply st714 x1111 x1113 with (st715, x1114)
            in
            paste02
              st715
              [ x1102,
                x1106,
                x1114 ]
  in
  recursive
    let ifCont3 =
      lam st57.
        lam currRep.
          lam eventSeq.
            lam eventIndex.
              lam nEvents.
                lam nhosts2.
                  lam event.
                    lam #var"3".
                      let hostIndex4 =
                        match event with Event1 x147
                        then
                          x147.host
                        else
                          let #var"216" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 171:18-171:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                          in
                          exit 1
                      in
                      let s27 =
                        [ slice currRep 1 hostIndex4,
                          [ p_pure
                              (match event with Event1 x146
                               then
                                 x146.toState
                               else
                                 let #var"215" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 175:7-175:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                                 in
                                 exit 1) ],
                          slice currRep (addi hostIndex4 1) (addi nhosts2 1) ]
                      in
                      let currRep1 =
                        match s27 with [ _ ] ++ _
                        then
                          match splitAt s27 1 with {#label"1" = x64}
                          in
                          rec21 (concat "" (get s27 0)) x64
                        else match s27 with ""
                        in
                        ""
                      in
                      let eventIndex1 = addi eventIndex 1 in
                      match gti eventIndex1 nEvents with true
                      then
                        (st57, p_pure true)
                      else match
                        p_map
                          st57
                          (lam x59.
                             get x59 (subi eventIndex1 1))
                          eventSeq
                      with
                        (st58, x60)
                      in
                      p_bind
                        st58
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st59.
                           lam x61.
                             match
                               eqi
                                 (match x61 with Event1 x301
                                  then
                                    x301.fromState
                                  else
                                    let #var"214" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 146:7-146:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                                    in
                                    exit 1)
                                 2
                             with
                               true
                             then
                               match count2s st59 currRep1 with (st60, x62)
                               in
                               p_bind
                                 st60
                                 hrmStoreSubmodel
                                 (hrmInit {})
                                 (lam st61.
                                    lam x63.
                                      match eqi x63 1 with true
                                      then
                                        (st61, p_pure false)
                                      else
                                        ifCont3 st61 currRep1 eventSeq eventIndex1 nEvents nhosts2 x61 0)
                                 x62
                             else
                               ifCont3 st59 currRep1 eventSeq eventIndex1 nEvents nhosts2 x61 0)
                        x60
    let allTimesValidBranch =
      lam st62.
        lam currRep11.
          lam eventSeq1.
            lam eventIndex11.
              lam nEvents1.
                lam nhosts3.
                  p_bind
                    st62
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st63.
                       lam x65.
                         match gti eventIndex11 x65 with true
                         then
                           (st63, p_pure true)
                         else match
                           p_map
                             st63
                             (lam x66.
                                get x66 (subi eventIndex11 1))
                             eventSeq1
                         with
                           (st64, x67)
                         in
                         p_bind
                           st64
                           hrmStoreSubmodel
                           (hrmInit {})
                           (lam st65.
                              lam x68.
                                match
                                  eqi
                                    (match x68 with Event1 x302
                                     then
                                       x302.fromState
                                     else
                                       let #var"217" =
                                         print
                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 146:7-146:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                                       in
                                       exit 1)
                                    2
                                with
                                  true
                                then
                                  match count2s st65 currRep11 with (st66, x69)
                                  in
                                  p_bind
                                    st66
                                    hrmStoreSubmodel
                                    (hrmInit {})
                                    (lam st67.
                                       lam x70.
                                         match eqi x70 1 with true
                                         then
                                           (st67, p_pure false)
                                         else
                                           ifCont3 st67 currRep11 eventSeq1 eventIndex11 x65 nhosts3 x68 0)
                                    x69
                                else
                                  ifCont3 st65 currRep11 eventSeq1 eventIndex11 x65 nhosts3 x68 0)
                           x67)
                    nEvents1
  in
  let anon11 =
    lam x1095.
      match eqi x1095 2 with true
      then
        true
      else
        eqi x1095 1
  in
  let anon12 =
    lam st701.
      lam x1093.
        p_map
          st701
          (lam x1094.
             match eqi x1094 2 with true
             then
               true
             else
               eqi x1094 1)
          x1093
  in
  recursive
    let rec5 =
      lam s4.
        match s4 with [ _,
            _ ] ++ _
        then
          match splitAt s4 1 with {#label"1" = x71}
          in
          cons (anon11 (get s4 0)) (rec5 x71)
        else match s4 with [ e6 ]
        then
          match splitAt s4 1 with {#label"1" = x72}
          in
          let slice5 = x72 in
          [ anon11 e6 ]
        else match s4 with ""
        in
        ""
    let rec6 =
      lam st68.
        lam s5.
          match s5 with [ _,
              _ ] ++ _
          then
            match anon12 st68 (get s5 0) with (st69, x73)
            in
            match splitAt s5 1 with {#label"1" = x74}
            in
            match rec6 st69 x74 with (st70, x75)
            in
            (st70, cons x73 x75)
          else match s5 with [ e7 ]
          then
            match splitAt s5 1 with {#label"1" = x76}
            in
            let slice6 = x76 in
            match anon12 st68 e7 with (st71, x77)
            in
            (st71, [ x77 ])
          else match s5 with ""
          in
          (st68, "")
  in
  let sapply = lam st700.
      lam s92.
        rec6 st700 s92
  in
  let anon13 = lam x1090.
      eqi x1090 2 in
  let anon14 =
    lam st699.
      lam x1088.
        p_map st699 (lam x1089.
             eqi x1089 2) x1088
  in
  recursive
    let rec7 =
      lam s6.
        match s6 with [ _,
            _ ] ++ _
        then
          match splitAt s6 1 with {#label"1" = x78}
          in
          cons (anon13 (get s6 0)) (rec7 x78)
        else match s6 with [ e8 ]
        then
          match splitAt s6 1 with {#label"1" = x79}
          in
          let slice7 = x79 in
          [ anon13 e8 ]
        else match s6 with ""
        in
        ""
    let rec8 =
      lam st72.
        lam s7.
          match s7 with [ _,
              _ ] ++ _
          then
            match anon14 st72 (get s7 0) with (st73, x80)
            in
            match splitAt s7 1 with {#label"1" = x81}
            in
            match rec8 st73 x81 with (st74, x82)
            in
            (st74, cons x80 x82)
          else match s7 with [ e9 ]
          then
            match splitAt s7 1 with {#label"1" = x83}
            in
            let slice8 = x83 in
            match anon14 st72 e9 with (st75, x84)
            in
            (st75, [ x84 ])
          else match s7 with ""
          in
          (st72, "")
  in
  let sapply1 = lam st698.
      lam s91.
        rec8 st698 s91
  in
  let getGainRate =
    lam st690.
      lam repertoire14.
        lam hostIndex33.
          lam modelParams123.
            let fromState53 = get repertoire14 (subi hostIndex33 1) in
            match
              mtxGet
                st690
                (addi fromState53 1)
                (addi (addi fromState53 1) 1)
                (match
                   match modelParams123 with ModelParams1 x1434
                   then
                     x1434.embeddedQMatrix
                   else
                     let #var"2145" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1424
                 then
                   x1424.mat
                 else
                   let #var"2146" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st691, baseRate13)
            in
            match eqi fromState53 0 with true
            then
              match
                p_map
                  st691
                  (lam x1074.
                     lam x1075.
                       mulf x1074 x1075)
                  baseRate13
              with
                (st692, x1076)
              in
              match
                p_map
                  st692
                  (lam x1077.
                     negf x1077)
                  (match modelParams123 with ModelParams1 x1384
                   then
                     x1384.beta
                   else
                     let #var"2147" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:30-123:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                     in
                     p_pure (exit 1))
              with
                (st693, x1078)
              in
              match
                pow1
                  st693
                  (mtxMean
                     (mtxRowCols
                        (match modelParams123 with ModelParams1 x1394
                         then
                           x1394.hostMetric
                         else
                           let #var"2148" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:6-121:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                           in
                           exit 1)
                        hostIndex33
                        (whichTrue (rec5 repertoire14))))
                  x1078
              with
                (st694, x1079)
              in
              p_apply st694 x1076 x1079
            else match
              p_map
                st691
                (lam x1080.
                   lam x1083.
                     mulf x1080 x1083)
                baseRate13
            with
              (st695, x1084)
            in
            match
              p_map
                st695
                (lam x1085.
                   negf x1085)
                (match modelParams123 with ModelParams1 x1404
                 then
                   x1404.beta
                 else
                   let #var"2149" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:30-132:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                   in
                   p_pure (exit 1))
            with
              (st696, x1086)
            in
            match
              pow1
                st696
                (mtxMean
                   (mtxRowCols
                      (match modelParams123 with ModelParams1 x1414
                       then
                         x1414.hostMetric
                       else
                         let #var"2150" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:6-130:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                         in
                         exit 1)
                      hostIndex33
                      (whichTrue (rec7 repertoire14))))
                x1086
            with
              (st697, x1087)
            in
            p_apply st697 x1084 x1087
  in
  let getGainRate1 =
    lam st671.
      lam repertoire13.
        lam hostIndex32.
          lam modelParams122.
            let fromState52 = get repertoire13 (subi hostIndex32 1) in
            match
              p_map
                st671
                (lam x1045.
                   addi x1045 1)
                fromState52
            with
              (st672, x1046)
            in
            match
              p_map
                st672
                (lam x1047.
                   addi (addi x1047 1) 1)
                fromState52
            with
              (st673, x1048)
            in
            match
              mtxGet2
                st673
                x1046
                x1048
                (match
                   match modelParams122 with ModelParams1 x1433
                   then
                     x1433.embeddedQMatrix
                   else
                     let #var"2139" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1423
                 then
                   x1423.mat
                 else
                   let #var"2140" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st674, baseRate12)
            in
            p_bind
              st674
              hrmStoreSubmodel
              (hrmInit {})
              (lam st675.
                 lam x1049.
                   match eqi x1049 0 with true
                   then
                     match
                       p_map
                         st675
                         (lam x1050.
                            lam x1053.
                              mulf x1050 x1053)
                         baseRate12
                     with
                       (st676, x1054)
                     in
                     match sapply st676 repertoire13 with (st677, x1055)
                     in
                     match whichTrue1 st677 x1055 with (st678, x1056)
                     in
                     match
                       mtxRowCols1
                         st678
                         (match modelParams122 with ModelParams1 x1393
                          then
                            x1393.hostMetric
                          else
                            let #var"2141" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:6-121:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex32
                         x1056
                     with
                       (st679, x1057)
                     in
                     match mtxMean1 st679 x1057 with (st680, x1058)
                     in
                     match
                       p_map
                         st680
                         (lam x1059.
                            negf x1059)
                         (match modelParams122 with ModelParams1 x1383
                          then
                            x1383.beta
                          else
                            let #var"2142" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:30-123:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st681, x1060)
                     in
                     match pow2 st681 x1058 x1060 with (st682, x1061)
                     in
                     p_apply st682 x1054 x1061
                   else match
                     p_map
                       st675
                       (lam x1062.
                          lam x1063.
                            mulf x1062 x1063)
                       baseRate12
                   with
                     (st683, x1064)
                   in
                   match sapply1 st683 repertoire13 with (st684, x1065)
                   in
                   match whichTrue1 st684 x1065 with (st685, x1066)
                   in
                   match
                     mtxRowCols1
                       st685
                       (match modelParams122 with ModelParams1 x1413
                        then
                          x1413.hostMetric
                        else
                          let #var"2143" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:6-130:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex32
                       x1066
                   with
                     (st686, x1067)
                   in
                   match mtxMean1 st686 x1067 with (st687, x1068)
                   in
                   match
                     p_map
                       st687
                       (lam x1069.
                          negf x1069)
                       (match modelParams122 with ModelParams1 x1403
                        then
                          x1403.beta
                        else
                          let #var"2144" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:30-132:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st688, x1070)
                   in
                   match pow2 st688 x1068 x1070 with (st689, x1073)
                   in
                   p_apply st689 x1064 x1073)
              fromState52
  in
  let getGainRate2 =
    lam st647.
      lam repertoire12.
        lam hostIndex31.
          lam modelParams121.
            match
              p_traverseSeq
                st647
                (lam st648.
                   lam x1015.
                     (st648, x1015))
                repertoire12
            with
              (st649, x1016)
            in
            match p_map st649 get x1016 with (st650, x1017)
            in
            match
              p_map
                st650
                (lam x1018.
                   subi x1018 1)
                hostIndex31
            with
              (st651, x1019)
            in
            match p_apply st651 x1017 x1019 with (st652, fromState51)
            in
            match
              p_map
                st652
                (lam x1020.
                   addi x1020 1)
                fromState51
            with
              (st653, x1021)
            in
            match
              p_map
                st653
                (lam x1022.
                   addi (addi x1022 1) 1)
                fromState51
            with
              (st654, x1023)
            in
            match
              mtxGet2
                st654
                x1021
                x1023
                (match
                   match modelParams121 with ModelParams1 x1432
                   then
                     x1432.embeddedQMatrix
                   else
                     let #var"2133" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1422
                 then
                   x1422.mat
                 else
                   let #var"2134" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st655, baseRate11)
            in
            p_bind
              st655
              hrmStoreSubmodel
              (hrmInit {})
              (lam st656.
                 lam x1024.
                   match eqi x1024 0 with true
                   then
                     match
                       p_map
                         st656
                         (lam x1025.
                            lam x1026.
                              mulf x1025 x1026)
                         baseRate11
                     with
                       (st657, x1027)
                     in
                     match sapply st657 repertoire12 with (st658, x1028)
                     in
                     let makeDirtyArray = lam st. lam arr.
                       p_traverseSeq st (lam st. lam a. (st, a)) arr 
                     in
                     match makeDirtyArray st657 repertoire12 with(st657, tmp) in
                    --  let pf = lam s. printLn (join ["Repertoire [", strJoin ", " (map int2string s), "]"]) in
                    --  match p_map st657 pf tmp with (st657, _) in
                     match whichTrue1 st658 x1028 with (st659, x1029)
                     in
                    --  let pf = lam s. printLn (join ["Which true [", strJoin ", " (map int2string s), "]"]) in
                    --  match p_map st658 pf x1029 with (st658, _) in
                     match
                       mtxRowCols2
                         st659
                         (match modelParams121 with ModelParams1 x1392
                          then
                            x1392.hostMetric
                          else
                            let #var"2135" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:6-121:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex31
                         x1029
                     with
                       (st660, x1030)
                     in
                     match mtxMean1 st660 x1030 with (st661, x1031)
                     in
                    --  let pf = lam s. printLn (join ["Normalized distance ", float2string s]) in
                    --  match p_map st661 pf x1031 with (st661, _) in
                     match
                       p_map
                         st661
                         (lam x1032.
                            negf x1032)
                         (match modelParams121 with ModelParams1 x1382
                          then
                            x1382.beta
                          else
                            let #var"2136" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:30-123:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st662, x1033)
                     in
                     match pow2 st662 x1031 x1033 with (st663, x1034)
                     in
                     p_apply st663 x1027 x1034
                   else match
                     p_map
                       st656
                       (lam x1035.
                          lam x1036.
                            mulf x1035 x1036)
                       baseRate11
                   with
                     (st664, x1037)
                   in
                   match sapply1 st664 repertoire12 with (st665, x1038)
                   in
                   match whichTrue1 st665 x1038 with (st666, x1039)
                   in
                   match
                     mtxRowCols2
                       st666
                       (match modelParams121 with ModelParams1 x1412
                        then
                          x1412.hostMetric
                        else
                          let #var"2137" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:6-130:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex31
                       x1039
                   with
                     (st667, x1040)
                   in
                   match mtxMean1 st667 x1040 with (st668, x1041)
                   in
                   match
                     p_map
                       st668
                       (lam x1042.
                          negf x1042)
                       (match modelParams121 with ModelParams1 x1402
                        then
                          x1402.beta
                        else
                          let #var"2138" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:30-132:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st669, x1043)
                   in
                   match pow2 st669 x1041 x1043 with (st670, x1044)
                   in
                   p_apply st670 x1037 x1044)
              fromState51
  in
  let getGainRate3 =
    lam st625.
      lam repertoire11.
        lam hostIndex3.
          lam modelParams12.
            match p_map st625 get repertoire11 with (st626, x981)
            in
            match
              p_map st626 (lam x982.
                   subi x982 1) hostIndex3
            with
              (st627, x983)
            in
            match p_apply st627 x981 x983 with (st628, fromState5)
            in
            match
              p_map st628 (lam x984.
                   addi x984 1) fromState5
            with
              (st629, x985)
            in
            match
              p_map
                st629
                (lam x986.
                   addi (addi x986 1) 1)
                fromState5
            with
              (st630, x987)
            in
            match
              mtxGet2
                st630
                x985
                x987
                (match
                   match modelParams12 with ModelParams1 x1431
                   then
                     x1431.embeddedQMatrix
                   else
                     let #var"2127" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1421
                 then
                   x1421.mat
                 else
                   let #var"2128" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st631, baseRate1)
            in
            p_bind
              st631
              hrmStoreSubmodel
              (hrmInit {})
              (lam st632.
                 lam x988.
                   match eqi x988 0 with true
                   then
                     match
                       p_map
                         st632
                         (lam x989.
                            lam x990.
                              mulf x989 x990)
                         baseRate1
                     with
                       (st633, x991)
                     in
                     match
                       p_map
                         st633
                         (lam x992.
                            match x992 with [ _,
                                _ ] ++ _
                            then
                              match splitAt x992 1 with {#label"1" = x993}
                              in
                              cons (anon11 (get x992 0)) (rec5 x993)
                            else match x992 with [ e15 ]
                            then
                              match splitAt x992 1 with {#label"1" = x994}
                              in
                              let slice14 = x994 in
                              [ anon11 e15 ]
                            else match x992 with ""
                            in
                            "")
                         repertoire11
                     with
                       (st634, x995)
                     in
                     match whichTrue2 st634 x995 with (st635, x996)
                     in
                     match
                       mtxRowCols2
                         st635
                         (match modelParams12 with ModelParams1 x1391
                          then
                            x1391.hostMetric
                          else
                            let #var"2129" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:6-121:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex3
                         x996
                     with
                       (st636, x997)
                     in
                     match mtxMean1 st636 x997 with (st637, x998)
                     in
                     match
                       p_map
                         st637
                         (lam x999.
                            negf x999)
                         (match modelParams12 with ModelParams1 x1381
                          then
                            x1381.beta
                          else
                            let #var"2130" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:30-123:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st638, x1000)
                     in
                     match pow2 st638 x998 x1000 with (st639, x1001)
                     in
                     p_apply st639 x991 x1001
                   else match
                     p_map
                       st632
                       (lam x1002.
                          lam x1003.
                            mulf x1002 x1003)
                       baseRate1
                   with
                     (st640, x1004)
                   in
                   match
                     p_map
                       st640
                       (lam x1005.
                          match x1005 with [ _,
                              _ ] ++ _
                          then
                            match splitAt x1005 1 with {#label"1" = x1006}
                            in
                            cons (anon13 (get x1005 0)) (rec7 x1006)
                          else match x1005 with [ e16 ]
                          then
                            match splitAt x1005 1 with {#label"1" = x1007}
                            in
                            let slice15 = x1007 in
                            [ anon13 e16 ]
                          else match x1005 with ""
                          in
                          "")
                       repertoire11
                   with
                     (st641, x1008)
                   in
                   match whichTrue2 st641 x1008 with (st642, x1009)
                   in
                   match
                     mtxRowCols2
                       st642
                       (match modelParams12 with ModelParams1 x1411
                        then
                          x1411.hostMetric
                        else
                          let #var"2131" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:6-130:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex3
                       x1009
                   with
                     (st643, x1010)
                   in
                   match mtxMean1 st643 x1010 with (st644, x1011)
                   in
                   match
                     p_map
                       st644
                       (lam x1012.
                          negf x1012)
                       (match modelParams12 with ModelParams1 x1401
                        then
                          x1401.beta
                        else
                          let #var"2132" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:30-132:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st645, x1013)
                   in
                   match pow2 st645 x1011 x1013 with (st646, x1014)
                   in
                   p_apply st646 x1004 x1014)
              fromState5
  in
  let getLossRate =
    lam st624.
      lam repertoire3.
        lam hostIndex23.
          lam modelParams103.
            let fromState33 = get repertoire3 (subi hostIndex23 1) in
            match
              match eqi fromState33 2 with true
              then
                eqi (rec25 0 repertoire3) 1
              else
                false
            with
              true
            then
              (st624, p_pure 0.)
            else
              mtxGet
                st624
                (addi fromState33 1)
                (addi (subi fromState33 1) 1)
                (match
                   match modelParams103 with ModelParams1 x1364
                   then
                     x1364.embeddedQMatrix
                   else
                     let #var"2125" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1354
                 then
                   x1354.mat
                 else
                   let #var"2126" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
  in
  let getLossRate1 =
    lam st617.
      lam repertoire2.
        lam hostIndex22.
          lam modelParams102.
            let fromState32 = get repertoire2 (subi hostIndex22 1) in
            match
              p_bind
                st617
                hrmStoreSubmodel
                (hrmInit {})
                (lam st618.
                   lam x972.
                     match eqi x972 2 with true
                     then
                       match count2s st618 repertoire2 with (st619, x973)
                       in
                       p_map
                         st619 (lam x974.
                            eqi x974 1) x973
                     else
                       (st618, p_pure false))
                fromState32
            with
              (st620, x975)
            in
            p_bind
              st620
              hrmStoreSubmodel
              (hrmInit {})
              (lam st621.
                 lam x976.
                   match x976 with true
                   then
                     (st621, p_pure 0.)
                   else match
                     p_map
                       st621
                       (lam x977.
                          addi x977 1)
                       fromState32
                   with
                     (st622, x978)
                   in
                   match
                     p_map
                       st622
                       (lam x979.
                          addi (subi x979 1) 1)
                       fromState32
                   with
                     (st623, x980)
                   in
                   mtxGet2
                     st623
                     x978
                     x980
                     (match
                        match modelParams102 with ModelParams1 x1363
                        then
                          x1363.embeddedQMatrix
                        else
                          let #var"2123" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1353
                      then
                        x1353.mat
                      else
                        let #var"2124" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x975
  in
  let getLossRate2 =
    lam st605.
      lam repertoire1.
        lam hostIndex21.
          lam modelParams101.
            match
              p_traverseSeq
                st605
                (lam st606.
                   lam x958.
                     (st606, x958))
                repertoire1
            with
              (st607, x959)
            in
            match p_map st607 get x959 with (st608, x960)
            in
            match
              p_map
                st608 (lam x961.
                   subi x961 1) hostIndex21
            with
              (st609, x962)
            in
            match p_apply st609 x960 x962 with (st610, fromState31)
            in
            match
              p_bind
                st610
                hrmStoreSubmodel
                (hrmInit {})
                (lam st611.
                   lam x963.
                     match eqi x963 2 with true
                     then
                       match count2s st611 repertoire1 with (st612, x964)
                       in
                       p_map
                         st612 (lam x965.
                            eqi x965 1) x964
                     else
                       (st611, p_pure false))
                fromState31
            with
              (st613, x966)
            in
            p_bind
              st613
              hrmStoreSubmodel
              (hrmInit {})
              (lam st614.
                 lam x967.
                   match x967 with true
                   then
                     (st614, p_pure 0.)
                   else match
                     p_map
                       st614
                       (lam x968.
                          addi x968 1)
                       fromState31
                   with
                     (st615, x969)
                   in
                   match
                     p_map
                       st615
                       (lam x970.
                          addi (subi x970 1) 1)
                       fromState31
                   with
                     (st616, x971)
                   in
                   mtxGet2
                     st616
                     x969
                     x971
                     (match
                        match modelParams101 with ModelParams1 x1362
                        then
                          x1362.embeddedQMatrix
                        else
                          let #var"2121" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1352
                      then
                        x1352.mat
                      else
                        let #var"2122" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x966
  in
  let getLossRate3 =
    lam st595.
      lam repertoire.
        lam hostIndex2.
          lam modelParams10.
            match p_map st595 get repertoire with (st596, x943)
            in
            match
              p_map st596 (lam x944.
                   subi x944 1) hostIndex2
            with
              (st597, x945)
            in
            match p_apply st597 x943 x945 with (st598, fromState3)
            in
            match
              p_bind
                st598
                hrmStoreSubmodel
                (hrmInit {})
                (lam st599.
                   lam x946.
                     match eqi x946 2 with true
                     then
                       match
                         p_map
                           st599
                           (lam x947.
                              match x947 with [ _ ] ++ _
                              then
                                match splitAt x947 1 with {#label"1" = x948}
                                in
                                rec25 (anon10 0 (get x947 0)) x948
                              else match x947 with ""
                              in
                              0)
                           repertoire
                       with
                         (st600, x949)
                       in
                       p_map
                         st600 (lam x950.
                            eqi x950 1) x949
                     else
                       (st599, p_pure false))
                fromState3
            with
              (st601, x952)
            in
            p_bind
              st601
              hrmStoreSubmodel
              (hrmInit {})
              (lam st602.
                 lam x953.
                   match x953 with true
                   then
                     (st602, p_pure 0.)
                   else match
                     p_map
                       st602
                       (lam x954.
                          addi x954 1)
                       fromState3
                   with
                     (st603, x955)
                   in
                   match
                     p_map
                       st603
                       (lam x956.
                          addi (subi x956 1) 1)
                       fromState3
                   with
                     (st604, x957)
                   in
                   mtxGet2
                     st604
                     x955
                     x957
                     (match
                        match modelParams10 with ModelParams1 x1361
                        then
                          x1361.embeddedQMatrix
                        else
                          let #var"2119" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1351
                      then
                        x1351.mat
                      else
                        let #var"2120" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x952
  in
  recursive
    let rec27 =
      lam st76.
        lam c24.
          lam c25.
            lam acc7.
              lam s28.
                match s28 with [ _ ] ++ _
                then
                  let x85 = get s28 0 in
                  match
                    p_bind
                      st76
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st77.
                         lam x86.
                           match eqi x86 2 with true
                           then
                             (st77, acc7)
                           else match
                             p_map
                               st77
                               (lam x87.
                                  lam x88.
                                    addf x87 x88)
                               acc7
                           with
                             (st78, x89)
                           in
                           match getGainRate1 st78 c24 x85 c25 with (st79, x90)
                           in
                           p_apply st79 x89 x90)
                      (get c24 (subi x85 1))
                  with
                    (st80, x91)
                  in
                  match splitAt s28 1 with {#label"1" = x92}
                  in
                  rec27 st80 c24 c25 x91 x92
                else match s28 with ""
                in
                (st76, acc7)
    let rec28 =
      lam st81.
        lam c26.
          lam c27.
            lam acc8.
              lam s29.
                match s29 with [ _ ] ++ _
                then
                  let x93 = get s29 0 in
                  match
                    p_bind
                      st81
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st82.
                         lam x94.
                           match eqi (get x94 (subi x93 1)) 2 with true
                           then
                             (st82, acc8)
                           else match
                             p_map
                               st82
                               (lam x95.
                                  lam x96.
                                    addf x95 x96)
                               acc8
                           with
                             (st83, x97)
                           in
                           match getGainRate st83 x94 x93 c27 with (st84, x98)
                           in
                           p_apply st84 x97 x98)
                      c26
                  with
                    (st85, x99)
                  in
                  match splitAt s29 1 with {#label"1" = x100}
                  in
                  rec28 st85 c26 c27 x99 x100
                else match s29 with ""
                in
                (st81, acc8)
  in
  let anon15 = lam x942.
      addi x942 1 in
  recursive
    let rec33 =
      lam i13.
        lam acc14.
          match geqi i13 0 with true
          then
            rec33 (subi i13 1) (cons (anon15 i13) acc14)
          else
            acc14
  in
  let create1 =
    lam l63.
      let i112 = subi l63 1 in
      match geqi i112 0 with true
      then
        rec33 (subi i112 1) (cons (anon15 i112) "")
      else
        ""
  in
  recursive
    let rec29 =
      lam st86.
        lam c28.
          lam c29.
            lam acc9.
              lam s210.
                match s210 with [ _ ] ++ _
                then
                  let x101 = get s210 0 in
                  match
                    p_bind
                      st86
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st87.
                         lam x102.
                           match eqi x102 0 with true
                           then
                             (st87, acc9)
                           else match
                             p_map
                               st87
                               (lam x103.
                                  lam x104.
                                    addf x103 x104)
                               acc9
                           with
                             (st88, x105)
                           in
                           match getLossRate1 st88 c28 x101 c29 with (st89, x106)
                           in
                           p_apply st89 x105 x106)
                      (get c28 (subi x101 1))
                  with
                    (st90, x107)
                  in
                  match splitAt s210 1 with {#label"1" = x108}
                  in
                  rec29 st90 c28 c29 x107 x108
                else match s210 with ""
                in
                (st86, acc9)
    let rec210 =
      lam st91.
        lam c30.
          lam c31.
            lam acc10.
              lam s211.
                match s211 with [ _ ] ++ _
                then
                  let x109 = get s211 0 in
                  match
                    p_bind
                      st91
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st92.
                         lam x110.
                           match eqi (get x110 (subi x109 1)) 0 with true
                           then
                             (st92, acc10)
                           else match
                             p_map
                               st92
                               (lam x111.
                                  lam x112.
                                    addf x111 x112)
                               acc10
                           with
                             (st93, x113)
                           in
                           match getLossRate st93 x110 x109 c31 with (st94, x114)
                           in
                           p_apply st94 x113 x114)
                      c30
                  with
                    (st95, x115)
                  in
                  match splitAt s211 1 with {#label"1" = x116}
                  in
                  rec210 st95 c30 c31 x115 x116
                else match s211 with ""
                in
                (st91, acc10)
  in
  let anon16 = lam x940.
      addi x940 1 in
  recursive
    let rec34 =
      lam i14.
        lam acc15.
          match geqi i14 0 with true
          then
            rec34 (subi i14 1) (cons (anon16 i14) acc15)
          else
            acc15
  in
  let create11 =
    lam l62.
      let i111 = subi l62 1 in
      match geqi i111 0 with true
      then
        rec34 (subi i111 1) (cons (anon16 i111) "")
      else
        ""
  in
  let getTotalRate =
    lam st585.
      lam currRep51.
        lam modelParams81.
          lam nhosts61.
            let s224 = create1 (addi (subi nhosts61 1) 1) in
            match
              match s224 with [ _ ] ++ _
              then
                let x923 = get s224 0 in
                match
                  p_bind
                    st585
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st586.
                       lam x924.
                         match eqi x924 2 with true
                         then
                           (st586, p_pure 0.)
                         else match getGainRate1 st586 currRep51 x923 modelParams81 with (st587, x925)
                         in
                         p_map
                           st587
                           (lam x926.
                              addf 0. x926)
                           x925)
                    (get currRep51 (subi x923 1))
                with
                  (st588, x927)
                in
                match splitAt s224 1 with {#label"1" = x928}
                in
                rec27 st588 currRep51 modelParams81 x927 x928
              else match s224 with ""
              in
              (st585, p_pure 0.)
            with
              (st589, x929)
            in
            match
              p_map
                st589
                (lam x930.
                   lam x931.
                     addf x930 x931)
                x929
            with
              (st590, x932)
            in
            let s225 = create11 (addi (subi nhosts61 1) 1) in
            match
              match s225 with [ _ ] ++ _
              then
                let x933 = get s225 0 in
                match
                  p_bind
                    st590
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st591.
                       lam x934.
                         match eqi x934 0 with true
                         then
                           (st591, p_pure 0.)
                         else match getLossRate1 st591 currRep51 x933 modelParams81 with (st592, x935)
                         in
                         p_map
                           st592
                           (lam x936.
                              addf 0. x936)
                           x935)
                    (get currRep51 (subi x933 1))
                with
                  (st593, x937)
                in
                match splitAt s225 1 with {#label"1" = x938}
                in
                rec29 st593 currRep51 modelParams81 x937 x938
              else match s225 with ""
              in
              (st590, p_pure 0.)
            with
              (st594, x939)
            in
            p_apply st594 x932 x939
  in
  let getTotalRate1 =
    lam st575.
      lam currRep5.
        lam modelParams8.
          lam nhosts6.
            let s222 = create1 (addi (subi nhosts6 1) 1) in
            match
              match s222 with [ _ ] ++ _
              then
                let x905 = get s222 0 in
                match
                  p_bind
                    st575
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st576.
                       lam x906.
                         match eqi (get x906 (subi x905 1)) 2 with true
                         then
                           (st576, p_pure 0.)
                         else match getGainRate st576 x906 x905 modelParams8 with (st577, x907)
                         in
                         p_map
                           st577
                           (lam x908.
                              addf 0. x908)
                           x907)
                    currRep5
                with
                  (st578, x909)
                in
                match splitAt s222 1 with {#label"1" = x910}
                in
                rec28 st578 currRep5 modelParams8 x909 x910
              else match s222 with ""
              in
              (st575, p_pure 0.)
            with
              (st579, x912)
            in
            match
              p_map
                st579
                (lam x913.
                   lam x914.
                     addf x913 x914)
                x912
            with
              (st580, x915)
            in
            let s223 = create11 (addi (subi nhosts6 1) 1) in
            match
              match s223 with [ _ ] ++ _
              then
                let x916 = get s223 0 in
                match
                  p_bind
                    st580
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st581.
                       lam x917.
                         match eqi (get x917 (subi x916 1)) 0 with true
                         then
                           (st581, p_pure 0.)
                         else match getLossRate st581 x917 x916 modelParams8 with (st582, x918)
                         in
                         p_map
                           st582
                           (lam x919.
                              addf 0. x919)
                           x918)
                    currRep5
                with
                  (st583, x920)
                in
                match splitAt s223 1 with {#label"1" = x921}
                in
                rec210 st583 currRep5 modelParams8 x920 x921
              else match s223 with ""
              in
              (st580, p_pure 0.)
            with
              (st584, x922)
            in
            p_apply st584 x915 x922
  in
  recursive
    let fullModelWeight =
      lam st96.
        lam nextIndex.
          lam currRep3.
            lam finalRep.
              lam currAge.
                lam finalAge.
                  lam eventSeq3.
                    lam nEvents3.
                      lam nhosts5.
                        lam modelParams.
                          match gti nextIndex nEvents3 with true
                          then
                            match
                              p_map
                                st96
                                (lam x117.
                                   lam x118.
                                     mulf (negf (subf x117 finalAge)) x118)
                                currAge
                            with
                              (st97, x119)
                            in
                            match getTotalRate1 st97 currRep3 modelParams nhosts5 with (st98, x120)
                            in
                            p_apply st98 x119 x120
                          else match
                            p_map
                              st96
                              (lam x121.
                                 get x121 (subi nextIndex 1))
                              eventSeq3
                          with
                            (st99, nextEvent)
                          in
                          match
                            p_map
                              st99
                              (lam x122.
                                 match x122 with Event1 x311
                                 then
                                   x311.eventTime
                                 else
                                   let #var"218" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st100, newAge)
                          in
                          match
                            getTotalRate1 st100 currRep3 modelParams nhosts5
                          with
                            (st101, totalLeavingRate1)
                          in
                          match
                            p_map
                              st101
                              (lam x123.
                                 match x123 with Event1 x133
                                 then
                                   x133.host
                                 else
                                   let #var"219" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st102, hostIndex1)
                          in
                          match
                            p_map
                              st102
                              (lam x124.
                                 lam x125.
                                   lam st103.
                                     match
                                       gti
                                         (match x124 with Event1 x131
                                          then
                                            x131.fromState
                                          else
                                            let #var"220" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x125
                                     with
                                       true
                                     then
                                       getLossRate3 st103 currRep3 hostIndex1 modelParams
                                     else
                                       getGainRate3 st103 currRep3 hostIndex1 modelParams)
                              nextEvent
                          with
                            (st104, x126)
                          in
                          match
                            p_map
                              st104
                              (lam x127.
                                 match x127 with Event1 x132
                                 then
                                   x132.toState
                                 else
                                   let #var"221" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st105, x128)
                          in
                          match
                            p_subApply st105 hrmStoreSubmodel (hrmInit {}) x126 x128
                          with
                            (st106, x129)
                          in
                          match p_join st106 x129 with (st107, x130)
                          in
                          match
                            p_map
                              st107
                              (lam x134.
                                 lam x135.
                                   divf x134 x135)
                              x130
                          with
                            (st108, x136)
                          in
                          match p_apply st108 x136 totalLeavingRate1 with (st109, x137)
                          in
                          match log11 st109 x137 with (st110, x138)
                          in
                          match
                            p_map
                              st110
                              (lam x139.
                                 lam x140.
                                   lam x141.
                                     addf (subf x139 x140) x141)
                              x138
                          with
                            (st111, x142)
                          in
                          match
                            p_map
                              st111
                              (lam x143.
                                 lam x144.
                                   lam x145.
                                     mulf (subf x143 x144) x145)
                              currAge
                          with
                            (st112, x148)
                          in
                          match p_apply st112 x148 newAge with (st113, x149)
                          in
                          match p_apply st113 x149 totalLeavingRate1 with (st114, x150)
                          in
                          match p_apply st114 x142 x150 with (st115, x151)
                          in
                          match
                            updateRepertoire1 st115 currRep3 nextEvent nhosts5
                          with
                            (st116, x152)
                          in
                          match
                            fullModelWeight
                              st116
                              (addi nextIndex 1)
                              x152
                              finalRep
                              newAge
                              finalAge
                              eventSeq3
                              nEvents3
                              nhosts5
                              modelParams
                          with
                            (st117, x153)
                          in
                          p_apply st117 x151 x153
    let fullModelWeight1 =
      lam st118.
        lam nextIndex1.
          lam currRep31.
            lam finalRep1.
              lam currAge1.
                lam finalAge1.
                  lam eventSeq31.
                    lam nEvents31.
                      lam nhosts51.
                        lam modelParams1.
                          match gti nextIndex1 nEvents31 with true
                          then
                            match
                              p_map
                                st118
                                (lam x154.
                                   lam x155.
                                     mulf (negf (subf x154 finalAge1)) x155)
                                currAge1
                            with
                              (st119, x156)
                            in
                            match
                              getTotalRate1 st119 currRep31 modelParams1 nhosts51
                            with
                              (st120, x157)
                            in
                            p_apply st120 x156 x157
                          else match
                            p_map
                              st118
                              (lam x158.
                                 get x158 (subi nextIndex1 1))
                              eventSeq31
                          with
                            (st121, nextEvent1)
                          in
                          match
                            p_map
                              st121
                              (lam x159.
                                 match x159 with Event1 x312
                                 then
                                   x312.eventTime
                                 else
                                   let #var"222" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st122, newAge1)
                          in
                          match
                            getTotalRate1 st122 currRep31 modelParams1 nhosts51
                          with
                            (st123, totalLeavingRate11)
                          in
                          match
                            p_map
                              st123
                              (lam x160.
                                 match x160 with Event1 x1331
                                 then
                                   x1331.host
                                 else
                                   let #var"223" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st124, hostIndex11)
                          in
                          match
                            p_map
                              st124
                              (lam x161.
                                 lam x162.
                                   lam st125.
                                     match
                                       gti
                                         (match x161 with Event1 x1311
                                          then
                                            x1311.fromState
                                          else
                                            let #var"224" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x162
                                     with
                                       true
                                     then
                                       getLossRate3 st125 currRep31 hostIndex11 modelParams1
                                     else
                                       getGainRate3 st125 currRep31 hostIndex11 modelParams1)
                              nextEvent1
                          with
                            (st126, x163)
                          in
                          match
                            p_map
                              st126
                              (lam x164.
                                 match x164 with Event1 x1321
                                 then
                                   x1321.toState
                                 else
                                   let #var"225" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st127, x165)
                          in
                          match
                            p_subApply st127 hrmStoreSubmodel (hrmInit {}) x163 x165
                          with
                            (st128, x166)
                          in
                          match p_join st128 x166 with (st129, x167)
                          in
                          match
                            p_map
                              st129
                              (lam x168.
                                 lam x169.
                                   divf x168 x169)
                              x167
                          with
                            (st130, x170)
                          in
                          match p_apply st130 x170 totalLeavingRate11 with (st131, x171)
                          in
                          match log11 st131 x171 with (st132, x172)
                          in
                          match
                            p_map
                              st132
                              (lam x173.
                                 lam x174.
                                   lam x175.
                                     addf (subf x173 x174) x175)
                              x172
                          with
                            (st133, x176)
                          in
                          match
                            p_map
                              st133
                              (lam x177.
                                 lam x178.
                                   lam x179.
                                     mulf (subf x177 x178) x179)
                              currAge1
                          with
                            (st134, x180)
                          in
                          match p_apply st134 x180 newAge1 with (st135, x181)
                          in
                          match p_apply st135 x181 totalLeavingRate11 with (st136, x182)
                          in
                          match p_apply st136 x176 x182 with (st137, x183)
                          in
                          match
                            updateRepertoire1 st137 currRep31 nextEvent1 nhosts51
                          with
                            (st138, x184)
                          in
                          match
                            fullModelWeight1
                              st138
                              (addi nextIndex1 1)
                              x184
                              finalRep1
                              newAge1
                              finalAge1
                              eventSeq31
                              nEvents31
                              nhosts51
                              modelParams1
                          with
                            (st139, x185)
                          in
                          p_apply st139 x183 x185
  in
  recursive
    let hostIndepLikelihood =
      lam st140.
        lam nextIndex11.
          lam currState.
            lam finalState.
              lam currAge11.
                lam finalAge11.
                  lam eventSeq4.
                    lam embeddedQMatrix.
                      match length13 st140 eventSeq4 with (st141, x186)
                      in
                      p_bind
                        st141
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st142.
                           lam x187.
                             match gti nextIndex11 x187 with true
                             then
                               match
                                 p_traverseSeq
                                   st142
                                   (lam st143.
                                      lam x188.
                                        (st143, x188))
                                   (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x321
                                    then
                                      x321.totalRates
                                    else
                                      let #var"226" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x189.
                                           p_pure x189)
                                        (exit 1))
                               with
                                 (st144, x190)
                               in
                               match
                                 p_map
                                   st144
                                   (lam x191.
                                      lam x192.
                                        mulf (negf (subf currAge11 finalAge11)) (get x191 x192))
                                   x190
                               with
                                 (st145, x193)
                               in
                               match
                                 p_map
                                   st145
                                   (lam x194.
                                      subi (addi x194 1) 1)
                                   currState
                               with
                                 (st146, x195)
                               in
                               p_apply st146 x193 x195
                             else match
                               p_map
                                 st142
                                 (lam x196.
                                    get x196 (subi nextIndex11 1))
                                 eventSeq4
                             with
                               (st147, nextEvent11)
                             in
                             match
                               p_map
                                 st147
                                 (lam x197.
                                    match x197 with Event1 x361
                                    then
                                      x361.toState
                                    else
                                      let #var"227" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent11
                             with
                               (st148, nextState)
                             in
                             match
                               p_map
                                 st148
                                 (lam x198.
                                    match x198 with Event1 x351
                                    then
                                      x351.eventTime
                                    else
                                      let #var"228" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent11
                             with
                               (st149, nextAge)
                             in
                             match
                               p_traverseSeq
                                 st149
                                 (lam st150.
                                    lam x199.
                                      p_traverseSeq
                                        st150
                                        (lam st151.
                                           lam x200.
                                             (st151, x200))
                                        x199)
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x331
                                  then
                                    x331.transitionProbs
                                  else
                                    let #var"229" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x201.
                                         map
                                           (lam x202.
                                              p_pure x202)
                                           x201)
                                      (exit 1))
                             with
                               (st152, x203)
                             in
                             match
                               p_map
                                 st152
                                 (lam x204.
                                    lam x205.
                                      get (get x204 x205))
                                 x203
                             with
                               (st153, x206)
                             in
                             match
                               p_map
                                 st153
                                 (lam x207.
                                    subi (addi x207 1) 1)
                                 currState
                             with
                               (st154, x208)
                             in
                             match p_apply st154 x206 x208 with (st155, x209)
                             in
                             match
                               p_map
                                 st155
                                 (lam x210.
                                    subi (addi x210 1) 1)
                                 nextState
                             with
                               (st156, x211)
                             in
                             match p_apply st156 x209 x211 with (st157, x212)
                             in
                             match log11 st157 x212 with (st158, x213)
                             in
                             match
                               p_map
                                 st158
                                 (lam x214.
                                    lam x215.
                                      lam x216.
                                        addf (subf x214 x215) x216)
                                 x213
                             with
                               (st159, x217)
                             in
                             match
                               p_map
                                 st159
                                 (lam x218.
                                    lam x219.
                                      mulf (subf currAge11 x218) x219)
                                 nextAge
                             with
                               (st160, x220)
                             in
                             match
                               p_traverseSeq
                                 st160
                                 (lam st161.
                                    lam x222.
                                      (st161, x222))
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x341
                                  then
                                    x341.totalRates
                                  else
                                    let #var"230" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x223.
                                         p_pure x223)
                                      (exit 1))
                             with
                               (st162, x224)
                             in
                             match p_map st162 get x224 with (st163, x225)
                             in
                             match
                               p_map
                                 st163
                                 (lam x226.
                                    subi (addi x226 1) 1)
                                 currState
                             with
                               (st164, x227)
                             in
                             match p_apply st164 x225 x227 with (st165, x228)
                             in
                             match p_apply st165 x220 x228 with (st166, x229)
                             in
                             match p_apply st166 x217 x229 with (st167, x230)
                             in
                             match
                               hostIndepLikelihood1
                                 st167
                                 (addi nextIndex11 1)
                                 nextState
                                 finalState
                                 nextAge
                                 finalAge11
                                 eventSeq4
                                 embeddedQMatrix
                             with
                               (st168, x232)
                             in
                             p_apply st168 x230 x232)
                        x186
    let hostIndepLikelihood1 =
      lam st169.
        lam nextIndex12.
          lam currState1.
            lam finalState1.
              lam currAge12.
                lam finalAge12.
                  lam eventSeq41.
                    lam embeddedQMatrix1.
                      match length13 st169 eventSeq41 with (st170, x233)
                      in
                      p_bind
                        st170
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st171.
                           lam x234.
                             match gti nextIndex12 x234 with true
                             then
                               match
                                 p_map
                                   st171
                                   (lam x235.
                                      lam x236.
                                        mulf (negf (subf x235 finalAge12)) x236)
                                   currAge12
                               with
                                 (st172, x237)
                               in
                               match
                                 p_traverseSeq
                                   st172
                                   (lam st173.
                                      lam x238.
                                        (st173, x238))
                                   (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x322
                                    then
                                      x322.totalRates
                                    else
                                      let #var"231" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x239.
                                           p_pure x239)
                                        (exit 1))
                               with
                                 (st174, x240)
                               in
                               match p_map st174 get x240 with (st175, x241)
                               in
                               match
                                 p_map
                                   st175
                                   (lam x242.
                                      subi (addi x242 1) 1)
                                   currState1
                               with
                                 (st176, x243)
                               in
                               match p_apply st176 x241 x243 with (st177, x244)
                               in
                               p_apply st177 x237 x244
                             else match
                               p_map
                                 st171
                                 (lam x245.
                                    get x245 (subi nextIndex12 1))
                                 eventSeq41
                             with
                               (st178, nextEvent12)
                             in
                             match
                               p_map
                                 st178
                                 (lam x246.
                                    match x246 with Event1 x362
                                    then
                                      x362.toState
                                    else
                                      let #var"232" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent12
                             with
                               (st179, nextState1)
                             in
                             match
                               p_map
                                 st179
                                 (lam x247.
                                    match x247 with Event1 x352
                                    then
                                      x352.eventTime
                                    else
                                      let #var"233" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent12
                             with
                               (st180, nextAge1)
                             in
                             match
                               p_traverseSeq
                                 st180
                                 (lam st181.
                                    lam x248.
                                      p_traverseSeq
                                        st181
                                        (lam st182.
                                           lam x249.
                                             (st182, x249))
                                        x248)
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x332
                                  then
                                    x332.transitionProbs
                                  else
                                    let #var"234" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x250.
                                         map
                                           (lam x251.
                                              p_pure x251)
                                           x250)
                                      (exit 1))
                             with
                               (st183, x252)
                             in
                             match
                               p_map
                                 st183
                                 (lam x253.
                                    lam x254.
                                      get (get x253 x254))
                                 x252
                             with
                               (st184, x255)
                             in
                             match
                               p_map
                                 st184
                                 (lam x256.
                                    subi (addi x256 1) 1)
                                 currState1
                             with
                               (st185, x257)
                             in
                             match p_apply st185 x255 x257 with (st186, x258)
                             in
                             match
                               p_map
                                 st186
                                 (lam x259.
                                    subi (addi x259 1) 1)
                                 nextState1
                             with
                               (st187, x260)
                             in
                             match p_apply st187 x258 x260 with (st188, x261)
                             in
                             match log11 st188 x261 with (st189, x262)
                             in
                             match
                               p_map
                                 st189
                                 (lam x263.
                                    lam x264.
                                      lam x265.
                                        addf (subf x263 x264) x265)
                                 x262
                             with
                               (st190, x266)
                             in
                             match
                               p_map
                                 st190
                                 (lam x267.
                                    lam x268.
                                      lam x269.
                                        mulf (subf x267 x268) x269)
                                 currAge12
                             with
                               (st191, x270)
                             in
                             match p_apply st191 x270 nextAge1 with (st192, x271)
                             in
                             match
                               p_traverseSeq
                                 st192
                                 (lam st193.
                                    lam x272.
                                      (st193, x272))
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x342
                                  then
                                    x342.totalRates
                                  else
                                    let #var"235" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x273.
                                         p_pure x273)
                                      (exit 1))
                             with
                               (st194, x274)
                             in
                             match p_map st194 get x274 with (st195, x275)
                             in
                             match
                               p_map
                                 st195
                                 (lam x276.
                                    subi (addi x276 1) 1)
                                 currState1
                             with
                               (st196, x277)
                             in
                             match p_apply st196 x275 x277 with (st197, x278)
                             in
                             match p_apply st197 x271 x278 with (st198, x279)
                             in
                             match p_apply st198 x266 x279 with (st199, x280)
                             in
                             match
                               hostIndepLikelihood1
                                 st199
                                 (addi nextIndex12 1)
                                 nextState1
                                 finalState1
                                 nextAge1
                                 finalAge12
                                 eventSeq41
                                 embeddedQMatrix1
                             with
                               (st200, x281)
                             in
                             p_apply st200 x280 x281)
                        x233
    let hostIndepLikelihood2 =
      lam st201.
        lam nextIndex13.
          lam currState2.
            lam finalState2.
              lam currAge13.
                lam finalAge13.
                  lam eventSeq42.
                    lam embeddedQMatrix2.
                      match length13 st201 eventSeq42 with (st202, x282)
                      in
                      p_bind
                        st202
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st203.
                           lam x283.
                             match gti nextIndex13 x283 with true
                             then
                               match
                                 p_traverseSeq
                                   st203
                                   (lam st204.
                                      lam x284.
                                        (st204, x284))
                                   (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x323
                                    then
                                      x323.totalRates
                                    else
                                      let #var"236" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x285.
                                           p_pure x285)
                                        (exit 1))
                               with
                                 (st205, x286)
                               in
                               match
                                 p_map
                                   st205
                                   (lam x287.
                                      lam x288.
                                        mulf (negf (subf currAge13 finalAge13)) (get x287 x288))
                                   x286
                               with
                                 (st206, x289)
                               in
                               match
                                 p_map
                                   st206
                                   (lam x290.
                                      subi (addi x290 1) 1)
                                   currState2
                               with
                                 (st207, x291)
                               in
                               p_apply st207 x289 x291
                             else match
                               p_map
                                 st203
                                 (lam x292.
                                    get x292 (subi nextIndex13 1))
                                 eventSeq42
                             with
                               (st208, nextEvent13)
                             in
                             match
                               p_map
                                 st208
                                 (lam x293.
                                    match x293 with Event1 x363
                                    then
                                      x363.toState
                                    else
                                      let #var"237" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent13
                             with
                               (st209, nextState2)
                             in
                             match
                               p_map
                                 st209
                                 (lam x294.
                                    match x294 with Event1 x353
                                    then
                                      x353.eventTime
                                    else
                                      let #var"238" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent13
                             with
                               (st210, nextAge2)
                             in
                             match
                               p_traverseSeq
                                 st210
                                 (lam st211.
                                    lam x295.
                                      p_traverseSeq
                                        st211
                                        (lam st212.
                                           lam x296.
                                             (st212, x296))
                                        x295)
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x333
                                  then
                                    x333.transitionProbs
                                  else
                                    let #var"239" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x297.
                                         map
                                           (lam x298.
                                              p_pure x298)
                                           x297)
                                      (exit 1))
                             with
                               (st213, x299)
                             in
                             match
                               p_map
                                 st213
                                 (lam x300.
                                    lam x303.
                                      get (get x300 x303))
                                 x299
                             with
                               (st214, x304)
                             in
                             match
                               p_map
                                 st214
                                 (lam x305.
                                    subi (addi x305 1) 1)
                                 currState2
                             with
                               (st215, x306)
                             in
                             match p_apply st215 x304 x306 with (st216, x307)
                             in
                             match
                               p_map
                                 st216
                                 (lam x308.
                                    subi (addi x308 1) 1)
                                 nextState2
                             with
                               (st217, x309)
                             in
                             match p_apply st217 x307 x309 with (st218, x310)
                             in
                             match log11 st218 x310 with (st219, x313)
                             in
                             match
                               p_map
                                 st219
                                 (lam x314.
                                    lam x315.
                                      lam x316.
                                        addf (subf x314 x315) x316)
                                 x313
                             with
                               (st220, x317)
                             in
                             match
                               p_map
                                 st220
                                 (lam x318.
                                    lam x319.
                                      mulf (subf currAge13 x318) x319)
                                 nextAge2
                             with
                               (st221, x320)
                             in
                             match
                               p_traverseSeq
                                 st221
                                 (lam st222.
                                    lam x324.
                                      (st222, x324))
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x343
                                  then
                                    x343.totalRates
                                  else
                                    let #var"240" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x325.
                                         p_pure x325)
                                      (exit 1))
                             with
                               (st223, x326)
                             in
                             match p_map st223 get x326 with (st224, x327)
                             in
                             match
                               p_map
                                 st224
                                 (lam x328.
                                    subi (addi x328 1) 1)
                                 currState2
                             with
                               (st225, x329)
                             in
                             match p_apply st225 x327 x329 with (st226, x330)
                             in
                             match p_apply st226 x320 x330 with (st227, x334)
                             in
                             match p_apply st227 x317 x334 with (st228, x335)
                             in
                             match
                               hostIndepLikelihood3
                                 st228
                                 (addi nextIndex13 1)
                                 nextState2
                                 finalState2
                                 nextAge2
                                 finalAge13
                                 eventSeq42
                                 embeddedQMatrix2
                             with
                               (st229, x336)
                             in
                             p_apply st229 x335 x336)
                        x282
    let hostIndepLikelihood3 =
      lam st230.
        lam nextIndex14.
          lam currState3.
            lam finalState3.
              lam currAge14.
                lam finalAge14.
                  lam eventSeq43.
                    lam embeddedQMatrix3.
                      match length13 st230 eventSeq43 with (st231, x337)
                      in
                      p_bind
                        st231
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st232.
                           lam x338.
                             match gti nextIndex14 x338 with true
                             then
                               match
                                 p_map
                                   st232
                                   (lam x339.
                                      lam x340.
                                        mulf (negf (subf x339 finalAge14)) x340)
                                   currAge14
                               with
                                 (st233, x344)
                               in
                               match
                                 p_traverseSeq
                                   st233
                                   (lam st234.
                                      lam x345.
                                        (st234, x345))
                                   (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3210
                                    then
                                      x3210.totalRates
                                    else
                                      let #var"241" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x346.
                                           p_pure x346)
                                        (exit 1))
                               with
                                 (st235, x347)
                               in
                               match p_map st235 get x347 with (st236, x348)
                               in
                               match
                                 p_map
                                   st236
                                   (lam x349.
                                      subi (addi x349 1) 1)
                                   currState3
                               with
                                 (st237, x350)
                               in
                               match p_apply st237 x348 x350 with (st238, x354)
                               in
                               p_apply st238 x344 x354
                             else match
                               p_map
                                 st232
                                 (lam x355.
                                    get x355 (subi nextIndex14 1))
                                 eventSeq43
                             with
                               (st239, nextEvent14)
                             in
                             match
                               p_map
                                 st239
                                 (lam x356.
                                    match x356 with Event1 x364
                                    then
                                      x364.toState
                                    else
                                      let #var"242" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent14
                             with
                               (st240, nextState3)
                             in
                             match
                               p_map
                                 st240
                                 (lam x357.
                                    match x357 with Event1 x358
                                    then
                                      x358.eventTime
                                    else
                                      let #var"243" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent14
                             with
                               (st241, nextAge3)
                             in
                             match
                               p_traverseSeq
                                 st241
                                 (lam st242.
                                    lam x359.
                                      p_traverseSeq
                                        st242
                                        (lam st243.
                                           lam x360.
                                             (st243, x360))
                                        x359)
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3310
                                  then
                                    x3310.transitionProbs
                                  else
                                    let #var"244" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x365.
                                         map
                                           (lam x366.
                                              p_pure x366)
                                           x365)
                                      (exit 1))
                             with
                               (st244, x367)
                             in
                             match
                               p_map
                                 st244
                                 (lam x368.
                                    lam x369.
                                      get (get x368 x369))
                                 x367
                             with
                               (st245, x370)
                             in
                             match
                               p_map
                                 st245
                                 (lam x371.
                                    subi (addi x371 1) 1)
                                 currState3
                             with
                               (st246, x372)
                             in
                             match p_apply st246 x370 x372 with (st247, x373)
                             in
                             match
                               p_map
                                 st247
                                 (lam x374.
                                    subi (addi x374 1) 1)
                                 nextState3
                             with
                               (st248, x375)
                             in
                             match p_apply st248 x373 x375 with (st249, x376)
                             in
                             match log11 st249 x376 with (st250, x377)
                             in
                             match
                               p_map
                                 st250
                                 (lam x378.
                                    lam x379.
                                      lam x380.
                                        addf (subf x378 x379) x380)
                                 x377
                             with
                               (st251, x381)
                             in
                             match
                               p_map
                                 st251
                                 (lam x382.
                                    lam x383.
                                      lam x384.
                                        mulf (subf x382 x383) x384)
                                 currAge14
                             with
                               (st252, x385)
                             in
                             match p_apply st252 x385 nextAge3 with (st253, x386)
                             in
                             match
                               p_traverseSeq
                                 st253
                                 (lam st254.
                                    lam x387.
                                      (st254, x387))
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3410
                                  then
                                    x3410.totalRates
                                  else
                                    let #var"245" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x388.
                                         p_pure x388)
                                      (exit 1))
                             with
                               (st255, x389)
                             in
                             match p_map st255 get x389 with (st256, x390)
                             in
                             match
                               p_map
                                 st256
                                 (lam x391.
                                    subi (addi x391 1) 1)
                                 currState3
                             with
                               (st257, x392)
                             in
                             match p_apply st257 x390 x392 with (st258, x393)
                             in
                             match p_apply st258 x386 x393 with (st259, x394)
                             in
                             match p_apply st259 x381 x394 with (st260, x395)
                             in
                             match
                               hostIndepLikelihood3
                                 st260
                                 (addi nextIndex14 1)
                                 nextState3
                                 finalState3
                                 nextAge3
                                 finalAge14
                                 eventSeq43
                                 embeddedQMatrix3
                             with
                               (st261, x396)
                             in
                             p_apply st261 x395 x396)
                        x337
  in
  let anon17 = lam x904.
      addi x904 1 in
  recursive
    let rec35 =
      lam i15.
        lam acc16.
          match geqi i15 0 with true
          then
            rec35 (subi i15 1) (cons (anon17 i15) acc16)
          else
            acc16
  in
  let anon18 =
    lam st570.
      lam msg1.
        lam nodeLabel51.
          lam x897.
            match
              mtx3ToSeq st570 msg1 (addi x897 (muli nodeLabel51 0))
            with
              (st571, x898)
            in
            match
              p_traverseSeq
                st571
                (lam st572.
                   lam x899.
                     (st572, x899))
                x898
            with
              (st573, x900)
            in
            match
              p_map st573 (lam x902.
                   mkCategorical x902) x900
            with
              (st574, x903)
            in
            p_assume (join ["node: ", int2string nodeLabel51, " ", int2string x897]) st574 (hrmStoreNode nodeLabel51 x897) x903
  in
  recursive
    let rec9 =
      lam st262.
        lam c32.
          lam c33.
            lam s8.
              match s8 with [ _,
                  _ ] ++ _
              then
                match anon18 st262 c32 c33 (get s8 0) with (st263, x397)
                in
                match splitAt s8 1 with {#label"1" = x398}
                in
                match rec9 st263 c32 c33 x398 with (st264, x399)
                in
                (st264, cons x397 x399)
              else match s8 with [ e10 ]
              then
                match splitAt s8 1 with {#label"1" = x400}
                in
                let slice9 = x400 in
                match anon18 st262 c32 c33 e10 with (st265, x401)
                in
                (st265, [ x401 ])
              else match s8 with ""
              in
              (st262, "")
  in
  let suggestNodeRep =
    lam st569.
      lam msg.
        lam nHosts4.
          lam nodeLabel5.
            let i110 = subi (addi (subi nHosts4 1) 1) 1 in
            rec9
              st569
              msg
              nodeLabel5
              (match geqi i110 0 with true
               then
                 rec35 (subi i110 1) (cons (anon17 i110) "")
               else
                 "")
  in
  recursive
    let sampleHostHistoryRec =
      lam st266.
        lam currentState.
          lam finalState11.
            lam currentAge.
              lam finalAge2.
                lam host.
                  lam nodeLabel.
                    lam embeddedQMatrix11.
                      p_bind
                        st266
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st267.
                           lam x402.
                             match
                               match ltf x402 finalAge2 with true
                               then
                                 match
                                   p_map
                                     st267
                                     (lam x403.
                                        eqi x403 finalState11)
                                     currentState
                                 with
                                   (st268, x404)
                                 in
                                 match
                                   p_traverseSeq
                                     st268
                                     (lam st269.
                                        lam x405.
                                          (st269, x405))
                                     ""
                                 with
                                   (st270, x406)
                                 in
                                 (st270, Bridge1
                                   { success = x404, events = x406 })
                               else match
                                 p_traverseSeq
                                   st267
                                   (lam st271.
                                      lam x407.
                                        p_traverseSeq
                                          st271
                                          (lam st272.
                                             lam x408.
                                               (st272, x408))
                                          x407)
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x409
                                    then
                                      x409.transitionProbs
                                    else
                                      let #var"246" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 321:16-321:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x410.
                                           map
                                             (lam x411.
                                                p_pure x411)
                                             x410)
                                        (exit 1))
                               with
                                 (st273, x412)
                               in
                               match
                                 p_map
                                   st273
                                   (lam x413.
                                      lam x414.
                                        mkCategorical (get x413 x414))
                                   x412
                               with
                                 (st274, x415)
                               in
                               match
                                 p_map
                                   st274
                                   (lam x416.
                                      subi (addi x416 1) 1)
                                   currentState
                               with
                                 (st275, x417)
                               in
                               match p_apply st275 x415 x417 with (st276, x418)
                               in
                               match p_assume (join ["state: ", int2string nodeLabel, " ", int2string host]) st276 (hrmStoreBranchState nodeLabel host) x418 with (st277, nextState11)
                               in
                               match
                                 p_traverseSeq
                                   st277
                                   (lam st278.
                                      lam x419.
                                        (st278, x419))
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x3910
                                    then
                                      x3910.totalRates
                                    else
                                      let #var"247" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 325:20-325:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x420.
                                           p_pure x420)
                                        (exit 1))
                               with
                                 (st279, x421)
                               in
                               match
                                 p_map
                                   st279
                                   (lam x422.
                                      lam x423.
                                        mkExponential
                                          (addf
                                             (addf (get x422 x423) (mulf (int2float host) 0.))
                                             (mulf (int2float nodeLabel) 0.)))
                                   x421
                               with
                                 (st280, x424)
                               in
                               match
                                 p_map
                                   st280
                                   (lam x425.
                                      subi (addi x425 1) 1)
                                   nextState11
                               with
                                 (st281, x426)
                               in
                               match p_apply st281 x424 x426 with (st282, x427)
                               in
                               match p_assume (join ["time: ", int2string nodeLabel, " ", int2string host]) st282 (hrmStoreBranchTime nodeLabel host) x427 with (st283, x428)
                               in
                               match
                                 p_map
                                   st283
                                   (lam x429.
                                      subf x402 x429)
                                   x428
                               with
                                 (st284, x430)
                               in
                               match
                                 sampleHostHistoryRec
                                   st284
                                   nextState11
                                   finalState11
                                   x430
                                   finalAge2
                                   host
                                   nodeLabel
                                   embeddedQMatrix11
                               with
                                 (st285, restOfHistory)
                               in
                               match
                                 p_map
                                   st285
                                   (lam x431.
                                      match x431 with Bridge1 x3710
                                      then
                                        x3710.success
                                      else
                                        let #var"248" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 343:18-343:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st286, x432)
                               in
                               match
                                 p_map
                                   st286
                                   (lam x433.
                                      match x433 with Bridge1 x3810
                                      then
                                        x3810.events
                                      else
                                        let #var"249" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 341:10-341:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st287, x434)
                               in
                               match
                                 cons11
                                   st287
                                   (Event1
                                      { host = host,
                                        toState = nextState11,
                                        eventTime = x402,
                                        fromState = currentState })
                                   x434
                               with
                                 (st288, x435)
                               in
                               (st288, Bridge1
                                 { success = x432, events = x435 })
                             with
                               (st289, x436)
                             in
                             match x436 with Bridge1 x437
                             in
                             match x437 with {success = x438}
                             in
                             match
                               p_map
                                 st289
                                 (lam x439.
                                    lam x440.
                                      Bridge1
                                        { success = x439, events = x440 })
                                 x438
                             with
                               (st290, x441)
                             in
                             match x437 with {events = x442}
                             in
                             p_apply st290 x441 x442)
                        currentAge
    let sampleHostHistoryRec1 =
      lam st291.
        lam currentState1.
          lam finalState12.
            lam currentAge1.
              lam finalAge21.
                lam host1.
                  lam nodeLabel1.
                    lam embeddedQMatrix12.
                      p_bind
                        st291
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st292.
                           lam x443.
                             match
                               match ltf x443 finalAge21 with true
                               then
                                 match
                                   p_map
                                     st292
                                     (lam x444.
                                        lam x445.
                                          eqi x444 x445)
                                     currentState1
                                 with
                                   (st293, x446)
                                 in
                                 match p_apply st293 x446 finalState12 with (st294, x447)
                                 in
                                 match
                                   p_traverseSeq
                                     st294
                                     (lam st295.
                                        lam x448.
                                          (st295, x448))
                                     ""
                                 with
                                   (st296, x449)
                                 in
                                 (st296, Bridge1
                                   { success = x447, events = x449 })
                               else match
                                 p_traverseSeq
                                   st292
                                   (lam st297.
                                      lam x450.
                                        p_traverseSeq
                                          st297
                                          (lam st298.
                                             lam x451.
                                               (st298, x451))
                                          x450)
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x4010
                                    then
                                      x4010.transitionProbs
                                    else
                                      let #var"250" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 321:16-321:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x452.
                                           map
                                             (lam x453.
                                                p_pure x453)
                                             x452)
                                        (exit 1))
                               with
                                 (st299, x454)
                               in
                               match
                                 p_map
                                   st299
                                   (lam x455.
                                      lam x456.
                                        mkCategorical (get x455 x456))
                                   x454
                               with
                                 (st300, x457)
                               in
                               match
                                 p_map
                                   st300
                                   (lam x458.
                                      subi (addi x458 1) 1)
                                   currentState1
                               with
                                 (st301, x459)
                               in
                               match p_apply st301 x457 x459 with (st302, x460)
                               in
                               match p_assume (join ["state: ", int2string nodeLabel1, " ", int2string host1]) st302 (hrmStoreBranchState nodeLabel1 host1) x460 with (st303, nextState12)
                               in
                               match
                                 p_traverseSeq
                                   st303
                                   (lam st304.
                                      lam x461.
                                        (st304, x461))
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x3911
                                    then
                                      x3911.totalRates
                                    else
                                      let #var"251" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 325:20-325:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x462.
                                           p_pure x462)
                                        (exit 1))
                               with
                                 (st305, x463)
                               in
                               match
                                 p_map
                                   st305
                                   (lam x464.
                                      lam x465.
                                        mkExponential
                                          (addf
                                             (addf (get x464 x465) (mulf (int2float host1) 0.))
                                             (mulf (int2float nodeLabel1) 0.)))
                                   x463
                               with
                                 (st306, x466)
                               in
                               match
                                 p_map
                                   st306
                                   (lam x467.
                                      subi (addi x467 1) 1)
                                   nextState12
                               with
                                 (st307, x468)
                               in
                               match p_apply st307 x466 x468 with (st308, x469)
                               in
                               match p_assume (join ["time: ", int2string nodeLabel1, " ", int2string host1]) st308 (hrmStoreBranchTime nodeLabel1 host1) x469 with (st309, x470)
                               in
                               match
                                 p_map
                                   st309
                                   (lam x471.
                                      subf x443 x471)
                                   x470
                               with
                                 (st310, x472)
                               in
                               match
                                 sampleHostHistoryRec1
                                   st310
                                   nextState12
                                   finalState12
                                   x472
                                   finalAge21
                                   host1
                                   nodeLabel1
                                   embeddedQMatrix12
                               with
                                 (st311, restOfHistory1)
                               in
                               match
                                 p_map
                                   st311
                                   (lam x473.
                                      match x473 with Bridge1 x3711
                                      then
                                        x3711.success
                                      else
                                        let #var"252" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 343:18-343:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st312, x474)
                               in
                               match
                                 p_map
                                   st312
                                   (lam x475.
                                      match x475 with Bridge1 x3811
                                      then
                                        x3811.events
                                      else
                                        let #var"253" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 341:10-341:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st313, x476)
                               in
                               match
                                 cons11
                                   st313
                                   (Event1
                                      { host = host1,
                                        toState = nextState12,
                                        eventTime = x443,
                                        fromState = currentState1 })
                                   x476
                               with
                                 (st314, x477)
                               in
                               (st314, Bridge1
                                 { success = x474, events = x477 })
                             with
                               (st315, x478)
                             in
                             match x478 with Bridge1 x479
                             in
                             match x479 with {success = x480}
                             in
                             match
                               p_map
                                 st315
                                 (lam x481.
                                    lam x482.
                                      Bridge1
                                        { success = x481, events = x482 })
                                 x480
                             with
                               (st316, x483)
                             in
                             match x479 with {events = x484}
                             in
                             p_apply st316 x483 x484)
                        currentAge1
  in
  let anon19 = lam x896.
      addi x896 1 in
  recursive
    let rec36 =
      lam i16.
        lam acc17.
          match geqi i16 0 with true
          then
            rec36 (subi i16 1) (cons (anon19 i16) acc17)
          else
            acc17
  in
  let create12 =
    lam l61.
      let i19 = subi l61 1 in
      match geqi i19 0 with true
      then
        rec36 (subi i19 1) (cons (anon19 i19) "")
      else
        ""
  in
  let anon20 =
    lam st557.
      lam startRep1.
        lam finalRep12.
          lam startAge1.
            lam finalAge33.
              lam nodeLabel12.
                lam modelParams31.
                  lam x876.
                    let startState1 = get startRep1 (subi x876 1) in
                    let embeddedQMatrix51 =
                      match modelParams31 with ModelParams1 x1052
                      then
                        x1052.embeddedQMatrix
                      else
                        let #var"2118" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 199:4-199:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st557
                        (lam st558.
                           lam x877.
                             (st558, x877))
                        (match embeddedQMatrix51 with EmbeddedMarkovChainMatrix1 x1092
                         then
                           x1092.totalRates
                         else
                           let #var"2115" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 290:18-290:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x878.
                                p_pure x878)
                             (exit 1))
                    with
                      (st559, x879)
                    in
                    match
                      p_map
                        st559
                        (lam x880.
                           lam x882.
                             mkExponential
                               (addf
                                  (addf (get x880 x882) (mulf (int2float x876) 0.))
                                  (mulf (int2float nodeLabel12) 0.)))
                        x879
                    with
                      (st560, x883)
                    in
                    match
                      p_map
                        st560
                        (lam x884.
                           subi (addi x884 1) 1)
                        startState1
                    with
                      (st561, x885)
                    in
                    match p_apply st561 x883 x885 with (st562, x886)
                    in
                    match p_assume (join ["time: ", int2string nodeLabel12, " ", int2string x876]) st562 (hrmStoreBranchTime nodeLabel12 x876) x886 with (st563, x887)
                    in
                    match
                      p_map
                        st563
                        (lam x888.
                           subf startAge1 x888)
                        x887
                    with
                      (st564, x889)
                    in
                    match
                      sampleHostHistoryRec
                        st564
                        startState1
                        (get finalRep12 (subi x876 1))
                        x889
                        finalAge33
                        x876
                        nodeLabel12
                        embeddedQMatrix51
                    with
                      (st565, bridge1)
                    in
                    match
                      p_map
                        st565
                        (lam x890.
                           match x890 with Bridge1 x1082
                           then
                             x1082.success
                           else
                             let #var"2116" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 302:19-302:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge1
                    with
                      (st566, x892)
                    in
                    match bool2real st566 x892 with (st567, x893)
                    in
                    let st568 =
                      p_weight
                        st567
                        (hrmStoreBridgeSuppWeight nodeLabel12 x876)
                        (lam x895.
                           externalLog
                             (addf
                                (addf x895 (mulf (int2float x876) 0.))
                                (mulf (int2float nodeLabel12) 0.)))
                        x893
                    in
                    let foo51 = {} in
                    p_map
                      st568
                      (lam x894.
                         match x894 with Bridge1 x1072
                         then
                           x1072.events
                         else
                           let #var"2117" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 303:9-303:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge1
  in
  let anon21 =
    lam st545.
      lam startRep.
        lam finalRep11.
          lam startAge.
            lam finalAge32.
              lam nodeLabel11.
                lam modelParams3.
                  lam x858.
                    let startState = get startRep (subi x858 1) in
                    let embeddedQMatrix5 =
                      match modelParams3 with ModelParams1 x1051
                      then
                        x1051.embeddedQMatrix
                      else
                        let #var"2114" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 199:4-199:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st545
                        (lam st546.
                           lam x859.
                             (st546, x859))
                        (match embeddedQMatrix5 with EmbeddedMarkovChainMatrix1 x1091
                         then
                           x1091.totalRates
                         else
                           let #var"2111" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 290:18-290:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x860.
                                p_pure x860)
                             (exit 1))
                    with
                      (st547, x861)
                    in
                    match
                      p_map
                        st547
                        (lam x862.
                           lam x863.
                             mkExponential
                               (addf
                                  (addf (get x862 x863) (mulf (int2float x858) 0.))
                                  (mulf (int2float nodeLabel11) 0.)))
                        x861
                    with
                      (st548, x864)
                    in
                    match
                      p_map
                        st548
                        (lam x865.
                           subi (addi x865 1) 1)
                        startState
                    with
                      (st549, x866)
                    in
                    match p_apply st549 x864 x866 with (st550, x867)
                    in
                    match p_assume (join ["time: ", int2string nodeLabel11, " ", int2string x858]) st550 (hrmStoreBranchTime nodeLabel11 x858) x867 with (st551, x868)
                    in
                    match
                      p_map
                        st551
                        (lam x869.
                           subf startAge x869)
                        x868
                    with
                      (st552, x870)
                    in
                    match
                      sampleHostHistoryRec1
                        st552
                        startState
                        (get finalRep11 (subi x858 1))
                        x870
                        finalAge32
                        x858
                        nodeLabel11
                        embeddedQMatrix5
                    with
                      (st553, bridge)
                    in
                    match
                      p_map
                        st553
                        (lam x871.
                           match x871 with Bridge1 x1081
                           then
                             x1081.success
                           else
                             let #var"2112" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 302:19-302:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge
                    with
                      (st554, x872)
                    in
                    match bool2real st554 x872 with (st555, x873)
                    in
                    let st556 =
                      p_weight
                        st555
                        (hrmStoreBridgeSuppWeight nodeLabel11 x858)
                        (lam x875.
                           externalLog
                             (addf
                                (addf x875 (mulf (int2float x858) 0.))
                                (mulf (int2float nodeLabel11) 0.)))
                        x873
                    in
                    let foo5 = {} in
                    p_map
                      st556
                      (lam x874.
                         match x874 with Bridge1 x1071
                         then
                           x1071.events
                         else
                           let #var"2113" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 303:9-303:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge
  in
  recursive
    let rec10 =
      lam st317.
        lam c34.
          lam c35.
            lam c36.
              lam c37.
                lam c38.
                  lam c39.
                    lam s9.
                      match s9 with [ _,
                          _ ] ++ _
                      then
                        match anon20 st317 c34 c35 c36 c37 c38 c39 (get s9 0) with (st318, x485)
                        in
                        match splitAt s9 1 with {#label"1" = x486}
                        in
                        match rec10 st318 c34 c35 c36 c37 c38 c39 x486 with (st319, x487)
                        in
                        (st319, cons x485 x487)
                      else match s9 with [ e11 ]
                      then
                        match splitAt s9 1 with {#label"1" = x488}
                        in
                        let slice10 = x488 in
                        match anon20 st317 c34 c35 c36 c37 c38 c39 e11 with (st320, x489)
                        in
                        (st320, [ x489 ])
                      else match s9 with ""
                      in
                      (st317, "")
    let rec13 =
      lam st321.
        lam c40.
          lam c41.
            lam c42.
              lam c43.
                lam c44.
                  lam c45.
                    lam s10.
                      match s10 with [ _,
                          _ ] ++ _
                      then
                        match
                          anon21 st321 c40 c41 c42 c43 c44 c45 (get s10 0)
                        with
                          (st322, x490)
                        in
                        match splitAt s10 1 with {#label"1" = x491}
                        in
                        match rec13 st322 c40 c41 c42 c43 c44 c45 x491 with (st323, x492)
                        in
                        (st323, cons x490 x492)
                      else match s10 with [ e12 ]
                      then
                        match splitAt s10 1 with {#label"1" = x493}
                        in
                        let slice11 = x493 in
                        match anon21 st321 c40 c41 c42 c43 c44 c45 e12 with (st324, x494)
                        in
                        (st324, [ x494 ])
                      else match s10 with ""
                      in
                      (st321, "")
  in
  let anon22 =
    lam h2.
      lam x857.
        lti
          (match
             isNaN1
               (match h2 with Event1 x1101
                then
                  x1101.eventTime
                else
                  let #var"2107" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 239:12-239:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             negi 1
           else match
             isNaN1
               (match x857 with Event1 x1141
                then
                  x1141.eventTime
                else
                  let #var"2108" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 242:12-242:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             1
           else match
             geqf
               (match h2 with Event1 x1151
                then
                  x1151.eventTime
                else
                  let #var"2109" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 245:6-245:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
                  in
                  exit 1)
               (match x857 with Event1 x1161
                then
                  x1161.eventTime
                else
                  let #var"2110" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 245:25-245:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
                  in
                  exit 1)
           with
             true
           then
             1
           else
             negi 1)
          0
  in
  recursive
    let work11 =
      lam c46.
        lam l.
          lam r.
            lam seq1.
              match seq1 with [ _ ] ++ _
              then
                let s41 = get seq1 0 in
                match splitAt seq1 1 with {#label"1" = x495}
                in
                let seq2 = x495 in
                match anon22 c46 s41 with true
                then
                  work11 c46 (cons s41 l) r seq2
                else
                  work11 c46 l (cons s41 r) seq2
              else match seq1 with ""
              in
              (l, r)
    let work12 =
      lam c47.
        lam l1.
          lam r1.
            lam seq11.
              match seq11 with [ _ ] ++ _
              then
                let s42 = get seq11 0 in
                match splitAt seq11 1 with {#label"1" = x496}
                in
                let seq21 = x496 in
                match anon22 c47 s42 with true
                then
                  work12 c47 (cons s42 l1) r1 seq21
                else
                  work11 c47 l1 (cons s42 r1) seq21
              else match seq11 with ""
              in
              (l1, r1)
    let work13 =
      lam c48.
        lam l2.
          lam r2.
            lam seq12.
              match seq12 with [ _ ] ++ _
              then
                let s43 = get seq12 0 in
                match splitAt seq12 1 with {#label"1" = x497}
                in
                let seq22 = x497 in
                match anon22 c48 s43 with true
                then
                  work11 c48 (cons s43 l2) r2 seq22
                else
                  work13 c48 l2 (cons s43 r2) seq22
              else match seq12 with ""
              in
              (l2, r2)
    let work14 =
      lam c49.
        lam l3.
          lam r3.
            lam seq13.
              match seq13 with [ _ ] ++ _
              then
                let s44 = get seq13 0 in
                match splitAt seq13 1 with {#label"1" = x498}
                in
                let seq23 = x498 in
                match anon22 c49 s44 with true
                then
                  work12 c49 (cons s44 l3) r3 seq23
                else
                  work13 c49 l3 (cons s44 r3) seq23
              else match seq13 with ""
              in
              (l3, r3)
  in
  recursive
    let quickSort =
      lam seq3.
        match null seq3 with true
        then
          seq3
        else
          let h = head seq3 in
          let lr = work14 h "" "" (reverse (tail seq3)) in
          match lr with (#var"X4",)
          in
          match lr with {#label"1" = #var"X5"}
          in
          concat (quickSort #var"X4") (cons h (quickSort #var"X5"))
    let quickSort1 =
      lam st325.
        lam seq31.
          p_map
            st325
            (lam x499.
               match null x499 with true
               then
                 x499
               else
                 let h1 = head x499 in
                 let lr1 = work14 h1 "" "" (reverse (tail x499)) in
                 match lr1 with (#var"X6",)
                 in
                 match lr1 with {#label"1" = #var"X7"}
                 in
                 concat (quickSort #var"X6") (cons h1 (quickSort #var"X7")))
            seq31
  in
  recursive
    let rec211 =
      lam st326.
        lam c50.
          lam c51.
            lam c52.
              lam c53.
                lam c54.
                  lam c55.
                    lam acc18.
                      lam s212.
                        match s212 with [ _ ] ++ _
                        then
                          let x500 = get s212 0 in
                          match
                            p_map
                              st326
                              (lam x501.
                                 lam x502.
                                   addf x501 x502)
                              acc18
                          with
                            (st327, x503)
                          in
                          match
                            hostIndepLikelihood
                              st327
                              1
                              (get c50 (subi x500 1))
                              (get c51 (subi x500 1))
                              c52
                              c53
                              (get c55 (subi x500 1))
                              (match c54 with ModelParams1 x1201
                               then
                                 x1201.embeddedQMatrix
                               else
                                 let #var"254" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st328, x504)
                          in
                          match p_apply st328 x503 x504 with (st329, x505)
                          in
                          match splitAt s212 1 with {#label"1" = x506}
                          in
                          rec211 st329 c50 c51 c52 c53 c54 c55 x505 x506
                        else match s212 with ""
                        in
                        (st326, acc18)
    let rec212 =
      lam st330.
        lam c56.
          lam c57.
            lam c58.
              lam c59.
                lam c60.
                  lam c61.
                    lam acc19.
                      lam s213.
                        match s213 with [ _ ] ++ _
                        then
                          let x507 = get s213 0 in
                          match
                            p_map
                              st330
                              (lam x508.
                                 lam x509.
                                   addf x508 x509)
                              acc19
                          with
                            (st331, x510)
                          in
                          match
                            hostIndepLikelihood2
                              st331
                              1
                              (get c56 (subi x507 1))
                              (get c57 (subi x507 1))
                              c58
                              c59
                              (get c61 (subi x507 1))
                              (match c60 with ModelParams1 x1202
                               then
                                 x1202.embeddedQMatrix
                               else
                                 let #var"255" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st332, x511)
                          in
                          match p_apply st332 x510 x511 with (st333, x512)
                          in
                          match splitAt s213 1 with {#label"1" = x513}
                          in
                          rec212 st333 c56 c57 c58 c59 c60 c61 x512 x513
                        else match s213 with ""
                        in
                        (st330, acc19)
  in
  let anon23 = lam x856.
      addi x856 1 in
  recursive
    let rec37 =
      lam i17.
        lam acc110.
          match geqi i17 0 with true
          then
            rec37 (subi i17 1) (cons (anon23 i17) acc110)
          else
            acc110
  in
  let create13 =
    lam l6.
      let i18 = subi l6 1 in
      match geqi i18 0 with true
      then
        rec37 (subi i18 1) (cons (anon23 i18) "")
      else
        ""
  in
  recursive
    let rec213 =
      lam st334.
        lam acc20.
          lam s214.
            match s214 with [ _ ] ++ _
            then
              match
                p_map
                  st334
                  (lam x514.
                     lam x515.
                       addf x514 x515)
                  acc20
              with
                (st335, x516)
              in
              match p_apply st335 x516 (get s214 0) with (st336, x517)
              in
              match splitAt s214 1 with {#label"1" = x518}
              in
              rec213 st336 x517 x518
            else match s214 with ""
            in
            (st334, acc20)
  in
  let fold =
    lam st543.
      lam init1.
        lam seq5.
          match seq5 with [ _ ] ++ _
          then
            match
              p_map
                st543
                (lam x853.
                   addf init1 x853)
                (get seq5 0)
            with
              (st544, x854)
            in
            match splitAt seq5 1 with {#label"1" = x855}
            in
            rec213 st544 x854 x855
          else match seq5 with ""
          in
          (st543, p_pure init1)
  in
  recursive
    let rec214 =
      lam st337.
        lam c62.
          lam acc23.
            lam s215.
              match s215 with [ _ ] ++ _
              then
                match acc23 with (field2, field3)
                in
                match
                  match field3 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st337
                        (lam x519.
                           addi x519 1)
                        (get field3 0)
                    with
                      (st338, x520)
                    in
                    match mtxGet1 st338 x520 (addi (get s215 0) 1) c62 with (st339, x521)
                    in
                    match log11 st339 x521 with (st340, x522)
                    in
                    match splitAt field3 1 with {#label"1" = x523}
                    in
                    (st340, (snoc field2 x522, x523))
                  else
                    let x524 = error "foldl2: Cannot happen!" in
                    match x524 with (x525,)
                    in
                    match x524 with {#label"1" = x526}
                    in
                    (st337, (map (lam x527.
                         p_pure x527) x525, map (lam x528.
                         p_pure x528) x526))
                with
                  (st341, x529)
                in
                match splitAt s215 1 with {#label"1" = x530}
                in
                rec214 st341 c62 x529 x530
              else match s215 with ""
              in
              (st337, acc23)
    let rec215 =
      lam st342.
        lam c63.
          lam acc24.
            lam s216.
              match s216 with [ _ ] ++ _
              then
                match acc24 with (field4, field5)
                in
                match
                  match field5 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st342
                        (lam x531.
                           addi x531 1)
                        (get field5 0)
                    with
                      (st343, x532)
                    in
                    match
                      p_map
                        st343
                        (lam x533.
                           addi x533 1)
                        (get s216 0)
                    with
                      (st344, x534)
                    in
                    match mtxGet2 st344 x532 x534 c63 with (st345, x535)
                    in
                    match log11 st345 x535 with (st346, x536)
                    in
                    match splitAt field5 1 with {#label"1" = x537}
                    in
                    (st346, (snoc field4 x536, x537))
                  else
                    let x538 = error "foldl2: Cannot happen!" in
                    match x538 with (x539,)
                    in
                    match x538 with {#label"1" = x540}
                    in
                    (st342, (map (lam x541.
                         p_pure x541) x539, map (lam x542.
                         p_pure x542) x540))
                with
                  (st347, x543)
                in
                match splitAt s216 1 with {#label"1" = x544}
                in
                rec215 st347 c63 x543 x544
              else match s216 with ""
              in
              (st342, acc24)
  in
  recursive
    let rec216 =
      lam st348.
        lam c64.
          lam acc25.
            lam s217.
              match s217 with [ _ ] ++ _
              then
                match acc25 with (field6, field7)
                in
                match
                  match field7 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st348
                        (lam x545.
                           addi x545 1)
                        (get s217 0)
                    with
                      (st349, x546)
                    in
                    match mtxGet1 st349 x546 (addi (get field7 0) 1) c64 with (st350, x547)
                    in
                    match log11 st350 x547 with (st351, x548)
                    in
                    match splitAt field7 1 with {#label"1" = x549}
                    in
                    (st351, (snoc field6 x548, x549))
                  else
                    let x550 = error "foldl2: Cannot happen!" in
                    match x550 with (x551,)
                    in
                    match x550 with {#label"1" = x552}
                    in
                    (st348, (map (lam x553.
                         p_pure x553) x551, x552))
                with
                  (st352, x554)
                in
                match splitAt s217 1 with {#label"1" = x555}
                in
                rec216 st352 c64 x554 x555
              else match s217 with ""
              in
              (st348, acc25)
    let rec217 =
      lam st353.
        lam c65.
          lam acc26.
            lam s218.
              match s218 with [ _ ] ++ _
              then
                match acc26 with (field8, field9)
                in
                match
                  match field9 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st353
                        (lam x556.
                           addi x556 1)
                        (get s218 0)
                    with
                      (st354, x557)
                    in
                    match
                      p_map
                        st354
                        (lam x558.
                           addi x558 1)
                        (get field9 0)
                    with
                      (st355, x559)
                    in
                    match mtxGet2 st355 x557 x559 c65 with (st356, x560)
                    in
                    match log11 st356 x560 with (st357, x561)
                    in
                    match splitAt field9 1 with {#label"1" = x562}
                    in
                    (st357, (snoc field8 x561, x562))
                  else
                    let x563 = error "foldl2: Cannot happen!" in
                    match x563 with (x564,)
                    in
                    match x563 with {#label"1" = x565}
                    in
                    (st353, (map (lam x566.
                         p_pure x566) x564, map (lam x567.
                         p_pure x567) x565))
                with
                  (st358, x568)
                in
                match splitAt s218 1 with {#label"1" = x569}
                in
                rec217 st358 c65 x568 x569
              else match s218 with ""
              in
              (st353, acc26)
  in
  recursive
    let any =
      lam st359.
        lam seq.
          match null seq with true
          then
            (st359, p_pure false)
          else match
            p_map st359 (lam x570.
                 eqi x570 2) (head seq)
          with
            (st360, x571)
          in
          p_bind
            st360
            hrmStoreSubmodel
            (hrmInit {})
            (lam st361.
               lam x572.
                 match x572 with true
                 then
                   (st361, p_pure true)
                 else
                   any st361 (tail seq))
            x571
  in
  let any1 = lam st542.
      lam l21.
        any st542 l21 in
  recursive
    let sampleTreeHistory =
      lam st362.
        lam tree2.
          lam nHosts.
            lam preorderMsg.
              lam parentRep.
                lam parentAge.
                  lam modelParams11.
                    lam branchKernel.
                      match
                        match tree2 with MsgLeaf _
                        then
                          true
                        else
                          false
                      with
                        true
                      then
                        let rep1 =
                          match tree2 with MsgLeaf x5410
                          then
                            x5410.interactions
                          else
                            let #var"269" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 113:14-113:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
                            in
                            exit 1
                        in
                        let finalAge3 =
                          match tree2 with MsgLeaf carried32
                          then
                            carried32.age
                          else match tree2 with MsgNode carried33
                          then
                            carried33.age
                          else
                            let #var"268" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 119:6-119:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                            in
                            exit 1
                        in
                        match
                          rec10
                            st362
                            parentRep
                            rep1
                            parentAge
                            finalAge3
                            (match tree2 with MsgLeaf carried24
                             then
                               carried24.label
                             else match tree2 with MsgNode carried25
                             then
                               carried25.label
                             else
                               let #var"256" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 121:6-121:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create12 (addi (subi nHosts 1) 1))
                        with
                          (st363, unorderedBranch)
                        in
                        match paste01 st363 unorderedBranch with (st364, x573)
                        in
                        match quickSort1 st364 x573 with (st365, orderedEvents)
                        in
                        match length13 st365 orderedEvents with (st366, nEvents4)
                        in
                        match
                          allTimesValidBranch st366 parentRep orderedEvents 1 nEvents4 nHosts
                        with
                          (st367, x574)
                        in
                        match
                          p_bind
                            st367
                            hrmStoreSubmodel
                            (hrmInit {})
                            (lam st368.
                               lam x575.
                                 match
                                   match x575 with true
                                   then
                                     let s219 = create13 (addi (subi (length11 unorderedBranch) 1) 1)
                                     in
                                     match
                                       match s219 with [ _ ] ++ _
                                       then
                                         let x576 = get s219 0 in
                                         match
                                           hostIndepLikelihood
                                             st368
                                             1
                                             (get parentRep (subi x576 1))
                                             (get rep1 (subi x576 1))
                                             parentAge
                                             finalAge3
                                             (get unorderedBranch (subi x576 1))
                                             (match modelParams11 with ModelParams1 x1203
                                              then
                                                x1203.embeddedQMatrix
                                              else
                                                let #var"257" =
                                                  print
                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                                in
                                                exit 1)
                                         with
                                           (st369, x577)
                                         in
                                         match
                                           p_map
                                             st369
                                             (lam x578.
                                                addf 0. x578)
                                             x577
                                         with
                                           (st370, x579)
                                         in
                                         match splitAt s219 1 with {#label"1" = x580}
                                         in
                                         rec211
                                           st370
                                           parentRep
                                           rep1
                                           parentAge
                                           finalAge3
                                           modelParams11
                                           unorderedBranch
                                           x579
                                           x580
                                       else match s219 with ""
                                       in
                                       (st368, p_pure 0.)
                                     with
                                       (st371, x581)
                                     in
                                     match
                                       p_map
                                         st371
                                         (lam x582.
                                            lam x583.
                                              subf x582 x583)
                                         x581
                                     with
                                       (st372, x584)
                                     in
                                     match
                                       match geqi (length parentRep) (length rep1) with true
                                       then
                                         let acc27 = ("", parentRep) in
                                         match
                                           match rep1 with [ _ ] ++ _
                                           then
                                             match acc27 with (field10, field11)
                                             in
                                             match
                                               match field11 with [ _ ] ++ _
                                               then
                                                 match
                                                   p_map
                                                     st372
                                                     (lam x585.
                                                        addi x585 1)
                                                     (get field11 0)
                                                 with
                                                   (st373, x586)
                                                 in
                                                 match
                                                   mtxGet1 st373 x586 (addi (get rep1 0) 1) branchKernel
                                                 with
                                                   (st374, x587)
                                                 in
                                                 match log11 st374 x587 with (st375, x588)
                                                 in
                                                 match splitAt field11 1 with {#label"1" = x589}
                                                 in
                                                 (st375, (snoc field10 x588, x589))
                                               else
                                                 let x590 = error "foldl2: Cannot happen!" in
                                                 match x590 with (x591,)
                                                 in
                                                 match x590 with {#label"1" = x592}
                                                 in
                                                 (st372, (map
                                                   (lam x593.
                                                      p_pure x593)
                                                   x591, map
                                                   (lam x594.
                                                      p_pure x594)
                                                   x592))
                                             with
                                               (st376, x595)
                                             in
                                             match splitAt rep1 1 with {#label"1" = x596}
                                             in
                                             rec214 st376 branchKernel x595 x596
                                           else match rep1 with ""
                                           in
                                           (st372, acc27)
                                         with
                                           (st377, x597)
                                         in
                                         match x597 with (field12, field13)
                                         in
                                         (st377, field12)
                                       else
                                         let acc28 = ("", rep1) in
                                         match
                                           match parentRep with [ _ ] ++ _
                                           then
                                             match acc28 with (field14, field15)
                                             in
                                             match
                                               match field15 with [ _ ] ++ _
                                               then
                                                 match
                                                   p_map
                                                     st372
                                                     (lam x598.
                                                        addi x598 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st378, x599)
                                                 in
                                                 match
                                                   mtxGet1 st378 x599 (addi (get field15 0) 1) branchKernel
                                                 with
                                                   (st379, x600)
                                                 in
                                                 match log11 st379 x600 with (st380, x601)
                                                 in
                                                 match splitAt field15 1 with {#label"1" = x602}
                                                 in
                                                 (st380, (snoc field14 x601, x602))
                                               else
                                                 let x603 = error "foldl2: Cannot happen!" in
                                                 match x603 with (x604,)
                                                 in
                                                 match x603 with {#label"1" = x605}
                                                 in
                                                 (st372, (map
                                                   (lam x606.
                                                      p_pure x606)
                                                   x604, x605))
                                             with
                                               (st381, x607)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x608}
                                             in
                                             rec216 st381 branchKernel x607 x608
                                           else match parentRep with ""
                                           in
                                           (st372, acc28)
                                         with
                                           (st382, x609)
                                         in
                                         match x609 with (field16, field17)
                                         in
                                         (st382, field16)
                                     with
                                       (st383, x610)
                                     in
                                     match fold st383 0. x610 with (st384, x611)
                                     in
                                     match p_apply st384 x584 x611 with (st385, x612)
                                     in
                                     match
                                       p_bind
                                         st385
                                         hrmStoreSubmodel
                                         (hrmInit {})
                                         (lam st386.
                                            lam x613.
                                              match gti 1 x613 with true
                                              then
                                                match
                                                  getTotalRate st386 parentRep modelParams11 nHosts
                                                with
                                                  (st387, x614)
                                                in
                                                p_map
                                                  st387
                                                  (lam x615.
                                                     mulf (negf (subf parentAge finalAge3)) x615)
                                                  x614
                                              else match
                                                p_map
                                                  st386
                                                  (lam x616.
                                                     get x616 (subi 1 1))
                                                  orderedEvents
                                              with
                                                (st388, nextEvent2)
                                              in
                                              match
                                                p_map
                                                  st388
                                                  (lam x617.
                                                     match x617 with Event1 x3110
                                                     then
                                                       x3110.eventTime
                                                     else
                                                       let #var"258" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st389, newAge2)
                                              in
                                              match
                                                getTotalRate st389 parentRep modelParams11 nHosts
                                              with
                                                (st390, totalLeavingRate12)
                                              in
                                              match
                                                p_map
                                                  st390
                                                  (lam x618.
                                                     match x618 with Event1 x1332
                                                     then
                                                       x1332.host
                                                     else
                                                       let #var"259" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st391, hostIndex12)
                                              in
                                              match
                                                p_map
                                                  st391
                                                  (lam x619.
                                                     lam x620.
                                                       lam st392.
                                                         match
                                                           gti
                                                             (match x619 with Event1 x1312
                                                              then
                                                                x1312.fromState
                                                              else
                                                                let #var"260" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x620
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st392 parentRep hostIndex12 modelParams11
                                                         else
                                                           getGainRate2 st392 parentRep hostIndex12 modelParams11)
                                                  nextEvent2
                                              with
                                                (st393, x621)
                                              in
                                              match
                                                p_map
                                                  st393
                                                  (lam x622.
                                                     match x622 with Event1 x1322
                                                     then
                                                       x1322.toState
                                                     else
                                                       let #var"261" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st394, x623)
                                              in
                                              match
                                                p_subApply st394 hrmStoreSubmodel (hrmInit {}) x621 x623
                                              with
                                                (st395, x624)
                                              in
                                              match p_join st395 x624 with (st396, x625)
                                              in
                                              match
                                                p_map
                                                  st396
                                                  (lam x626.
                                                     lam x627.
                                                       divf x626 x627)
                                                  x625
                                              with
                                                (st397, x628)
                                              in
                                              match p_apply st397 x628 totalLeavingRate12 with (st398, x629)
                                              in
                                              match log11 st398 x629 with (st399, x630)
                                              in
                                              match
                                                p_map
                                                  st399
                                                  (lam x631.
                                                     lam x632.
                                                       lam x633.
                                                         addf (subf x631 x632) x633)
                                                  x630
                                              with
                                                (st400, x634)
                                              in
                                              match
                                                p_map
                                                  st400
                                                  (lam x635.
                                                     lam x636.
                                                       mulf (subf parentAge x635) x636)
                                                  newAge2
                                              with
                                                (st401, x637)
                                              in
                                              match p_apply st401 x637 totalLeavingRate12 with (st402, x638)
                                              in
                                              match p_apply st402 x634 x638 with (st403, x639)
                                              in
                                              match
                                                updateRepertoire st403 parentRep nextEvent2 nHosts
                                              with
                                                (st404, x640)
                                              in
                                              match
                                                fullModelWeight
                                                  st404
                                                  (addi 1 1)
                                                  x640
                                                  rep1
                                                  newAge2
                                                  finalAge3
                                                  orderedEvents
                                                  x613
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st405, x641)
                                              in
                                              p_apply st405 x639 x641)
                                         nEvents4
                                     with
                                       (st406, x642)
                                     in
                                     (st406, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = x612,
                                         logModelDensity = x642,
                                         success = true })
                                   else
                                     (st368, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = p_pure (log1 0.),
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st407, x643)
                                 in
                                 match x643 with CorrectedBranchSample1 x644
                                 in
                                 match x644 with {history = x645}
                                 in
                                 match
                                   p_map
                                     st407
                                     (lam x646.
                                        lam x647.
                                          lam x648.
                                            match x644 with {success = x649}
                                            in
                                            CorrectedBranchSample1
                                              { history = x646,
                                                logSamplingDensity = x647,
                                                logModelDensity = x648,
                                                success = x649 })
                                     x645
                                 with
                                   (st408, x650)
                                 in
                                 match x644 with {logSamplingDensity = x651}
                                 in
                                 match p_apply st408 x650 x651 with (st409, x652)
                                 in
                                 match x644 with {logModelDensity = x653}
                                 in
                                 p_apply st409 x652 x653)
                            x574
                        with
                          (st410, branchSample)
                        in
                        match
                          p_map
                            st410
                            (lam x654.
                               lam x655.
                                 mulf
                                   (subf
                                      (match x654 with CorrectedBranchSample1 x4610
                                       then
                                         x4610.logModelDensity
                                       else
                                         let #var"262" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 127:15-127:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x655)
                                   (exp1
                                      (mulf
                                         (int2float
                                            (match tree2 with MsgLeaf carried26
                                             then
                                               carried26.label
                                             else match tree2 with MsgNode carried27
                                             then
                                               carried27.label
                                             else
                                               let #var"263" =
                                                 print
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 127:90-127:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1))
                                         0.)))
                            branchSample
                        with
                          (st411, x656)
                        in
                        match
                          p_map
                            st411
                            (lam x657.
                               match x657 with CorrectedBranchSample1 x4710
                               then
                                 x4710.logSamplingDensity
                               else
                                 let #var"264" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 127:46-127:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st412, x658)
                        in
                        match p_apply st412 x656 x658 with (st413, x659)
                        in
                        let nl = (match tree2 with MsgLeaf carried26
                                             then
                                               carried26.label
                                             else match tree2 with MsgNode carried27
                                             then
                                               carried27.label
                                             else
                                               let #var"263" =
                                                 print
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 127:90-127:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1) in
                        let st414 =
                          p_weight
                            st413
                            (hrmStoreLikrWeight nl)
                            (/-temp-/lam x662.
                               x662)
                            x659
                        in
                        let foo = {} in
                        match
                          p_map
                            st414
                            (lam x660.
                               match x660 with CorrectedBranchSample1 x4510
                               then
                                 x4510.history
                               else
                                 let #var"265" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 133:16-133:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st415, x661)
                        in
                        (st415, HistoryLeaf
                          { age =
                              match tree2 with MsgLeaf carried28
                              then
                                carried28.age
                              else match tree2 with MsgNode carried29
                              then
                                carried29.age
                              else
                                let #var"266" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 130:12-130:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
                                in
                                exit 1,
                            label =
                              match tree2 with MsgLeaf carried30
                              then
                                carried30.label
                              else match tree2 with MsgNode carried31
                              then
                                carried31.label
                              else
                                let #var"267" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 131:14-131:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            history = x661,
                            repertoire = rep1 })
                      else match
                        mtxElemMul
                          st362
                          (match tree2 with MsgLeaf carried34
                           then
                             match carried34 with {outMsg = #var"X8"}
                             in
                             p_pure #var"X8"
                           else match tree2 with MsgNode carried35
                           then
                             carried35.outMsg
                           else
                             let #var"270" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 136:34-136:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                             in
                             p_pure (exit 1))
                          preorderMsg
                      with
                        (st416, samplingProb)
                      in
                      match
                        suggestNodeRep
                          st416
                          samplingProb
                          nHosts
                          (match tree2 with MsgLeaf carried36
                           then
                             carried36.label
                           else match tree2 with MsgNode carried37
                           then
                             carried37.label
                           else
                             let #var"271" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 137:51-137:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                             in
                             exit 1)
                      with
                        (st417, rep2)
                      in
                      match any1 st417 rep2 with (st418, x663)
                      in
                      match bool2real st418 x663 with (st419, x664)
                      in
                      let nl = (match tree2 with MsgLeaf carried52
                                         then
                                           carried52.label
                                         else match tree2 with MsgNode carried53
                                         then
                                           carried53.label
                                         else
                                           let #var"293" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 139:43-139:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1) in
                      let st420 =
                        p_weight
                          st419
                          (hrmStoreNodeSuppWeight nl)
                          (lam x770.
                             externalLog
                               (addf
                                  x770
                                  (mulf
                                     (int2float
                                        (match tree2 with MsgLeaf carried52
                                         then
                                           carried52.label
                                         else match tree2 with MsgNode carried53
                                         then
                                           carried53.label
                                         else
                                           let #var"293" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 139:43-139:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1))
                                     0.)))
                          x664
                      in
                      let foo1 = {} in
                      let finalAge31 =
                        match tree2 with MsgLeaf carried50
                        then
                          carried50.age
                        else match tree2 with MsgNode carried51
                        then
                          carried51.age
                        else
                          let #var"292" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 147:6-147:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                          in
                          exit 1
                      in
                      match
                        rec13
                          st420
                          parentRep
                          rep2
                          parentAge
                          finalAge31
                          (match tree2 with MsgLeaf carried38
                           then
                             carried38.label
                           else match tree2 with MsgNode carried39
                           then
                             carried39.label
                           else
                             let #var"272" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 149:6-149:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                             in
                             exit 1)
                          modelParams11
                          (create12 (addi (subi nHosts 1) 1))
                      with
                        (st421, unorderedBranch1)
                      in
                      match paste01 st421 unorderedBranch1 with (st422, x665)
                      in
                      match quickSort1 st422 x665 with (st423, orderedEvents1)
                      in
                      match length13 st423 orderedEvents1 with (st424, nEvents41)
                      in
                      match
                        allTimesValidBranch st424 parentRep orderedEvents1 1 nEvents41 nHosts
                      with
                        (st425, x666)
                      in
                      match
                        p_bind
                          st425
                          hrmStoreSubmodel
                          (hrmInit {})
                          (lam st426.
                             lam x667.
                               match
                                 match x667 with true
                                 then
                                   let s220 = create13 (addi (subi (length11 unorderedBranch1) 1) 1)
                                   in
                                   match
                                     match s220 with [ _ ] ++ _
                                     then
                                       let x668 = get s220 0 in
                                       match
                                         hostIndepLikelihood2
                                           st426
                                           1
                                           (get parentRep (subi x668 1))
                                           (get rep2 (subi x668 1))
                                           parentAge
                                           finalAge31
                                           (get unorderedBranch1 (subi x668 1))
                                           (match modelParams11 with ModelParams1 x1204
                                            then
                                              x1204.embeddedQMatrix
                                            else
                                              let #var"273" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                              in
                                              exit 1)
                                       with
                                         (st427, x669)
                                       in
                                       match
                                         p_map
                                           st427
                                           (lam x670.
                                              addf 0. x670)
                                           x669
                                       with
                                         (st428, x671)
                                       in
                                       match splitAt s220 1 with {#label"1" = x672}
                                       in
                                       rec212
                                         st428
                                         parentRep
                                         rep2
                                         parentAge
                                         finalAge31
                                         modelParams11
                                         unorderedBranch1
                                         x671
                                         x672
                                     else match s220 with ""
                                     in
                                     (st426, p_pure 0.)
                                   with
                                     (st429, x673)
                                   in
                                   match
                                     p_map
                                       st429
                                       (lam x674.
                                          lam x675.
                                            subf x674 x675)
                                       x673
                                   with
                                     (st430, x676)
                                   in
                                   match
                                     match geqi (length parentRep) (length rep2) with true
                                     then
                                       let acc29 = ("", parentRep) in
                                       match
                                         match rep2 with [ _ ] ++ _
                                         then
                                           match acc29 with (field18, field19)
                                           in
                                           match
                                             match field19 with [ _ ] ++ _
                                             then
                                               match
                                                 p_map
                                                   st430
                                                   (lam x677.
                                                      addi x677 1)
                                                   (get field19 0)
                                               with
                                                 (st431, x678)
                                               in
                                               match
                                                 p_map
                                                   st431
                                                   (lam x679.
                                                      addi x679 1)
                                                   (get rep2 0)
                                               with
                                                 (st432, x680)
                                               in
                                               match mtxGet2 st432 x678 x680 branchKernel with (st433, x681)
                                               in
                                               match log11 st433 x681 with (st434, x682)
                                               in
                                               match splitAt field19 1 with {#label"1" = x683}
                                               in
                                               (st434, (snoc field18 x682, x683))
                                             else
                                               let x684 = error "foldl2: Cannot happen!" in
                                               match x684 with (x685,)
                                               in
                                               match x684 with {#label"1" = x686}
                                               in
                                               (st430, (map
                                                 (lam x687.
                                                    p_pure x687)
                                                 x685, map
                                                 (lam x688.
                                                    p_pure x688)
                                                 x686))
                                           with
                                             (st435, x689)
                                           in
                                           match splitAt rep2 1 with {#label"1" = x690}
                                           in
                                           rec215 st435 branchKernel x689 x690
                                         else match rep2 with ""
                                         in
                                         (st430, acc29)
                                       with
                                         (st436, x691)
                                       in
                                       match x691 with (field20, field21)
                                       in
                                       (st436, field20)
                                     else
                                       let acc30 = ("", rep2) in
                                       match
                                         match parentRep with [ _ ] ++ _
                                         then
                                           match acc30 with (field22, field23)
                                           in
                                           match
                                             match field23 with [ _ ] ++ _
                                             then
                                               match
                                                 p_map
                                                   st430
                                                   (lam x692.
                                                      addi x692 1)
                                                   (get parentRep 0)
                                               with
                                                 (st437, x693)
                                               in
                                               match
                                                 p_map
                                                   st437
                                                   (lam x694.
                                                      addi x694 1)
                                                   (get field23 0)
                                               with
                                                 (st438, x695)
                                               in
                                               match mtxGet2 st438 x693 x695 branchKernel with (st439, x696)
                                               in
                                               match log11 st439 x696 with (st440, x697)
                                               in
                                               match splitAt field23 1 with {#label"1" = x698}
                                               in
                                               (st440, (snoc field22 x697, x698))
                                             else
                                               let x699 = error "foldl2: Cannot happen!" in
                                               match x699 with (x700,)
                                               in
                                               match x699 with {#label"1" = x701}
                                               in
                                               (st430, (map
                                                 (lam x702.
                                                    p_pure x702)
                                                 x700, map
                                                 (lam x703.
                                                    p_pure x703)
                                                 x701))
                                           with
                                             (st441, x704)
                                           in
                                           match splitAt parentRep 1 with {#label"1" = x705}
                                           in
                                           rec217 st441 branchKernel x704 x705
                                         else match parentRep with ""
                                         in
                                         (st430, acc30)
                                       with
                                         (st442, x706)
                                       in
                                       match x706 with (field24, field25)
                                       in
                                       (st442, field24)
                                   with
                                     (st443, x707)
                                   in
                                   match fold st443 0. x707 with (st444, x708)
                                   in
                                   match p_apply st444 x676 x708 with (st445, x709)
                                   in
                                   match
                                     p_bind
                                       st445
                                       hrmStoreSubmodel
                                       (hrmInit {})
                                       (lam st446.
                                          lam x710.
                                            match gti 1 x710 with true
                                            then
                                              match
                                                getTotalRate st446 parentRep modelParams11 nHosts
                                              with
                                                (st447, x711)
                                              in
                                              p_map
                                                st447
                                                (lam x712.
                                                   mulf (negf (subf parentAge finalAge31)) x712)
                                                x711
                                            else match
                                              p_map
                                                st446
                                                (lam x713.
                                                   get x713 (subi 1 1))
                                                orderedEvents1
                                            with
                                              (st448, nextEvent3)
                                            in
                                            match
                                              p_map
                                                st448
                                                (lam x714.
                                                   match x714 with Event1 x3111
                                                   then
                                                     x3111.eventTime
                                                   else
                                                     let #var"274" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st449, newAge3)
                                            in
                                            match
                                              getTotalRate st449 parentRep modelParams11 nHosts
                                            with
                                              (st450, totalLeavingRate13)
                                            in
                                            match
                                              p_map
                                                st450
                                                (lam x715.
                                                   match x715 with Event1 x1333
                                                   then
                                                     x1333.host
                                                   else
                                                     let #var"275" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st451, hostIndex13)
                                            in
                                            match
                                              p_map
                                                st451
                                                (lam x716.
                                                   lam x717.
                                                     lam st452.
                                                       match
                                                         gti
                                                           (match x716 with Event1 x1313
                                                            then
                                                              x1313.fromState
                                                            else
                                                              let #var"276" =
                                                                print
                                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                              in
                                                              exit 1)
                                                           x717
                                                       with
                                                         true
                                                       then
                                                         getLossRate2 st452 parentRep hostIndex13 modelParams11
                                                       else
                                                         getGainRate2 st452 parentRep hostIndex13 modelParams11)
                                                nextEvent3
                                            with
                                              (st453, x718)
                                            in
                                            match
                                              p_map
                                                st453
                                                (lam x719.
                                                   match x719 with Event1 x1323
                                                   then
                                                     x1323.toState
                                                   else
                                                     let #var"277" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st454, x720)
                                            in
                                            match
                                              p_subApply st454 hrmStoreSubmodel (hrmInit {}) x718 x720
                                            with
                                              (st455, x721)
                                            in
                                            match p_join st455 x721 with (st456, x722)
                                            in
                                            match
                                              p_map
                                                st456
                                                (lam x723.
                                                   lam x724.
                                                     divf x723 x724)
                                                x722
                                            with
                                              (st457, x725)
                                            in
                                            match p_apply st457 x725 totalLeavingRate13 with (st458, x726)
                                            in
                                            match log11 st458 x726 with (st459, x727)
                                            in
                                            match
                                              p_map
                                                st459
                                                (lam x728.
                                                   lam x729.
                                                     lam x730.
                                                       addf (subf x728 x729) x730)
                                                x727
                                            with
                                              (st460, x731)
                                            in
                                            match
                                              p_map
                                                st460
                                                (lam x732.
                                                   lam x733.
                                                     mulf (subf parentAge x732) x733)
                                                newAge3
                                            with
                                              (st461, x734)
                                            in
                                            match p_apply st461 x734 totalLeavingRate13 with (st462, x735)
                                            in
                                            match p_apply st462 x731 x735 with (st463, x736)
                                            in
                                            match
                                              updateRepertoire st463 parentRep nextEvent3 nHosts
                                            with
                                              (st464, x737)
                                            in
                                            match
                                              fullModelWeight1
                                                st464
                                                (addi 1 1)
                                                x737
                                                rep2
                                                newAge3
                                                finalAge31
                                                orderedEvents1
                                                x710
                                                nHosts
                                                modelParams11
                                            with
                                              (st465, x738)
                                            in
                                            p_apply st465 x736 x738)
                                       nEvents41
                                   with
                                     (st466, x739)
                                   in
                                   (st466, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = x709,
                                       logModelDensity = x739,
                                       success = true })
                                 else
                                   (st426, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = p_pure (log1 0.),
                                       logModelDensity = p_pure (log1 0.),
                                       success = false })
                               with
                                 (st467, x740)
                               in
                               match x740 with CorrectedBranchSample1 x741
                               in
                               match x741 with {history = x742}
                               in
                               match
                                 p_map
                                   st467
                                   (lam x743.
                                      lam x744.
                                        lam x745.
                                          match x741 with {success = x746}
                                          in
                                          CorrectedBranchSample1
                                            { history = x743,
                                              logSamplingDensity = x744,
                                              logModelDensity = x745,
                                              success = x746 })
                                   x742
                               with
                                 (st468, x747)
                               in
                               match x741 with {logSamplingDensity = x748}
                               in
                               match p_apply st468 x747 x748 with (st469, x749)
                               in
                               match x741 with {logModelDensity = x750}
                               in
                               p_apply st469 x749 x750)
                          x666
                      with
                        (st470, branchSample1)
                      in
                      match
                        p_map
                          st470
                          (lam x751.
                             lam x752.
                               lam x753.
                                 subf
                                   (subf
                                      (match x751 with CorrectedBranchSample1 x7010
                                       then
                                         x7010.logModelDensity
                                       else
                                         let #var"278" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 155:14-155:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x752)
                                   x753)
                          branchSample1
                      with
                        (st471, x754)
                      in
                      match
                        p_map
                          st471
                          (lam x755.
                             match x755 with CorrectedBranchSample1 x7110
                             then
                               x7110.logSamplingDensity
                             else
                               let #var"279" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 155:45-155:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st472, x756)
                      in
                      match p_apply st472 x754 x756 with (st473, x757)
                      in
                      match
                        getRepertoireSamplingDensity st473 rep2 samplingProb nHosts
                      with
                        (st474, x758)
                      in
                      match
                        p_map
                          st474
                          (lam x759.
                             mulf
                               x759
                               (exp1
                                  (mulf
                                     (int2float
                                        (match tree2 with MsgLeaf carried40
                                         then
                                           carried40.label
                                         else match tree2 with MsgNode carried41
                                         then
                                           carried41.label
                                         else
                                           let #var"280" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 155:113-155:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1))
                                     0.)))
                          x758
                      with
                        (st475, x760)
                      in
                      match p_apply st475 x757 x760 with (st476, x761)
                      in
                      let nl = (match tree2 with MsgLeaf carried40
                                         then
                                           carried40.label
                                         else match tree2 with MsgNode carried41
                                         then
                                           carried41.label
                                         else
                                           let #var"280" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 155:113-155:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1) in
                      let st477 =
                        p_weight
                          st476
                          (hrmStoreLikrWeight nl)
                          (/-temp-/lam x769.
                             x769)
                          x761
                      in
                      let foo2 = {} in
                      match observationMessage1 st477 rep2 1 nHosts with (st478, x762)
                      in
                      match mtxCreate1 st478 nHosts 3 x762 with (st479, newMsg) in
                      let st479 = p_export st479 (hrmStoreNodeMsg nl) newMsg in
                      let st479 = p_export st479 (hrmStorePreorderMsg nl) preorderMsg
                      in
                      match
                        mtxMul
                          st479
                          newMsg
                          (match tree2 with MsgNode x6910
                           then
                             x6910.leftKernel
                           else
                             let #var"281" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 159:33-159:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st480, x763)
                      in
                      match
                        sampleTreeHistory
                          st480
                          (match tree2 with MsgNode x6410
                           then
                             x6410.left
                           else
                             let #var"282" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 164:6-164:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          nHosts
                          x763
                          rep2
                          (match tree2 with MsgLeaf carried42
                           then
                             carried42.age
                           else match tree2 with MsgNode carried43
                           then
                             carried43.age
                           else
                             let #var"283" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 164:39-164:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6710
                           then
                             x6710.leftKernel
                           else
                             let #var"284" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 164:62-164:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st481, x764)
                      in
                      match
                        mtxMul
                          st481
                          newMsg
                          (match tree2 with MsgNode x6810
                           then
                             x6810.rightKernel
                           else
                             let #var"285" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 160:34-160:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st482, x765)
                      in
                      match
                        sampleTreeHistory
                          st482
                          (match tree2 with MsgNode x6010
                           then
                             x6010.right
                           else
                             let #var"286" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 167:6-167:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          nHosts
                          x765
                          rep2
                          (match tree2 with MsgLeaf carried44
                           then
                             carried44.age
                           else match tree2 with MsgNode carried45
                           then
                             carried45.age
                           else
                             let #var"287" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 167:41-167:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6310
                           then
                             x6310.rightKernel
                           else
                             let #var"288" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 167:64-167:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st483, x766)
                      in
                      match
                        p_map
                          st483
                          (lam x767.
                             match x767 with CorrectedBranchSample1 x5910
                             then
                               x5910.history
                             else
                               let #var"289" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 174:16-174:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st484, x768)
                      in
                      (st484, HistoryNode
                        { age =
                            match tree2 with MsgLeaf carried46
                            then
                              carried46.age
                            else match tree2 with MsgNode carried47
                            then
                              carried47.age
                            else
                              let #var"290" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 171:12-171:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
                              in
                              exit 1,
                          label =
                            match tree2 with MsgLeaf carried48
                            then
                              carried48.label
                            else match tree2 with MsgNode carried49
                            then
                              carried49.label
                            else
                              let #var"291" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 172:14-172:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                              in
                              exit 1,
                          left = x764,
                          right = x766,
                          history = x768,
                          repertoire = rep2 })
  in
  recursive
    let rec218 =
      lam acc33.
        lam s221.
          match s221 with [ _ ] ++ _
          then
            match splitAt s221 1 with {#label"1" = x771}
            in
            rec218 (addf acc33 (get s221 0)) x771
          else match s221 with ""
          in
          acc33
  in
  let anon24 =
    lam n12.
      lam hostDistances2.
        lam x852.
          divf
            x852
            (divf
               (rec218 0. (paste0 hostDistances2))
               (int2float (muli n12 (subi n12 1))))
  in
  recursive
    let rec14 =
      lam c66.
        lam c67.
          lam s13.
            match s13 with [ _,
                _ ] ++ _
            then
              match splitAt s13 1 with {#label"1" = x772}
              in
              cons (anon24 c66 c67 (get s13 0)) (rec14 c66 c67 x772)
            else match s13 with [ e13 ]
            then
              match splitAt s13 1 with {#label"1" = x773}
              in
              let slice12 = x773 in
              [ anon24 c66 c67 e13 ]
            else match s13 with ""
            in
            ""
  in
  let anon25 =
    lam n11.
      lam hostDistances1.
        lam x851.
          rec14 n11 hostDistances1 x851
  in
  recursive
    let rec15 =
      lam c68.
        lam c69.
          lam s14.
            match s14 with [ _,
                _ ] ++ _
            then
              match splitAt s14 1 with {#label"1" = x774}
              in
              cons (anon25 c68 c69 (get s14 0)) (rec15 c68 c69 x774)
            else match s14 with [ e14 ]
            then
              match splitAt s14 1 with {#label"1" = x775}
              in
              let slice13 = x775 in
              [ anon25 c68 c69 e14 ]
            else match s14 with ""
            in
            ""
  in
  match input1 with {symbiontTree = #var"X9"}
  in
  let symbiontTree = #var"X9" in
  match input1 with {hostDistances = #var"X10"}
  in
  let hostDistances = #var"X10" in
  let nHosts1 = length1 hostDistances in
  match
    p_assume "lambda"
      st hrmStoreLambda (p_pure (mkDirichlet [ 1., 1., 1., 1. ]))
  with
    (st485, lambda)
  in
  match
    p_assume "mu" st485 hrmStoreMu (p_pure (mkExponential 10.))
  with
    (st486, mu)
  in
  match
    p_assume "beta" st486 hrmStoreBeta (p_pure (mkExponential 1.))
  with
    (st487, beta)
  in
  recursive let buildTree = lam stree.
    match stree with Leaf { label = label, age = _ } then 
      HRMLeaf { label = label }
    else match stree with Node { label = label, age = _, left = left, right = right } in 
      HRMNode { label = label, left = buildTree left, right = buildTree right } in
  match p_export st487 (hrmStoreTree (buildTree symbiontTree) (match input1 with {interactions = ints} in ints)) (p_pure ()) with st487 in
  match
    p_map
      st487
      (lam x776.
         subf 0. (get x776 (subi 1 1)))
      lambda
  with
    (st488, x777)
  in
  match
    p_map st488 (lam x778.
         get x778 (subi 1 1)) lambda
  with
    (st489, x779)
  in
  match
    p_map st489 (lam x780.
         get x780 (subi 2 1)) lambda
  with
    (st490, x781)
  in
  match
    p_map
      st490
      (lam x782.
         lam x783.
           subf 0. (addf (get x782 (subi 2 1)) x783))
      lambda
  with
    (st491, x784)
  in
  match
    p_map st491 (lam x785.
         get x785 (subi 3 1)) lambda
  with
    (st492, x786)
  in
  match p_apply st492 x784 x786 with (st493, x787)
  in
  match
    p_map st493 (lam x788.
         get x788 (subi 3 1)) lambda
  with
    (st494, x789)
  in
  match
    p_map st494 (lam x790.
         get x790 (subi 4 1)) lambda
  with
    (st495, x791)
  in
  match
    p_map
      st495
      (lam x792.
         subf 0. (get x792 (subi 4 1)))
      lambda
  with
    (st496, x793)
  in
  match
    mtxCreate1
      st496
      3
      3
      [ x777,
        x779,
        p_pure 0.,
        x781,
        x787,
        x789,
        p_pure 0.,
        x791,
        x793 ]
  with
    (st497, mtx4)
  in
  match p_map st497 (lam x794.
         x794.m) mtx4 with (st498, m2)
  in
  match p_map st498 (lam x795.
         x795.n) mtx4 with (st499, n5)
  in
  match
    p_map
      st499
      (lam x796.
         lam x797.
           lam x798.
             lam x799.
               lam x800.
                 tmOpaque (let b15 = matMakeUninit (externalExtArrKind x800.arr) x796 x797
                  in
                  let #var"14" = externalCblasCopy x798 x800.arr 1 b15.arr 1 in
                  let #var"15" = externalCblasScal x798 x799 b15.arr 1 in
                  b15))
      m2
  with
    (st500, x801)
  in
  match p_apply st500 x801 n5 with (st501, x802)
  in
  match
    p_map
      st501
      (lam x803.
         lam x804.
           muli x803 x804)
      m2
  with
    (st502, x805)
  in
  match p_apply st502 x805 n5 with (st503, x806)
  in
  match p_apply st503 x802 x806 with (st504, x807)
  in
  match p_apply st504 x807 mu with (st505, x808)
  in
  match p_apply st505 x808 mtx4 with (st506, qMatrix2)
  in
  match input1 with {interactions = #var"X11"}
  in
  match
    postorderTraverse st506 symbiontTree qMatrix2 #var"X11" nHosts1
  with
    (st507, postorderTree)
  in
  let a36 =
    match postorderTree with MsgLeaf carried66
    then
      match carried66 with {outMsg = #var"X16"}
      in
      p_pure #var"X16"
    else match postorderTree with MsgNode carried67
    then
      carried67.outMsg
    else
      let #var"2106" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 38:36-38:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n"
      in
      p_pure (exit 1)
  in
  let b4 = mtxCreate nHosts1 3 (rep (muli 3 nHosts1) 1.) in
  match
    p_map
      st507
      (lam x809.
         match x809 with {m = #var"X12"}
         in
         match b4 with {m = #var"X13"}
         in
         eqi #var"X12" #var"X13")
      a36
  with
    (st508, x810)
  in
  match
    p_map
      st508
      (lam x811.
         match x811 with {n = #var"X14"}
         in
         match b4 with {n = #var"X15"}
         in
         eqi #var"X14" #var"X15")
      a36
  with
    (st509, x812)
  in
  match and1 st509 x810 x812 with (st510, x813)
  in
  match
    p_bind
      st510
      hrmStoreSubmodel
      (hrmInit {})
      (lam st511.
         lam x814.
           match
             match x814 with true
             then
               match
                 p_map
                   st511
                   (lam x815.
                      tmOpaque (let c310 = matMakeUninit (externalExtArrKind x815.arr) x815.m x815.n
                       in
                       let #var"16" = matElemMulNoAlloc x815 b4 c310 in
                       c310))
                   a36
               with
                 (st512, x816)
               in
               (st512, Right
                 x816)
             else
               (st511, Left
                 (DimensionMismatch
                    {}))
           with
             (st513, n3)
           in
           match n3 with Right x817
           then
             p_map
               st513
               (lam x818.
                  Right
                    x818)
               x817
           else match n3 with Left x819
           in
           (st513, p_pure (Left
                x819)))
      x813
  with
    (st514, x820)
  in
  match eitherEither st514 x820 with (st515, rootSamplingProb)
  in
  match
    suggestNodeRep
      st515
      rootSamplingProb
      nHosts1
      (match postorderTree with MsgLeaf carried54
       then
         carried54.label
       else match postorderTree with MsgNode carried55
       then
         carried55.label
       else
         let #var"294" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 39:57-39:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
         in
         exit 1)
  with
    (st516, rootRep)
  in
  let makeDirtyArray = lam st. lam arr.
    p_traverseSeq st (lam st. lam a. (st, a)) arr 
  in
  let pf = lam s. printLn (join ["Root rep [", strJoin ", " (map int2string s), "]"]) in
  -- match makeDirtyArray st516 rootRep with (st516, tmp) in
  -- match p_map st516 pf tmp with (st516, _) in
  match any1 st516 rootRep with (st517, x821)
  in
  match bool2real st517 x821 with (st518, x822)
  in
  -- match p_map st518 (lam s. printLn (join ["Is valid? ", float2string s])) x822 with (st518, _) in
  let rl = (match postorderTree with MsgLeaf carried64
                     then
                       carried64.label
                     else match postorderTree with MsgNode carried65
                     then
                       carried65.label
                     else
                       let #var"2105" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 41:45-41:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1) in
  let st519 =
    p_weight
      st518
      (hrmStoreNodeSuppWeight rl)
      (lam x850.
         externalLog
           (addf
              x850
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried64
                     then
                       carried64.label
                     else match postorderTree with MsgNode carried65
                     then
                       carried65.label
                     else
                       let #var"2105" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 41:45-41:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1))
                 0.)))
      x822
  in
  let foo3 = {} in
  match
    getRepertoireSamplingDensity st519 rootRep rootSamplingProb nHosts1
  with
    (st520, x823)
  in
  let rl = (match postorderTree with MsgLeaf carried64
                     then
                       carried64.label
                     else match postorderTree with MsgNode carried65
                     then
                       carried65.label
                     else
                       let #var"2105" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 41:45-41:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1) in
  let st521 =
    p_weight
      st520
      (hrmStoreLikrWeight rl)
      (lam x849.
         mulf
           (subf
              (negf
                 (log1
                    (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1)))))
              x849)
           (exp1
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried62
                     then
                       carried62.label
                     else match postorderTree with MsgNode carried63
                     then
                       carried63.label
                     else
                       let #var"2104" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 48:70-48:89>:\nField \'label\' not found\n[0m  logWeight (rootLogModelDensity - rootLogSamplingDensity) * exp(Real([31mpostorderTree.label[0m[0m) * 0.);\n"
                       in
                       exit 1))
                 0.)))
      x823
  in
  let foo4 = {} in
  match observationMessage1 st521 rootRep 1 nHosts1 with (st522, x824)
  in
  match mtxCreate1 st522 nHosts1 3 x824 with (st523, newMsg1) in
  let st523 = p_export st523 (hrmStoreNodeMsg rl) newMsg1 in
  let st523 = p_export st523 (hrmStorePreorderMsg rl) (p_pure b4) 
  in
  let ns = rec15 (length1 hostDistances) hostDistances hostDistances
  in
  match mtxGet st523 2 2 qMatrix2 with (st524, x825)
  in
  match p_map st524 (lam x826.
         negf x826) x825 with (st525, q2)
  in
  match mtxGet st525 1 1 qMatrix2 with (st526, x827)
  in
  match p_map st526 (lam x828.
         negf x828) x827 with (st527, x829)
  in
  match mtxGet st527 3 3 qMatrix2 with (st528, x830)
  in
  match p_map st528 (lam x831.
         negf x831) x830 with (st529, x832)
  in
  match mtxGet st529 2 1 qMatrix2 with (st530, x833)
  in
  match
    p_map
      st530
      (lam x834.
         lam x835.
           divf x834 x835)
      x833
  with
    (st531, x836)
  in
  match p_apply st531 x836 q2 with (st532, x837)
  in
  match mtxGet st532 2 3 qMatrix2 with (st533, x838)
  in
  match
    p_map
      st533
      (lam x839.
         lam x840.
           divf x839 x840)
      x838
  with
    (st534, x841)
  in
  match p_apply st534 x841 q2 with (st535, x842)
  in
  let modelParams2 =
    ModelParams1
      { beta = beta,
        hostMetric =
          mtxCreate (length1 ns) (length (get ns (subi 1 1))) (paste0 ns),
        embeddedQMatrix =
          EmbeddedMarkovChainMatrix1
            { totalRates =
                [ x829,
                  q2,
                  x832 ],
              transitionProbs =
                [ [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ],
                  [ x837,
                    p_pure 0.,
                    x842 ],
                  [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ] ],
              mat = qMatrix2 } }
  in
  let rootAge =
    match postorderTree with MsgLeaf carried60
    then
      carried60.age
    else match postorderTree with MsgNode carried61
    then
      carried61.age
    else
      let #var"2103" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 63:16-63:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    mtxMul
      st535
      newMsg1
      (match postorderTree with MsgNode x951
       then
         x951.leftKernel
       else
         let #var"295" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 52:31-52:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st536, x843)
  in
  match
    sampleTreeHistory
      st536
      (match postorderTree with MsgNode x901
       then
         x901.left
       else
         let #var"296" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 65:4-65:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
         in
         exit 1)
      nHosts1
      x843
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x911
       then
         x911.leftKernel
       else
         let #var"297" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 65:72-65:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st537, x844)
  in
  match
    mtxMul
      st537
      newMsg1
      (match postorderTree with MsgNode x941
       then
         x941.rightKernel
       else
         let #var"298" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 53:32-53:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st538, x845)
  in
  match
    sampleTreeHistory
      st538
      (match postorderTree with MsgNode x881
       then
         x881.right
       else
         let #var"299" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 69:4-69:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
         in
         exit 1)
      nHosts1
      x845
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x891
       then
         x891.rightKernel
       else
         let #var"2100" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 69:74-69:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st539, x846)
  in
  match
    p_traverseSeq
      st539
      (lam st540.
         lam x847.
           (st540, x847))
      ""
  with
    (st541, x848)
  in
  let m = mapEmpty subi in
  let makeDirtyArray = lam st. lam arr.
    p_traverseSeq st (lam st. lam a. (st, a)) arr 
  in
  recursive let extractSamples = lam st. lam m. lam hTree.
    match hTree with HistoryLeaf _ then (st, m)
    else match hTree with HistoryNode n in
    match makeDirtyArray st n.repertoire with (st, wrappedRep) in
    let m = mapInsert n.label wrappedRep m in
    match extractSamples st m n.left with (st, m) in
    extractSamples st m n.right
  in
  match makeDirtyArray st541 rootRep with (st541, dRootRep) in
  let m = mapInsert rl dRootRep m in
  match extractSamples st541 m x844 with (st541, m) in
  match extractSamples st541 m x846 with (st541, m) in
  let dirtyKeyVal = lam st. lam kv. match kv with (k, v) in p_map st (lam v. (k, v)) v in 
  match p_traverseSeq st541 dirtyKeyVal (mapToSeq m) with (st541, wrappedReps) in
  match p_map st541 (
    lam mu. lam beta. lam lambda. lam reps.
      -- printLn (join ["Export root rep: [", int2string rootRep1, ", ", int2string rootRep2, "]"]);
      { mu = mu
      , beta = beta
      , lambda = lambda
      , reps = mapFromSeq subi reps 
      }
  ) mu with (st541, partres) in
  match p_apply st541 partres beta with (st541, partres) in
  match p_apply st541 partres lambda with (st541, partres) in
  match p_apply st541 partres wrappedReps with (st541, res) in
   p_export
    st541
    hrmStoreExport
    res