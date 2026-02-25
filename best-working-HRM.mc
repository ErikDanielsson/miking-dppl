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
  type TreeLabeled p18 p19 p20 in
  con Leaf: all p21. all p22. all p23. p21 -> TreeLabeled p21 p22 p23
  in
  con Node: all p24. all p25. all p26. {age: p25, left: TreeLabeled p24 p25 p26, label: p26, right: TreeLabeled p24 p25 p26} -> TreeLabeled p24 p25 p26
  in
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
    lam a951.
      lam b321.
        match a951 with true
        then
          b321
        else
          false
  in
  let and1 =
    lam st951.
      lam a95.
        lam b32.
          p_select
            st951
            (lam x1519.
               match x1519 with true
               then
                 b32
               else
                 p_pure false)
            a95
  in
  let pow = lam x1723.
      lam y2.
        externalPow x1723 y2
  in
  let pow1 =
    lam st950.
      lam x1722.
        lam y1.
          p_map
            st950 (lam x1518.
               externalPow x1722 x1518) y1
  in
  let pow2 =
    lam st948.
      lam x1721.
        lam y.
          match
            p_map
              st948
              (lam x1515.
                 lam x1516.
                   externalPow x1515 x1516)
              x1721
          with
            (st949, x1517)
          in
          p_apply st949 x1517 y
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
  let anon = lam v31.
      lam x1514.
        v31 in
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
  let make =
    lam n9.
      lam v3.
        let i114 = subi n9 1 in
        match geqi i114 0 with true
        then
          rec3 v3 (subi i114 1) (cons (anon v3 i114) "")
        else
          ""
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
      lam n7.
        externalExtArrMakeUninit kind2 n7
  in
  let extArrGetExn =
    lam st947.
      lam a78.
        lam i23.
          p_map
            st947
            (lam x1513.
               externalExtArrGet x1513 i23)
            a78
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
        lam n62.
          { arr = externalExtArrMakeUninit kind1 (muli m41 n62),
            n = n62,
            m = m41 }
  in
  let matMakeUninit1 =
    lam st945.
      lam kind.
        lam m4.
          lam n61.
            match
              p_map
                st945
                (lam x1511.
                   externalExtArrMakeUninit kind (muli m4 x1511))
                n61
            with
              (st946, x1512)
            in
            (st946, { arr = x1512, n = n61, m = m4 })
  in
  let matGetExn =
    lam a691.
      lam i201.
        lam j21.
          match a691 with {arr = #var"X70"}
          in
          match a691 with {n = #var"X71"}
          in
          externalExtArrGet #var"X70" (addi (muli i201 #var"X71") j21)
  in
  let matGetExn1 =
    lam st942.
      lam a69.
        lam i20.
          lam j2.
            match
              p_map
                st942
                (lam x1506.
                   lam x1507.
                     match x1506 with {arr = #var"X68"}
                     in
                     externalExtArrGet #var"X68" x1507)
                a69
            with
              (st943, x1508)
            in
            match
              p_map
                st943
                (lam x1509.
                   match x1509 with {n = #var"X69"}
                   in
                   addi (muli i20 #var"X69") j2)
                a69
            with
              (st944, x1510)
            in
            p_apply st944 x1508 x1510
  in
  let matCopy =
    lam st935.
      lam a63.
        match
          p_map
            st935
            (lam x1493.
               lam x1494.
                 { x1493 with arr = x1494 })
            a63
        with
          (st936, x1495)
        in
        match
          p_map
            st936
            (lam x1496.
               lam x1497.
                 tmOpaque (let b23 = extArrMakeUninit (externalExtArrKind x1496.arr) x1497
                  in
                  let #var"20" = externalCblasCopy x1497 x1496.arr 1 b23 1 in
                  b23))
            a63
        with
          (st937, x1498)
        in
        match
          p_map
            st937
            (lam x1499.
               lam x1500.
                 match x1499 with {m = #var"X67"}
                 in
                 muli #var"X67" x1500)
            a63
        with
          (st938, x1501)
        in
        match
          p_map st938 (lam x1502.
               x1502.n) a63
        with
          (st939, x1503)
        in
        match p_apply st939 x1501 x1503 with (st940, x1504)
        in
        match p_apply st940 x1498 x1504 with (st941, x1505)
        in
        p_apply st941 x1495 x1505
  in
  let matHasSameShape2 =
    lam a61.
      lam b21.
        match a61 with {m = #var"X63"}
        in
        match b21 with {m = #var"X64"}
        in
        match a61 with {n = #var"X65"}
        in
        match b21 with {n = #var"X66"}
        in
        and (eqi #var"X63" #var"X64") (eqi #var"X65" #var"X66")
  in
  let matTranposeNoAlloc =
    lam a58.
      lam b19.
        match a58 with {m = #var"X55"}
        in
        match b19 with {n = #var"X56"}
        in
        match a58 with {n = #var"X57"}
        in
        match b19 with {m = #var"X58"}
        in
        match and (eqi #var"X55" #var"X56") (eqi #var"X57" #var"X58") with true
        then
          match a58 with {m = #var"X59"}
          in
          match a58 with {n = #var"X60"}
          in
          match a58 with {arr = #var"X61"}
          in
          match b19 with {arr = #var"X62"}
          in
          let #var"19" = externalMatTranspose #var"X59" #var"X60" #var"X61" #var"X62"
          in
          Right
            {}
        else
          Left
            (DimensionMismatch
               {})
  in
  let matElemMulNoAlloc =
    lam a57.
      lam b18.
        lam c410.
          match
            and (matHasSameShape2 a57 b18) (matHasSameShape2 b18 c410)
          with
            true
          then
            match a57 with {m = #var"X50"}
            in
            match a57 with {n = #var"X51"}
            in
            match a57 with {arr = #var"X52"}
            in
            match b18 with {arr = #var"X53"}
            in
            match c410 with {arr = #var"X54"}
            in
            let #var"18" =
              externalMatElemMul #var"X50" #var"X51" #var"X52" #var"X53" #var"X54"
            in
            Right
              {}
          else
            Left
              (DimensionMismatch
                 {})
  in
  let matMulExn =
    lam st921.
      lam a51.
        lam b12.
          match
            p_map st921 (lam x1467.
                 x1467.n) a51
          with
            (st922, x1468)
          in
          match
            p_map
              st922
              (lam x1469.
                 lam x1470.
                   lam st923.
                     match
                       match eqi x1469 x1470 with true
                       then
                         match
                           p_map
                             st923
                             (lam x1471.
                                x1471.m)
                             a51
                         with
                           (st924, x1472)
                         in
                         match
                           p_map
                             st924
                             (lam x1473.
                                lam x1474.
                                  lam x1475.
                                    lam x1476.
                                      tmOpaque (let c210 = matMakeUninit (externalExtArrKind x1476.arr) x1473 x1474
                                       in
                                       let #var"13" =
                                         externalCblasGemm
                                           cblasRowMajor
                                           cblasNoTrans
                                           cblasNoTrans
                                           x1473
                                           x1474
                                           x1469
                                           1.
                                           x1475.arr
                                           x1469
                                           x1476.arr
                                           x1474
                                           0.
                                           c210.arr
                                           x1474
                                       in
                                       c210))
                             x1472
                         with
                           (st925, x1477)
                         in
                         match
                           p_map
                             st925
                             (lam x1478.
                                x1478.n)
                             b12
                         with
                           (st926, x1479)
                         in
                         match p_apply st926 x1477 x1479 with (st927, x1480)
                         in
                         match p_apply st927 x1480 a51 with (st928, x1482)
                         in
                         match p_apply st928 x1482 b12 with (st929, x1483)
                         in
                         (st929, Right
                           x1483)
                       else
                         (st923, Left
                           (DimensionMismatch
                              {}))
                     with
                       (st930, n6)
                     in
                     match n6 with Right x1484
                     then
                       p_map
                         st930
                         (lam x1485.
                            Right
                              x1485)
                         x1484
                     else match n6 with Left x1486
                     in
                     (st930, p_pure (Left
                          x1486)))
              x1468
          with
            (st931, x1487)
          in
          match
            p_map st931 (lam x1488.
                 x1488.m) b12
          with
            (st932, x1489)
          in
          match
            p_subApply st932 hrmStoreSubmodel (hrmInit {}) x1487 x1489
          with
            (st933, x1490)
          in
          match p_join st933 x1490 with (st934, x1491)
          in
          p_map
            st934
            (lam x1492.
               match x1492 with Left carried73
               then
                 error (matErrorToString carried73)
               else match x1492 with Right carried74
               in
               carried74)
            x1491
  in
  let exp1 = lam x1591.
      externalExp x1591 in
  let log1 = lam x1582.
      externalLog x1582 in
  let log11 =
    lam st920.
      lam x1581.
        p_map st920 (lam x1466.
             externalLog x1466) x1581
  in
  let cons1 = lam e112.
      lam s83.
        cons e112 s83 in
  let cons11 =
    lam st916.
      lam e111.
        lam s82.
          match e111 with Event1 x1456
          in
          match x1456 with {toState = x1457}
          in
          match
            p_map
              st916
              (lam x1458.
                 lam x1459.
                   match x1456 with {host = x1460}
                   in
                   match x1456 with {eventTime = x1461}
                   in
                   Event1
                     { host = x1460,
                       toState = x1458,
                       eventTime = x1461,
                       fromState = x1459 })
              x1457
          with
            (st917, x1462)
          in
          match x1456 with {fromState = x1463}
          in
          match p_apply st917 x1462 x1463 with (st918, x1464)
          in
          match p_map st918 cons x1464 with (st919, x1465)
          in
          p_apply st919 x1465 s82
  in
  let cons12 = lam e110.
      lam s81.
        cons e110 s81 in
  let paste0 =
    lam st910.
      lam l51.
        match l51 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st910
              (lam st911.
                 lam x1450.
                   (st911, x1450))
              ""
          with
            (st912, x1451)
          in
          match p_map st912 concat x1451 with (st913, x1452)
          in
          match p_apply st913 x1452 (get l51 0) with (st914, x1453)
          in
          match splitAt l51 1 with {#label"1" = x1454}
          in
          rec22 st914 x1453 x1454
        else match l51 with ""
        in
        p_traverseSeq
          st910
          (lam st915.
             lam x1455.
               (st915, x1455))
          ""
  in
  let paste01 =
    lam st904.
      lam l5.
        match l5 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st904
              (lam st905.
                 lam x1440.
                   (st905, x1440))
              ""
          with
            (st906, x1445)
          in
          match p_map st906 concat x1445 with (st907, x1446)
          in
          match p_apply st907 x1446 (get l5 0) with (st908, x1447)
          in
          match splitAt l5 1 with {#label"1" = x1448}
          in
          rec23 st908 x1447 x1448
        else match l5 with ""
        in
        p_traverseSeq
          st904
          (lam st909.
             lam x1449.
               (st909, x1449))
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
  let length13 = lam st903.
      lam l31.
        p_map st903 length l31
  in
  let anon1 =
    lam x1437.
      lam x1438.
        lam x1439.
          match x1439 with true
          then
            snoc x1437 (addi x1438 1)
          else
            x1437
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
    lam s63.
      match s63 with [ e19 ] ++ rest4
      then
        work (anon1 "" 0 e19) (addi 0 1) rest4
      else
        ""
  in
  let whichTrue1 =
    lam st900.
      lam s62.
        match s62 with [ e18 ] ++ rest3
        then
          match
            p_map
              st900
              (lam x1430.
                 match x1430 with true
                 then
                   snoc "" (addi 0 1)
                 else
                   "")
              e18
          with
            (st901, x1435)
          in
          work1 st901 x1435 (addi 0 1) rest3
        else
          p_traverseSeq
            st900
            (lam st902.
               lam x1436.
                 (st902, x1436))
            ""
  in
  let whichTrue2 =
    lam st899.
      lam s61.
        p_map
          st899
          (lam x1429.
             match x1429 with [ e17 ] ++ rest2
             then
               work (anon1 "" 0 e17) (addi 0 1) rest2
             else
               "")
          s61
  in
  let bool2real =
    lam st898.
      lam v.
        p_map
          st898
          (lam x1428.
             match x1428 with true
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
          let a651 =
            tmOpaque (let len2 = length data1 in
             let a742 = externalExtArrMakeUninit extArrKindFloat64 len2 in
             recursive
               let work32 =
                 lam i213.
                   match eqi i213 len2 with true
                   then
                     {}
                   else
                     let #var"2165" = externalExtArrSet a742 i213 (get data1 i213)
                     in
                     work32 (addi i213 1)
             in
             let #var"2212" = work32 0 in
             a742)
          in
          match eqi (muli rows1 cols12) (externalExtArrLength a651) with true
          then
            { arr = a651, n = cols12, m = rows1 }
          else
            error "matFromArrExn: dimensions mismatch"
  in
  let mtxCreate1 =
    lam st894.
      lam rows.
        lam cols11.
          lam data.
            match
              p_traverseSeq
                st894
                (lam st895.
                   lam x1419.
                     (st895, x1419))
                data
            with
              (st896, x1420)
            in
            match
              p_map
                st896
                (lam x1425.
                   tmOpaque (let len1 = length x1425 in
                    let a741 = externalExtArrMakeUninit extArrKindFloat64 len1 in
                    recursive
                      let work31 =
                        lam i212.
                          match eqi i212 len1 with true
                          then
                            {}
                          else
                            let #var"2164" = externalExtArrSet a741 i212 (get x1425 i212)
                            in
                            work31 (addi i212 1)
                    in
                    let #var"2211" = work31 0 in
                    a741))
                x1420
            with
              (st897, x1426)
            in
            p_map
              st897
              (lam x1427.
                 match eqi (muli rows cols11) (externalExtArrLength x1427) with true
                 then
                   { arr = x1427, n = cols11, m = rows }
                 else
                   error "matFromArrExn: dimensions mismatch")
              x1426
  in
  let mtxGet =
    lam st893.
      lam row13.
        lam col2.
          lam mtx62.
            matGetExn1 st893 mtx62 (subi row13 1) (subi col2 1)
  in
  let mtxGet1 =
    lam st887.
      lam row12.
        lam col1.
          lam mtx61.
            match
              p_map
                st887
                (lam x1400.
                   lam x1405.
                     match x1400 with {arr = #var"X49"}
                     in
                     externalExtArrGet #var"X49" x1405)
                mtx61
            with
              (st888, x1406)
            in
            match
              p_map st888 (lam x1407.
                   subi x1407 1) row12
            with
              (st889, x1408)
            in
            match
              p_map
                st889
                (lam x1409.
                   lam x1410.
                     addi (muli x1409 x1410) (subi col1 1))
                x1408
            with
              (st890, x1415)
            in
            match
              p_map st890 (lam x1416.
                   x1416.n) mtx61
            with
              (st891, x1417)
            in
            match p_apply st891 x1415 x1417 with (st892, x1418)
            in
            p_apply st892 x1406 x1418
  in
  let mtxGet2 =
    lam st879.
      lam row11.
        lam col.
          lam mtx6.
            match
              p_map
                st879
                (lam x1377.
                   lam x1378.
                     match x1377 with {arr = #var"X48"}
                     in
                     externalExtArrGet #var"X48" x1378)
                mtx6
            with
              (st880, x1379)
            in
            match
              p_map st880 (lam x1380.
                   subi x1380 1) row11
            with
              (st881, x1385)
            in
            match
              p_map
                st881
                (lam x1386.
                   lam x1387.
                     lam x1388.
                       addi (muli x1386 x1387) x1388)
                x1385
            with
              (st882, x1389)
            in
            match
              p_map st882 (lam x1390.
                   x1390.n) mtx6
            with
              (st883, x1395)
            in
            match p_apply st883 x1389 x1395 with (st884, x1396)
            in
            match
              p_map st884 (lam x1397.
                   subi x1397 1) col
            with
              (st885, x1398)
            in
            match p_apply st885 x1396 x1398 with (st886, x1399)
            in
            p_apply st886 x1379 x1399
  in
  let anon2 =
    lam new5.
      lam mtx55.
        lam row5.
          lam x1375.
            lam x1376.
              match new5 with {arr = #var"X46"}
              in
              match new5 with {n = #var"X47"}
              in
              externalExtArrSet
                #var"X46"
                (addi (muli 0 #var"X47") x1375)
                (matGetExn mtx55 (subi row5 1) (subi x1376 1))
  in
  let anon3 =
    lam st876.
      lam new4.
        lam mtx54.
          lam row4.
            lam x1364.
              lam x1365.
                match new4 with {arr = #var"X44"}
                in
                match
                  p_map
                    st876
                    (lam x1366.
                       lam x1367.
                         externalExtArrSet x1366 x1367 (matGetExn mtx54 (subi row4 1) (subi x1365 1)))
                    #var"X44"
                with
                  (st877, x1368)
                in
                match new4 with {n = #var"X45"}
                in
                match
                  p_map
                    st877
                    (lam x1369.
                       addi (muli 0 x1369) x1364)
                    #var"X45"
                with
                  (st878, x1370)
                in
                p_apply st878 x1368 x1370
  in
  let anon4 =
    lam st870.
      lam new3.
        lam mtx53.
          lam row3.
            lam x1347.
              lam x1348.
                match new3 with {arr = #var"X40"}
                in
                match
                  p_map
                    st870
                    (lam x1349.
                       lam x1350.
                         lam x1355.
                           externalExtArrSet x1349 x1350 x1355)
                    #var"X40"
                with
                  (st871, x1356)
                in
                match new3 with {n = #var"X41"}
                in
                match
                  p_map
                    st871
                    (lam x1357.
                       addi (muli 0 x1357) x1347)
                    #var"X41"
                with
                  (st872, x1358)
                in
                match p_apply st872 x1356 x1358 with (st873, x1359)
                in
                match
                  p_map st873 (lam x1360.
                       subi x1360 1) row3
                with
                  (st874, x1361)
                in
                match
                  p_map
                    st874
                    (lam x1362.
                       match mtx53 with {arr = #var"X42"}
                       in
                       match mtx53 with {n = #var"X43"}
                       in
                       externalExtArrGet #var"X42" (addi (muli x1362 #var"X43") (subi x1348 1)))
                    x1361
                with
                  (st875, x1363)
                in
                p_apply st875 x1359 x1363
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
          match mtx52 with {arr = #var"X39"}
          in
          let new2 =
            matMakeUninit (externalExtArrKind #var"X39") 1 (length cols2)
          in
          let #var"2412" = rec1 new2 mtx52 row2 0 cols2 in
          let #var"102" = {} in
          new2
  in
  let mtxRowCols1 =
    lam st860.
      lam mtx51.
        lam row1.
          lam cols1.
            match mtx51 with {arr = #var"X38"}
            in
            match p_map st860 length cols1 with (st861, x1334)
            in
            match
              matMakeUninit1 st861 (externalExtArrKind #var"X38") 1 x1334
            with
              (st862, new1)
            in
            match
              p_bind
                st862
                hrmStoreSubmodel
                (hrmInit {})
                (lam st863.
                   lam x1335.
                     match
                       match x1335 with [ _,
                           _ ] ++ _
                       then
                         match anon3 st863 new1 mtx51 row1 0 (get x1335 0) with (st864, x1336)
                         in
                         match splitAt x1335 1 with {#label"1" = x1337}
                         in
                         match rec11 st864 new1 mtx51 row1 (addi 0 1) x1337 with (st865, x1338)
                         in
                         (st865, cons x1336 x1338)
                       else match x1335 with [ e16 ]
                       then
                         match splitAt x1335 1 with {#label"1" = x1339}
                         in
                         let slice15 = x1339 in
                         match anon3 st863 new1 mtx51 row1 0 e16 with (st866, x1340)
                         in
                         (st866, [ x1340 ])
                       else match x1335 with ""
                       in
                       (st863, "")
                     with
                       (st867, x1345)
                     in
                     p_traverseSeq
                       st867
                       (lam st868.
                          lam x1346.
                            (st868, x1346))
                       x1345)
                cols1
            with
              (st869, #var"2411")
            in
            let #var"101" = {} in
            (st869, new1)
  in
  let mtxRowCols2 =
    lam st850.
      lam mtx5.
        lam row.
          lam cols.
            match mtx5 with {arr = #var"X37"}
            in
            match p_map st850 length cols with (st851, x1325)
            in
            match
              matMakeUninit1 st851 (externalExtArrKind #var"X37") 1 x1325
            with
              (st852, new)
            in
            match
              p_bind
                st852
                hrmStoreSubmodel
                (hrmInit {})
                (lam st853.
                   lam x1326.
                     match
                       match x1326 with [ _,
                           _ ] ++ _
                       then
                         match anon4 st853 new mtx5 row 0 (get x1326 0) with (st854, x1327)
                         in
                         match splitAt x1326 1 with {#label"1" = x1328}
                         in
                         match rec12 st854 new mtx5 row (addi 0 1) x1328 with (st855, x1329)
                         in
                         (st855, cons x1327 x1329)
                       else match x1326 with [ e15 ]
                       then
                         match splitAt x1326 1 with {#label"1" = x1330}
                         in
                         let slice14 = x1330 in
                         match anon4 st853 new mtx5 row 0 e15 with (st856, x1331)
                         in
                         (st856, [ x1331 ])
                       else match x1326 with ""
                       in
                       (st853, "")
                     with
                       (st857, x1332)
                     in
                     p_traverseSeq
                       st857
                       (lam st858.
                          lam x1333.
                            (st858, x1333))
                       x1332)
                cols
            with
              (st859, #var"2410")
            in
            let #var"10" = {} in
            (st859, new)
  in
  let mtxSclrMul =
    lam st842.
      lam scalar.
        lam mtx41.
          match
            p_map st842 (lam x1300.
                 x1300.m) mtx41
          with
            (st843, m21)
          in
          match
            p_map st843 (lam x1305.
                 x1305.n) mtx41
          with
            (st844, n41)
          in
          match
            p_map
              st844
              (lam x1306.
                 lam x1307.
                   lam x1308.
                     lam x1309.
                       tmOpaque (let b141 = matMakeUninit (externalExtArrKind x1309.arr) x1306 x1307
                        in
                        let #var"141" = externalCblasCopy x1308 x1309.arr 1 b141.arr 1
                        in
                        let #var"151" = externalCblasScal x1308 scalar b141.arr 1 in
                        b141))
              m21
          with
            (st845, x1310)
          in
          match p_apply st845 x1310 n41 with (st846, x1315)
          in
          match
            p_map
              st846
              (lam x1316.
                 lam x1317.
                   muli x1316 x1317)
              m21
          with
            (st847, x1318)
          in
          match p_apply st847 x1318 n41 with (st848, x1319)
          in
          match p_apply st848 x1315 x1319 with (st849, x1320)
          in
          p_apply st849 x1320 mtx41
  in
  let mtxTrans =
    lam st841.
      lam mtx3.
        p_map
          st841
          (lam x1299.
             tmOpaque (let b17 = matMakeUninit (externalExtArrKind x1299.arr) x1299.n x1299.m
              in
              let #var"17" = matTranposeNoAlloc x1299 b17 in
              b17))
          mtx3
  in
  let anon5 =
    lam st836.
      lam mtx112.
        lam mtx241.
          lam x1290.
            match
              p_map
                st836
                (lam x1291.
                   lam x1292.
                     match x1291 with {arr = #var"X36"}
                     in
                     externalExtArrSet #var"X36" x1290 x1292)
                mtx241
            with
              (st837, x1293)
            in
            match
              p_map st837 (lam x1294.
                   x1294.arr) mtx112
            with
              (st838, x1295)
            in
            match extArrGetExn st838 x1295 x1290 with (st839, x1296)
            in
            match
              p_map
                st839
                (lam x1297.
                   match gtf x1297 0. with true
                   then
                     x1297
                   else
                     0.)
                x1296
            with
              (st840, x1298)
            in
            p_apply st840 x1293 x1298
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
    lam st809.
      lam mtx82.
        lam mtx212.
          lam x1237.
            lam x1238.
              match
                p_map
                  st809
                  (lam x1239.
                     lam x1240.
                       lam x1241.
                         match x1239 with {arr = #var"X34"}
                         in
                         externalExtArrSet #var"X34" x1240 x1241)
                  mtx212
              with
                (st810, x1242)
              in
              match
                p_map
                  st810
                  (lam x1243.
                     match x1243 with {n = #var"X35"}
                     in
                     addi (muli x1237 #var"X35") x1238)
                  mtx212
              with
                (st811, x1244)
              in
              match p_apply st811 x1242 x1244 with (st812, x1245)
              in
              match matGetExn1 st812 mtx82 x1237 x1238 with (st813, x1246)
              in
              match
                p_map
                  st813
                  (lam x1247.
                     lam x1248.
                       divf x1247 x1248)
                  x1246
              with
                (st814, x1249)
              in
              match
                p_map st814 (lam x1250.
                     x1250.m) mtx82
              with
                (st815, x1251)
              in
              match
                p_map st815 (lam x1252.
                     subi x1252 1) x1251
              with
                (st816, x1253)
              in
              match
                p_map
                  st816
                  (lam x1254.
                     match geqi x1254 0 with true
                     then
                       rec3 1. (subi x1254 1) (cons (anon 1. x1254) "")
                     else
                       "")
                  x1253
              with
                (st817, x1255)
              in
              match
                p_map
                  st817
                  (lam x1256.
                     tmOpaque (let len = length x1256 in
                      let a74 = externalExtArrMakeUninit extArrKindFloat64 len in
                      recursive
                        let work3 =
                          lam i211.
                            match eqi i211 len with true
                            then
                              {}
                            else
                              let #var"2163" = externalExtArrSet a74 i211 (get x1256 i211) in
                              work3 (addi i211 1)
                      in
                      let #var"2210" = work3 0 in
                      a74))
                  x1255
              with
                (st818, a65)
              in
              match
                p_map st818 (lam x1257.
                     x1257.m) mtx82
              with
                (st819, x1258)
              in
              match
                p_map
                  st819
                  (lam x1259.
                     lam x1260.
                       lam st820.
                         let x1261 =
                           match eqi (muli x1259 1) x1260 with true
                           then
                             { arr = a65, n = 1, m = x1259 }
                           else
                             let x1266 = error "matFromArrExn: dimensions mismatch" in
                             match x1266 with {arr = x1267}
                             in
                             match x1266 with {n = x1268}
                             in
                             match x1266 with {m = x1269}
                             in
                             { arr = p_pure x1267, n = x1268, m = x1269 }
                         in
                         match x1261 with {arr = x1262}
                         in
                         p_map
                           st820
                           (lam x1263.
                              match x1261 with {n = x1264}
                              in
                              match x1261 with {m = x1265}
                              in
                              { arr = x1263, n = x1264, m = x1265 })
                           x1262)
                  x1258
              with
                (st821, x1270)
              in
              match
                p_map
                  st821
                  (lam x1271.
                     externalExtArrLength x1271)
                  a65
              with
                (st822, x1272)
              in
              match
                p_subApply st822 hrmStoreSubmodel (hrmInit {}) x1270 x1272
              with
                (st823, x1273)
              in
              match p_join st823 x1273 with (st824, x1274)
              in
              match matMulExn st824 mtx82 x1274 with (st825, x1275)
              in
              match
                p_map
                  st825
                  (lam x1276.
                     match x1276 with {arr = field26, n = field27, m = field28}
                     in
                     field26)
                  x1275
              with
                (st826, a72)
              in
              match
                p_map
                  st826
                  (lam x1277.
                     externalExtArrLength x1277)
                  a72
              with
                (st827, x1278)
              in
              match
                p_map st827 (lam x1279.
                     subi x1279 1) x1278
              with
                (st828, x1280)
              in
              match
                p_bind
                  st828
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st829.
                     lam x1281.
                       match
                         match geqi x1281 0 with true
                         then
                           match
                             p_map
                               st829
                               (lam x1282.
                                  externalExtArrGet x1282 x1281)
                               a72
                           with
                             (st830, x1283)
                           in
                           rec31 st830 a72 (subi x1281 1) (cons x1283 "")
                         else
                           (st829, "")
                       with
                         (st831, x1284)
                       in
                       p_traverseSeq
                         st831
                         (lam st832.
                            lam x1285.
                              (st832, x1285))
                         x1284)
                  x1280
              with
                (st833, x1286)
              in
              match
                p_map
                  st833 (lam x1287.
                     get x1287 x1237) x1286
              with
                (st834, x1288)
              in
              match p_apply st834 x1249 x1288 with (st835, x1289)
              in
              p_apply st835 x1245 x1289
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
    lam st805.
      lam mtx81.
        lam mtx211.
          lam x1233.
            match
              p_map st805 (lam x1234.
                   x1234.n) mtx81
            with
              (st806, x1235)
            in
            p_subMap
              st806
              hrmStoreSubmodel
              (hrmInit {})
              (lam x1236.
                 lam st807.
                   match geqi 0 x1236 with true
                   then
                     (st807, {})
                   else match anon6 st807 mtx81 mtx211 #frozen"x1233" 0 with (st808, #var"6")
                   in
                   rec41 st808 mtx81 mtx211 #frozen"x1233" x1236 (addi 0 1))
              x1235
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
    lam st788.
      lam mtx2.
        match
          p_map
            st788
            (lam x1216.
               lam x1217.
                 match x1216 with {m = #var"X29"}
                 in
                 match eqi #var"X29" x1217 with true
                 then
                   match x1216 with {m = #var"X30"}
                   in
                   match x1216 with {n = #var"X31"}
                   in
                   match x1216 with {arr = #var"X32"}
                   in
                   Right
                     { x1216 with arr = externalMatExp #var"X30" #var"X31" #var"X32" }
                 else
                   Left
                     (NotSquare
                        {}))
            mtx2
        with
          (st789, x1218)
        in
        match
          p_map st789 (lam x1219.
               x1219.n) mtx2
        with
          (st790, x1220)
        in
        match p_apply st790 x1218 x1220 with (st791, x1221)
        in
        match
          p_map
            st791
            (lam x1222.
               match x1222 with Left carried70
               then
                 match carried70 with NotSquare carried71
                 in
                 error "Not square"
               else match x1222 with Right carried72
               in
               carried72)
            x1221
        with
          (st792, mtx111)
        in
        match matCopy st792 mtx111 with (st793, mtx24)
        in
        match
          p_map
            st793
            (lam x1223.
               lam x1224.
                 match x1223 with {m = #var"X33"}
                 in
                 muli #var"X33" x1224)
            mtx111
        with
          (st794, x1225)
        in
        match
          p_map st794 (lam x1226.
               x1226.n) mtx111
        with
          (st795, x1227)
        in
        match p_apply st795 x1225 x1227 with (st796, x1228)
        in
        match
          p_subMap
            st796
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1229.
               lam st797.
                 match geqi 0 x1229 with true
                 then
                   (st797, {})
                 else match anon5 st797 mtx111 mtx24 0 with (st798, #var"4")
                 in
                 rec4 st798 mtx111 mtx24 x1229 (addi 0 1))
            x1228
        with
          (st799, #var"12")
        in
        let mtx8 = mtx24 in
        match matCopy st799 mtx8 with (st800, mtx21)
        in
        match
          p_map st800 (lam x1230.
               x1230.m) mtx8
        with
          (st801, x1231)
        in
        match
          p_subMap
            st801
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1232.
               lam st802.
                 match geqi 0 x1232 with true
                 then
                   (st802, {})
                 else match anon7 st802 mtx8 mtx21 0 with (st803, #var"5")
                 in
                 rec42 st803 mtx8 mtx21 x1232 (addi 0 1))
            x1231
        with
          (st804, #var"11")
        in
        (st804, mtx21)
  in
  let mtxMul =
    lam st787.
      lam a37.
        lam b5.
          matMulExn st787 a37 b5
  in
  let eitherEither =
    lam st786.
      lam e21.
        p_map
          st786
          (lam x1215.
             match x1215 with Left carried68
             then
               error (matErrorToString carried68)
             else match x1215 with Right carried69
             in
             carried69)
          e21
  in
  let mtxElemMul =
    lam st773.
      lam a361.
        lam b41.
          match
            p_map
              st773
              (lam x1189.
                 lam x1190.
                   match x1189 with {m = #var"X27"}
                   in
                   eqi #var"X27" x1190)
              a361
          with
            (st774, x1195)
          in
          match
            p_map st774 (lam x1196.
                 x1196.m) b41
          with
            (st775, x1197)
          in
          match p_apply st775 x1195 x1197 with (st776, x1198)
          in
          match
            p_map
              st776
              (lam x1199.
                 lam x1200.
                   match x1199 with {n = #var"X28"}
                   in
                   eqi #var"X28" x1200)
              a361
          with
            (st777, x1201)
          in
          match
            p_map st777 (lam x1202.
                 x1202.n) b41
          with
            (st778, x1203)
          in
          match p_apply st778 x1201 x1203 with (st779, x1204)
          in
          match and1 st779 x1198 x1204 with (st780, x1205)
          in
          match
            p_bind
              st780
              hrmStoreSubmodel
              (hrmInit {})
              (lam st781.
                 lam x1206.
                   match
                     match x1206 with true
                     then
                       match
                         p_map
                           st781
                           (lam x1207.
                              lam x1208.
                                tmOpaque (let c311 = matMakeUninit (externalExtArrKind x1207.arr) x1207.m x1207.n
                                 in
                                 let #var"161" = matElemMulNoAlloc x1207 x1208 c311 in
                                 c311))
                           a361
                       with
                         (st782, x1209)
                       in
                       match p_apply st782 x1209 b41 with (st783, x1210)
                       in
                       (st783, Right
                         x1210)
                     else
                       (st781, Left
                         (DimensionMismatch
                            {}))
                   with
                     (st784, n5)
                   in
                   match n5 with Right x1211
                   then
                     p_map
                       st784
                       (lam x1212.
                          Right
                            x1212)
                       x1211
                   else match n5 with Left x1213
                   in
                   (st784, p_pure (Left
                        x1213)))
              x1205
          with
            (st785, x1214)
          in
          eitherEither st785 x1214
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
      match mtx11 with {m = #var"X23"}
      in
      match mtx11 with {n = #var"X24"}
      in
      match mtx11 with {m = #var"X25"}
      in
      match mtx11 with {n = #var"X26"}
      in
      divf
        (work2 (muli #var"X23" #var"X24") mtx11 0 0.)
        (int2float (muli #var"X25" #var"X26"))
  in
  let mtxMean1 =
    lam st765.
      lam mtx1.
        match mtx1 with {n = #var"X18"}
        in
        match
          p_map
            st765
            (lam x1177.
               match mtx1 with {m = #var"X19"}
               in
               muli #var"X19" x1177)
            #var"X18"
        with
          (st766, x1178)
        in
        match
          p_bind
            st766
            hrmStoreSubmodel
            (hrmInit {})
            (lam st767.
               lam x1179.
                 match lti 0 x1179 with true
                 then
                   match mtx1 with {arr = #var"X20"}
                   in
                   match extArrGetExn st767 #var"X20" 0 with (st768, x1180)
                   in
                   match
                     p_map
                       st768
                       (lam x1181.
                          addf 0. x1181)
                       x1180
                   with
                     (st769, x1182)
                   in
                   work21 st769 x1179 mtx1 (addi 0 1) x1182
                 else
                   (st767, p_pure 0.))
            x1178
        with
          (st770, x1183)
        in
        match
          p_map
            st770
            (lam x1184.
               lam x1185.
                 divf x1184 x1185)
            x1183
        with
          (st771, x1186)
        in
        match mtx1 with {n = #var"X21"}
        in
        match
          p_map
            st771
            (lam x1187.
               match mtx1 with {m = #var"X22"}
               in
               int2float (muli #var"X22" x1187))
            #var"X21"
        with
          (st772, x1188)
        in
        p_apply st772 x1186 x1188
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
    let any =
      lam st30.
        lam seq.
          match null seq with true
          then
            (st30, p_pure false)
          else match
            p_map st30 (lam x30.
                 eqi x30 2) (head seq)
          with
            (st31, x31)
          in
          p_bind
            st31
            hrmStoreSubmodel
            (hrmInit {})
            (lam st32.
               lam x32.
                 match x32 with true
                 then
                   (st32, p_pure true)
                 else
                   any st32 (tail seq))
            x31
  in
  let any1 = lam st764.
      lam l21.
        any st764 l21 in
  recursive
    let ones =
      lam nOnes.
        match gti nOnes 0 with true
        then
          cons1 1. (ones (subi nOnes 1))
        else
          ""
  in
  let updateRepertoire =
    lam st746.
      lam currRep81.
        lam event31.
          lam nhosts81.
            match
              p_map
                st746
                (lam x1155.
                   match x1155 with Event1 x1532
                   then
                     x1532.host
                   else
                     let #var"2161" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event31
            with
              (st747, hostIndex42)
            in
            match
              p_traverseSeq
                st747
                (lam st748.
                   lam x1156.
                     (st748, x1156))
                currRep81
            with
              (st749, x1157)
            in
            match
              p_map
                st749
                (lam x1158.
                   subsequence x1158 (subi 1 1))
                x1157
            with
              (st750, x1159)
            in
            match
              p_map
                st750
                (lam x1160.
                   subi x1160 1)
                hostIndex42
            with
              (st751, x1161)
            in
            match p_apply st751 x1159 x1161 with (st752, x1162)
            in
            match
              p_map
                st752
                (lam x1163.
                   match x1163 with Event1 x1522
                   then
                     x1522.toState
                   else
                     let #var"2162" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event31
            with
              (st753, x1164)
            in
            match
              p_traverseSeq
                st753
                (lam st754.
                   lam x1165.
                     (st754, x1165))
                [ x1164 ]
            with
              (st755, x1166)
            in
            match
              p_map
                st755
                (lam x1167.
                   addi x1167 1)
                hostIndex42
            with
              (st756, first1)
            in
            match
              p_traverseSeq
                st756
                (lam st757.
                   lam x1168.
                     (st757, x1168))
                currRep81
            with
              (st758, x1169)
            in
            match p_map st758 subsequence x1169 with (st759, x1170)
            in
            match
              p_map st759 (lam x1171.
                   subi x1171 1) first1
            with
              (st760, x1172)
            in
            match p_apply st760 x1170 x1172 with (st761, x1173)
            in
            match
              p_map
                st761
                (lam x1174.
                   subi (addi nhosts81 1) x1174)
                first1
            with
              (st762, x1175)
            in
            match p_apply st762 x1173 x1175 with (st763, x1176)
            in
            paste01
              st763
              [ x1162,
                x1166,
                x1176 ]
  in
  let updateRepertoire1 =
    lam st732.
      lam currRep8.
        lam event3.
          lam nhosts8.
            match
              p_map
                st732
                (lam x1135.
                   match x1135 with Event1 x1531
                   then
                     x1531.host
                   else
                     let #var"2159" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event3
            with
              (st733, hostIndex41)
            in
            match
              p_map
                st733
                (lam x1136.
                   subsequence x1136 (subi 1 1))
                currRep8
            with
              (st734, x1137)
            in
            match
              p_map
                st734
                (lam x1138.
                   subi x1138 1)
                hostIndex41
            with
              (st735, x1139)
            in
            match p_apply st735 x1137 x1139 with (st736, x1140)
            in
            match
              p_map
                st736
                (lam x1142.
                   match x1142 with Event1 x1521
                   then
                     x1521.toState
                   else
                     let #var"2160" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event3
            with
              (st737, x1143)
            in
            match
              p_traverseSeq
                st737
                (lam st738.
                   lam x1144.
                     (st738, x1144))
                [ x1143 ]
            with
              (st739, x1145)
            in
            match
              p_map
                st739
                (lam x1146.
                   addi x1146 1)
                hostIndex41
            with
              (st740, first)
            in
            match p_map st740 subsequence currRep8 with (st741, x1147)
            in
            match
              p_map st741 (lam x1148.
                   subi x1148 1) first
            with
              (st742, x1149)
            in
            match p_apply st742 x1147 x1149 with (st743, x1150)
            in
            match
              p_map
                st743
                (lam x1152.
                   subi (addi nhosts8 1) x1152)
                first
            with
              (st744, x1153)
            in
            match p_apply st744 x1150 x1153 with (st745, x1154)
            in
            paste01
              st745
              [ x1140,
                x1145,
                x1154 ]
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
            match splitAt s 1 with {#label"1" = x33}
            in
            cons (anon8 c20 (get s 0)) (rec c20 x33)
          else match s with [ e5 ]
          then
            match splitAt s 1 with {#label"1" = x34}
            in
            let slice4 = x34 in
            [ anon8 c20 e5 ]
          else match s with ""
          in
          ""
    let map1 = lam c21.
        lam s14.
          rec c21 s14
    let anon8 =
      lam interaction.
        lam x35.
          match eqi (subi (addi interaction 1) 1) x35 with true
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
                  make 3 1.
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
      lam st33.
        lam obsRepertoire1.
          lam i51.
            lam max1.
              match leqi i51 max1 with true
              then
                match
                  p_map
                    st33
                    (lam x36.
                       match
                         match geqi x36 0 with true
                         then
                           leqi x36 2
                         else
                           false
                       with
                         true
                       then
                         map1 x36 (unfoldr 0)
                       else
                         make 3 1.)
                    (get obsRepertoire1 (subi i51 1))
                with
                  (st34, stateMsg1)
                in
                match
                  p_map
                    st34
                    (lam x37.
                       get x37 (subi 1 1))
                    stateMsg1
                with
                  (st35, x38)
                in
                match
                  p_map
                    st35
                    (lam x39.
                       get x39 (subi 2 1))
                    stateMsg1
                with
                  (st36, x40)
                in
                match
                  p_map
                    st36
                    (lam x41.
                       get x41 (subi 3 1))
                    stateMsg1
                with
                  (st37, x42)
                in
                match
                  observationMessage1 st37 obsRepertoire1 (addi i51 1) max1
                with
                  (st38, x43)
                in
                (st38, cons12 x38 (cons12 x40 (cons12 x42 x43)))
              else
                (st33, "")
  in
  recursive
    let postorderTraverse =
      lam st39.
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
                  let st39 = p_export st39 (hrmStoreNodeMsg ll) (p_pure __outMsg) in
                  (st39, MsgLeaf
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
                    st39
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
                  (st40, left)
                in
                match
                  postorderTraverse
                    st40
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
                  (st41, right)
                in
                match
                  mtxSclrMul
                    st41
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
                  (st42, x44)
                in
                match mtxExpRateSafe st42 x44 with (st43, leftKernel)
                in
                match
                  mtxSclrMul
                    st43
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
                  (st44, x45)
                in
                let getLabel = lam n. match n with MsgLeaf l then l.label else match n with MsgNode n in n.label in
                let leftLabel = getLabel left in
                let rightLabel = getLabel right in
                match mtxExpRateSafe st44 x45 with (st45, rightKernel) in
                -- Save the transition kernels
                let st45 = p_export st45 (hrmStoreTransKernel rightLabel) rightKernel in 
                match mtxTrans st45 leftKernel with (st46, x46) in
                -- Save the transition kernels
                let st46 = p_export st46 (hrmStoreTransKernel leftLabel) leftKernel in 
                match
                  mtxMul
                    st46
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
                    x46
                with
                  (st47, leftInMsg)
                in
                match mtxTrans st47 rightKernel with (st48, x47)
                in
                match
                  mtxMul
                    st48
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
                    x47
                with
                  (st49, rightInMsg)
                in
                match mtxElemMul st49 leftInMsg rightInMsg with (st50, x48)
                in
                (st50, MsgNode
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
                    outMsg = x48,
                    leftInMsg = leftInMsg,
                    rightInMsg = rightInMsg })
  in
  let mtx3ToSeq =
    lam st719.
      lam mtx.
        lam i121.
          match mtxGet st719 i121 1 mtx with (st720, p111)
          in
          match mtxGet st720 i121 2 mtx with (st721, p210)
          in
          match mtxGet st721 i121 3 mtx with (st722, p310)
          in
          match
            p_map
              st722
              (lam x1117.
                 lam x1118.
                   lam x1119.
                     addf (addf x1117 x1118) x1119)
              p111
          with
            (st723, x1120)
          in
          match p_apply st723 x1120 p210 with (st724, x1121)
          in
          match p_apply st724 x1121 p310 with (st725, s51)
          in
          match
            p_map
              st725
              (lam x1122.
                 lam x1123.
                   divf x1122 x1123)
              p111
          with
            (st726, x1124)
          in
          match p_apply st726 x1124 s51 with (st727, x1125)
          in
          match
            p_map
              st727
              (lam x1126.
                 lam x1127.
                   divf x1126 x1127)
              p210
          with
            (st728, x1128)
          in
          match p_apply st728 x1128 s51 with (st729, x1129)
          in
          match
            p_map
              st729
              (lam x1130.
                 lam x1132.
                   divf x1130 x1132)
              p310
          with
            (st730, x1133)
          in
          match p_apply st730 x1133 s51 with (st731, x1134)
          in
          (st731, [ x1125,
            x1129,
            x1134 ])
  in
  recursive
    let rec24 =
      lam st51.
        lam c22.
          lam c23.
            lam acc4.
              lam s24.
                match s24 with [ _ ] ++ _
                then
                  let x49 = get s24 0 in
                  match
                    p_map
                      st51
                      (lam x50.
                         lam x51.
                           addf x50 x51)
                      acc4
                  with
                    (st52, x52)
                  in
                  match mtx3ToSeq st52 c23 x49 with (st53, params)
                  in
                  match
                    p_bind
                      st53
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st54.
                         lam x53.
                           match
                             match geqi x53 0 with true
                             then
                               lti x53 (length12 params)
                             else
                               false
                           with
                             true
                           then
                             log11 st54 (get params (subi (addi x53 1) 1))
                           else
                             (st54, p_pure (log1 0.)))
                      (get c22 (subi x49 1))
                  with
                    (st55, x54)
                  in
                  match p_apply st55 x52 x54 with (st56, x55)
                  in
                  match splitAt s24 1 with {#label"1" = x56}
                  in
                  rec24 st56 c22 c23 x55 x56
                else match s24 with ""
                in
                (st51, acc4)
  in
  let anon9 = lam x1116.
      addi x1116 1 in
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
    lam st714.
      lam x1481.
        lam samplingProb1.
          lam nhosts7.
            let i113 = subi (addi (subi nhosts7 1) 1) 1 in
            let s226 =
              match geqi i113 0 with true
              then
                rec32 (subi i113 1) (cons (anon9 i113) "")
              else
                ""
            in
            match s226 with [ _ ] ++ _
            then
              let x1110 = get s226 0 in
              match mtx3ToSeq st714 samplingProb1 x1110 with (st715, params1)
              in
              match
                p_bind
                  st715
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st716.
                     lam x1111.
                       match
                         match geqi x1111 0 with true
                         then
                           lti x1111 (length12 params1)
                         else
                           false
                       with
                         true
                       then
                         log11 st716 (get params1 (subi (addi x1111 1) 1))
                       else
                         (st716, p_pure (log1 0.)))
                  (get x1481 (subi x1110 1))
              with
                (st717, x1112)
              in
              match
                p_map st717 (lam x1113.
                     addf 0. x1113) x1112
              with
                (st718, x1114)
              in
              match splitAt s226 1 with {#label"1" = x1115}
              in
              rec24 st718 x1481 samplingProb1 x1114 x1115
            else match s226 with ""
            in
            (st714, p_pure 0.)
  in
  recursive
    let rec25 =
      lam st57.
        lam acc5.
          lam s25.
            match s25 with [ _ ] ++ _
            then
              match
                p_bind
                  st57
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st58.
                     lam x57.
                       match eqi x57 2 with true
                       then
                         p_map
                           st58 (lam x58.
                              addi x58 1) acc5
                       else
                         (st58, acc5))
                  (get s25 0)
              with
                (st59, x59)
              in
              match splitAt s25 1 with {#label"1" = x60}
              in
              rec25 st59 x59 x60
            else match s25 with ""
            in
            (st57, acc5)
    let fold =
      lam st60.
        lam init1.
          lam seq5.
            match seq5 with [ _ ] ++ _
            then
              match
                p_map
                  st60
                  (lam x61.
                     match eqi x61 2 with true
                     then
                       addi init1 1
                     else
                       init1)
                  (get seq5 0)
              with
                (st61, x62)
              in
              match splitAt seq5 1 with {#label"1" = x63}
              in
              rec25 st61 x62 x63
            else match seq5 with ""
            in
            (st60, p_pure init1)
    let ifCont3 =
      lam st62.
        lam currRep.
          lam eventSeq.
            lam eventIndex.
              lam nEvents.
                lam nhosts2.
                  lam event.
                    lam #var"3".
                      let hostIndex4 =
                        match event with Event1 x153
                        then
                          x153.host
                        else
                          let #var"216" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                          in
                          exit 1
                      in
                      let s26 =
                        [ slice currRep 1 hostIndex4,
                          [ p_pure
                              (match event with Event1 x152
                               then
                                 x152.toState
                               else
                                 let #var"215" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                                 in
                                 exit 1) ],
                          slice currRep (addi hostIndex4 1) (addi nhosts2 1) ]
                      in
                      let currRep1 =
                        match s26 with [ _ ] ++ _
                        then
                          match splitAt s26 1 with {#label"1" = x69}
                          in
                          rec21 (concat "" (get s26 0)) x69
                        else match s26 with ""
                        in
                        ""
                      in
                      let eventIndex1 = addi eventIndex 1 in
                      match gti eventIndex1 nEvents with true
                      then
                        (st62, p_pure true)
                      else match
                        p_map
                          st62
                          (lam x64.
                             get x64 (subi eventIndex1 1))
                          eventSeq
                      with
                        (st63, x65)
                      in
                      p_bind
                        st63
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st64.
                           lam x66.
                             match
                               eqi
                                 (match x66 with Event1 x301
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
                               match fold st64 0 currRep1 with (st65, x67)
                               in
                               p_bind
                                 st65
                                 hrmStoreSubmodel
                                 (hrmInit {})
                                 (lam st66.
                                    lam x68.
                                      match eqi x68 1 with true
                                      then
                                        (st66, p_pure false)
                                      else
                                        ifCont3 st66 currRep1 eventSeq eventIndex1 nEvents nhosts2 x66 0)
                                 x67
                             else
                               ifCont3 st64 currRep1 eventSeq eventIndex1 nEvents nhosts2 x66 0)
                        x65
    let allTimesValidBranch =
      lam st67.
        lam currRep11.
          lam eventSeq1.
            lam eventIndex11.
              lam nEvents1.
                lam nhosts3.
                  p_bind
                    st67
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st68.
                       lam x70.
                         match gti eventIndex11 x70 with true
                         then
                           (st68, p_pure true)
                         else match
                           p_map
                             st68
                             (lam x71.
                                get x71 (subi eventIndex11 1))
                             eventSeq1
                         with
                           (st69, x72)
                         in
                         p_bind
                           st69
                           hrmStoreSubmodel
                           (hrmInit {})
                           (lam st70.
                              lam x73.
                                match
                                  eqi
                                    (match x73 with Event1 x302
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
                                  match fold st70 0 currRep11 with (st71, x74)
                                  in
                                  p_bind
                                    st71
                                    hrmStoreSubmodel
                                    (hrmInit {})
                                    (lam st72.
                                       lam x75.
                                         match eqi x75 1 with true
                                         then
                                           (st72, p_pure false)
                                         else
                                           ifCont3 st72 currRep11 eventSeq1 eventIndex11 x70 nhosts3 x73 0)
                                    x74
                                else
                                  ifCont3 st70 currRep11 eventSeq1 eventIndex11 x70 nhosts3 x73 0)
                           x72)
                    nEvents1
  in
  let anon10 =
    lam x1109.
      match eqi x1109 2 with true
      then
        true
      else
        eqi x1109 1
  in
  let anon11 =
    lam st713.
      lam x1107.
        p_map
          st713
          (lam x1108.
             match eqi x1108 2 with true
             then
               true
             else
               eqi x1108 1)
          x1107
  in
  recursive
    let rec5 =
      lam s4.
        match s4 with [ _,
            _ ] ++ _
        then
          match splitAt s4 1 with {#label"1" = x76}
          in
          cons (anon10 (get s4 0)) (rec5 x76)
        else match s4 with [ e6 ]
        then
          match splitAt s4 1 with {#label"1" = x77}
          in
          let slice5 = x77 in
          [ anon10 e6 ]
        else match s4 with ""
        in
        ""
    let rec6 =
      lam st73.
        lam s5.
          match s5 with [ _,
              _ ] ++ _
          then
            match anon11 st73 (get s5 0) with (st74, x78)
            in
            match splitAt s5 1 with {#label"1" = x79}
            in
            match rec6 st74 x79 with (st75, x80)
            in
            (st75, cons x78 x80)
          else match s5 with [ e7 ]
          then
            match splitAt s5 1 with {#label"1" = x81}
            in
            let slice6 = x81 in
            match anon11 st73 e7 with (st76, x82)
            in
            (st76, [ x82 ])
          else match s5 with ""
          in
          (st73, "")
  in
  let sapply = lam st712.
      lam s72.
        rec6 st712 s72
  in
  let anon12 = lam x1106.
      eqi x1106 2 in
  let anon13 =
    lam st711.
      lam x1104.
        p_map st711 (lam x1105.
             eqi x1105 2) x1104
  in
  recursive
    let rec7 =
      lam s6.
        match s6 with [ _,
            _ ] ++ _
        then
          match splitAt s6 1 with {#label"1" = x83}
          in
          cons (anon12 (get s6 0)) (rec7 x83)
        else match s6 with [ e8 ]
        then
          match splitAt s6 1 with {#label"1" = x84}
          in
          let slice7 = x84 in
          [ anon12 e8 ]
        else match s6 with ""
        in
        ""
    let rec8 =
      lam st77.
        lam s7.
          match s7 with [ _,
              _ ] ++ _
          then
            match anon13 st77 (get s7 0) with (st78, x85)
            in
            match splitAt s7 1 with {#label"1" = x86}
            in
            match rec8 st78 x86 with (st79, x87)
            in
            (st79, cons x85 x87)
          else match s7 with [ e9 ]
          then
            match splitAt s7 1 with {#label"1" = x88}
            in
            let slice8 = x88 in
            match anon13 st77 e9 with (st80, x89)
            in
            (st80, [ x89 ])
          else match s7 with ""
          in
          (st77, "")
  in
  let sapply1 = lam st710.
      lam s71.
        rec8 st710 s71
  in
  let getGainRate =
    lam st702.
      lam repertoire14.
        lam hostIndex33.
          lam modelParams123.
            let fromState53 = get repertoire14 (subi hostIndex33 1) in
            match
              mtxGet
                st702
                (addi fromState53 1)
                (addi (addi fromState53 1) 1)
                (match
                   match modelParams123 with ModelParams1 x1444
                   then
                     x1444.embeddedQMatrix
                   else
                     let #var"2151" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1434
                 then
                   x1434.mat
                 else
                   let #var"2152" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st703, baseRate13)
            in
            match eqi fromState53 0 with true
            then
              match
                p_map
                  st703
                  (lam x1092.
                     lam x1093.
                       mulf x1092 x1093)
                  baseRate13
              with
                (st704, x1094)
              in
              match
                p_map
                  st704
                  (lam x1095.
                     negf x1095)
                  (match modelParams123 with ModelParams1 x1384
                   then
                     x1384.beta
                   else
                     let #var"2153" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                     in
                     p_pure (exit 1))
              with
                (st705, x1096)
              in
              match
                pow1
                  st705
                  (divf
                     (mtxMean
                        (mtxRowCols
                           (match modelParams123 with ModelParams1 x1394
                            then
                              x1394.hostMetric
                            else
                              let #var"2154" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                              in
                              exit 1)
                           hostIndex33
                           (whichTrue (rec5 repertoire14))))
                     (match modelParams123 with ModelParams1 x1374
                      then
                        x1374.meanDist
                      else
                        let #var"2155" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                        in
                        exit 1))
                  x1096
              with
                (st706, x1097)
              in
              p_apply st706 x1094 x1097
            else match
              p_map
                st703
                (lam x1098.
                   lam x1099.
                     mulf x1098 x1099)
                baseRate13
            with
              (st707, x1100)
            in
            match
              p_map
                st707
                (lam x1101.
                   negf x1101)
                (match modelParams123 with ModelParams1 x1414
                 then
                   x1414.beta
                 else
                   let #var"2156" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                   in
                   p_pure (exit 1))
            with
              (st708, x1102)
            in
            match
              pow1
                st708
                (divf
                   (mtxMean
                      (mtxRowCols
                         (match modelParams123 with ModelParams1 x1424
                          then
                            x1424.hostMetric
                          else
                            let #var"2157" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex33
                         (whichTrue (rec7 repertoire14))))
                   (match modelParams123 with ModelParams1 x1404
                    then
                      x1404.meanDist
                    else
                      let #var"2158" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                      in
                      exit 1))
                x1102
            with
              (st709, x1103)
            in
            p_apply st709 x1100 x1103
  in
  let getGainRate1 =
    lam st681.
      lam repertoire13.
        lam hostIndex32.
          lam modelParams122.
            let fromState52 = get repertoire13 (subi hostIndex32 1) in
            match
              p_map
                st681
                (lam x1056.
                   addi x1056 1)
                fromState52
            with
              (st682, x1057)
            in
            match
              p_map
                st682
                (lam x1058.
                   addi (addi x1058 1) 1)
                fromState52
            with
              (st683, x1059)
            in
            match
              mtxGet2
                st683
                x1057
                x1059
                (match
                   match modelParams122 with ModelParams1 x1443
                   then
                     x1443.embeddedQMatrix
                   else
                     let #var"2143" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1433
                 then
                   x1433.mat
                 else
                   let #var"2144" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st684, baseRate12)
            in
            p_bind
              st684
              hrmStoreSubmodel
              (hrmInit {})
              (lam st685.
                 lam x1060.
                   match eqi x1060 0 with true
                   then
                     match
                       p_map
                         st685
                         (lam x1063.
                            lam x1064.
                              mulf x1063 x1064)
                         baseRate12
                     with
                       (st686, x1065)
                     in
                     match sapply st686 repertoire13 with (st687, x1066)
                     in
                     match whichTrue1 st687 x1066 with (st688, x1067)
                     in
                     match
                       mtxRowCols1
                         st688
                         (match modelParams122 with ModelParams1 x1393
                          then
                            x1393.hostMetric
                          else
                            let #var"2145" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex32
                         x1067
                     with
                       (st689, x1068)
                     in
                     match mtxMean1 st689 x1068 with (st690, x1069)
                     in
                     match
                       p_map
                         st690
                         (lam x1070.
                            divf
                              x1070
                              (match modelParams122 with ModelParams1 x1373
                               then
                                 x1373.meanDist
                               else
                                 let #var"2146" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x1069
                     with
                       (st691, x1073)
                     in
                     match
                       p_map
                         st691
                         (lam x1074.
                            negf x1074)
                         (match modelParams122 with ModelParams1 x1383
                          then
                            x1383.beta
                          else
                            let #var"2147" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st692, x1075)
                     in
                     match pow2 st692 x1073 x1075 with (st693, x1076)
                     in
                     p_apply st693 x1065 x1076
                   else match
                     p_map
                       st685
                       (lam x1077.
                          lam x1078.
                            mulf x1077 x1078)
                       baseRate12
                   with
                     (st694, x1079)
                   in
                   match sapply1 st694 repertoire13 with (st695, x1080)
                   in
                   match whichTrue1 st695 x1080 with (st696, x1083)
                   in
                   match
                     mtxRowCols1
                       st696
                       (match modelParams122 with ModelParams1 x1423
                        then
                          x1423.hostMetric
                        else
                          let #var"2148" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex32
                       x1083
                   with
                     (st697, x1084)
                   in
                   match mtxMean1 st697 x1084 with (st698, x1085)
                   in
                   match
                     p_map
                       st698
                       (lam x1086.
                          divf
                            x1086
                            (match modelParams122 with ModelParams1 x1403
                             then
                               x1403.meanDist
                             else
                               let #var"2149" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1085
                   with
                     (st699, x1087)
                   in
                   match
                     p_map
                       st699
                       (lam x1088.
                          negf x1088)
                       (match modelParams122 with ModelParams1 x1413
                        then
                          x1413.beta
                        else
                          let #var"2150" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st700, x1089)
                   in
                   match pow2 st700 x1087 x1089 with (st701, x1090)
                   in
                   p_apply st701 x1079 x1090)
              fromState52
  in
  let getGainRate2 =
    lam st655.
      lam repertoire12.
        lam hostIndex31.
          lam modelParams121.
            match
              p_traverseSeq
                st655
                (lam st656.
                   lam x1020.
                     (st656, x1020))
                repertoire12
            with
              (st657, x1021)
            in
            match p_map st657 get x1021 with (st658, x1022)
            in
            match
              p_map
                st658
                (lam x1023.
                   subi x1023 1)
                hostIndex31
            with
              (st659, x1024)
            in
            match p_apply st659 x1022 x1024 with (st660, fromState51)
            in
            match
              p_map
                st660
                (lam x1025.
                   addi x1025 1)
                fromState51
            with
              (st661, x1026)
            in
            match
              p_map
                st661
                (lam x1027.
                   addi (addi x1027 1) 1)
                fromState51
            with
              (st662, x1028)
            in
            match
              mtxGet2
                st662
                x1026
                x1028
                (match
                   match modelParams121 with ModelParams1 x1442
                   then
                     x1442.embeddedQMatrix
                   else
                     let #var"2135" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1432
                 then
                   x1432.mat
                 else
                   let #var"2136" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st663, baseRate11)
            in
            p_bind
              st663
              hrmStoreSubmodel
              (hrmInit {})
              (lam st664.
                 lam x1029.
                   match eqi x1029 0 with true
                   then
                     match
                       p_map
                         st664
                         (lam x1030.
                            lam x1031.
                              mulf x1030 x1031)
                         baseRate11
                     with
                       (st665, x1032)
                     in
                     match sapply st665 repertoire12 with (st666, x1033)
                     in
                     match whichTrue1 st666 x1033 with (st667, x1034)
                     in
                     match
                       mtxRowCols2
                         st667
                         (match modelParams121 with ModelParams1 x1392
                          then
                            x1392.hostMetric
                          else
                            let #var"2137" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex31
                         x1034
                     with
                       (st668, x1035)
                     in
                     match mtxMean1 st668 x1035 with (st669, x1036)
                     in
                     match
                       p_map
                         st669
                         (lam x1037.
                            divf
                              x1037
                              (match modelParams121 with ModelParams1 x1372
                               then
                                 x1372.meanDist
                               else
                                 let #var"2138" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x1036
                     with
                       (st670, x1038)
                     in
                     match
                       p_map
                         st670
                         (lam x1039.
                            negf x1039)
                         (match modelParams121 with ModelParams1 x1382
                          then
                            x1382.beta
                          else
                            let #var"2139" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st671, x1040)
                     in
                     match pow2 st671 x1038 x1040 with (st672, x1043)
                     in
                     p_apply st672 x1032 x1043
                   else match
                     p_map
                       st664
                       (lam x1044.
                          lam x1045.
                            mulf x1044 x1045)
                       baseRate11
                   with
                     (st673, x1046)
                   in
                   match sapply1 st673 repertoire12 with (st674, x1047)
                   in
                   match whichTrue1 st674 x1047 with (st675, x1048)
                   in
                   match
                     mtxRowCols2
                       st675
                       (match modelParams121 with ModelParams1 x1422
                        then
                          x1422.hostMetric
                        else
                          let #var"2140" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex31
                       x1048
                   with
                     (st676, x1049)
                   in
                   match mtxMean1 st676 x1049 with (st677, x1050)
                   in
                   match
                     p_map
                       st677
                       (lam x1051.
                          divf
                            x1051
                            (match modelParams121 with ModelParams1 x1402
                             then
                               x1402.meanDist
                             else
                               let #var"2141" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1050
                   with
                     (st678, x1052)
                   in
                   match
                     p_map
                       st678
                       (lam x1053.
                          negf x1053)
                       (match modelParams121 with ModelParams1 x1412
                        then
                          x1412.beta
                        else
                          let #var"2142" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st679, x1054)
                   in
                   match pow2 st679 x1052 x1054 with (st680, x1055)
                   in
                   p_apply st680 x1046 x1055)
              fromState51
  in
  let getGainRate3 =
    lam st631.
      lam repertoire11.
        lam hostIndex3.
          lam modelParams12.
            match p_map st631 get repertoire11 with (st632, x982)
            in
            match
              p_map st632 (lam x983.
                   subi x983 1) hostIndex3
            with
              (st633, x984)
            in
            match p_apply st633 x982 x984 with (st634, fromState5)
            in
            match
              p_map st634 (lam x985.
                   addi x985 1) fromState5
            with
              (st635, x986)
            in
            match
              p_map
                st635
                (lam x987.
                   addi (addi x987 1) 1)
                fromState5
            with
              (st636, x988)
            in
            match
              mtxGet2
                st636
                x986
                x988
                (match
                   match modelParams12 with ModelParams1 x1441
                   then
                     x1441.embeddedQMatrix
                   else
                     let #var"2127" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1431
                 then
                   x1431.mat
                 else
                   let #var"2128" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st637, baseRate1)
            in
            p_bind
              st637
              hrmStoreSubmodel
              (hrmInit {})
              (lam st638.
                 lam x989.
                   match eqi x989 0 with true
                   then
                     match
                       p_map
                         st638
                         (lam x990.
                            lam x991.
                              mulf x990 x991)
                         baseRate1
                     with
                       (st639, x992)
                     in
                     match
                       p_map
                         st639
                         (lam x993.
                            match x993 with [ _,
                                _ ] ++ _
                            then
                              match splitAt x993 1 with {#label"1" = x994}
                              in
                              cons (anon10 (get x993 0)) (rec5 x994)
                            else match x993 with [ e13 ]
                            then
                              match splitAt x993 1 with {#label"1" = x995}
                              in
                              let slice12 = x995 in
                              [ anon10 e13 ]
                            else match x993 with ""
                            in
                            "")
                         repertoire11
                     with
                       (st640, x996)
                     in
                     match whichTrue2 st640 x996 with (st641, x997)
                     in
                     match
                       mtxRowCols2
                         st641
                         (match modelParams12 with ModelParams1 x1391
                          then
                            x1391.hostMetric
                          else
                            let #var"2129" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex3
                         x997
                     with
                       (st642, x998)
                     in
                     match mtxMean1 st642 x998 with (st643, x999)
                     in
                     match
                       p_map
                         st643
                         (lam x1000.
                            divf
                              x1000
                              (match modelParams12 with ModelParams1 x1371
                               then
                                 x1371.meanDist
                               else
                                 let #var"2130" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x999
                     with
                       (st644, x1001)
                     in
                     match
                       p_map
                         st644
                         (lam x1002.
                            negf x1002)
                         (match modelParams12 with ModelParams1 x1381
                          then
                            x1381.beta
                          else
                            let #var"2131" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st645, x1003)
                     in
                     match pow2 st645 x1001 x1003 with (st646, x1004)
                     in
                     p_apply st646 x992 x1004
                   else match
                     p_map
                       st638
                       (lam x1005.
                          lam x1006.
                            mulf x1005 x1006)
                       baseRate1
                   with
                     (st647, x1007)
                   in
                   match
                     p_map
                       st647
                       (lam x1008.
                          match x1008 with [ _,
                              _ ] ++ _
                          then
                            match splitAt x1008 1 with {#label"1" = x1009}
                            in
                            cons (anon12 (get x1008 0)) (rec7 x1009)
                          else match x1008 with [ e14 ]
                          then
                            match splitAt x1008 1 with {#label"1" = x1010}
                            in
                            let slice13 = x1010 in
                            [ anon12 e14 ]
                          else match x1008 with ""
                          in
                          "")
                       repertoire11
                   with
                     (st648, x1011)
                   in
                   match whichTrue2 st648 x1011 with (st649, x1012)
                   in
                   match
                     mtxRowCols2
                       st649
                       (match modelParams12 with ModelParams1 x1421
                        then
                          x1421.hostMetric
                        else
                          let #var"2132" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex3
                       x1012
                   with
                     (st650, x1013)
                   in
                   match mtxMean1 st650 x1013 with (st651, x1014)
                   in
                   match
                     p_map
                       st651
                       (lam x1015.
                          divf
                            x1015
                            (match modelParams12 with ModelParams1 x1401
                             then
                               x1401.meanDist
                             else
                               let #var"2133" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1014
                   with
                     (st652, x1016)
                   in
                   match
                     p_map
                       st652
                       (lam x1017.
                          negf x1017)
                       (match modelParams12 with ModelParams1 x1411
                        then
                          x1411.beta
                        else
                          let #var"2134" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st653, x1018)
                   in
                   match pow2 st653 x1016 x1018 with (st654, x1019)
                   in
                   p_apply st654 x1007 x1019)
              fromState5
  in
  let anon14 =
    lam x980.
      lam x981.
        match eqi x981 2 with true
        then
          addi x980 1
        else
          x980
  in
  recursive
    let rec26 =
      lam acc6.
        lam s27.
          match s27 with [ _ ] ++ _
          then
            match splitAt s27 1 with {#label"1" = x90}
            in
            rec26 (anon14 acc6 (get s27 0)) x90
          else match s27 with ""
          in
          acc6
    let rec27 =
      lam st81.
        lam acc7.
          lam s28.
            match s28 with [ _ ] ++ _
            then
              match
                p_bind
                  st81
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st82.
                     lam x91.
                       match eqi x91 2 with true
                       then
                         p_map
                           st82 (lam x92.
                              addi x92 1) acc7
                       else
                         (st82, acc7))
                  (get s28 0)
              with
                (st83, x93)
              in
              match splitAt s28 1 with {#label"1" = x94}
              in
              rec27 st83 x93 x94
            else match s28 with ""
            in
            (st81, acc7)
  in
  let fold1 =
    lam st629.
      lam init12.
        lam seq52.
          match seq52 with [ _ ] ++ _
          then
            match
              p_map
                st629
                (lam x977.
                   match eqi x977 2 with true
                   then
                     addi init12 1
                   else
                     init12)
                (get seq52 0)
            with
              (st630, x978)
            in
            match splitAt seq52 1 with {#label"1" = x979}
            in
            rec27 st630 x978 x979
          else match seq52 with ""
          in
          (st629, p_pure init12)
  in
  let getLossRate =
    lam st628.
      lam repertoire3.
        lam hostIndex23.
          lam modelParams103.
            let fromState33 = get repertoire3 (subi hostIndex23 1) in
            match
              match eqi fromState33 2 with true
              then
                eqi (rec26 0 repertoire3) 1
              else
                false
            with
              true
            then
              (st628, p_pure 0.)
            else
              mtxGet
                st628
                (addi fromState33 1)
                (addi (subi fromState33 1) 1)
                (match
                   match modelParams103 with ModelParams1 x1354
                   then
                     x1354.embeddedQMatrix
                   else
                     let #var"2125" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1344
                 then
                   x1344.mat
                 else
                   let #var"2126" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
  in
  let getLossRate1 =
    lam st621.
      lam repertoire2.
        lam hostIndex22.
          lam modelParams102.
            let fromState32 = get repertoire2 (subi hostIndex22 1) in
            match
              p_bind
                st621
                hrmStoreSubmodel
                (hrmInit {})
                (lam st622.
                   lam x968.
                     match eqi x968 2 with true
                     then
                       match fold1 st622 0 repertoire2 with (st623, x969)
                       in
                       p_map
                         st623 (lam x970.
                            eqi x970 1) x969
                     else
                       (st622, p_pure false))
                fromState32
            with
              (st624, x971)
            in
            p_bind
              st624
              hrmStoreSubmodel
              (hrmInit {})
              (lam st625.
                 lam x972.
                   match x972 with true
                   then
                     (st625, p_pure 0.)
                   else match
                     p_map
                       st625
                       (lam x973.
                          addi x973 1)
                       fromState32
                   with
                     (st626, x974)
                   in
                   match
                     p_map
                       st626
                       (lam x975.
                          addi (subi x975 1) 1)
                       fromState32
                   with
                     (st627, x976)
                   in
                   mtxGet2
                     st627
                     x974
                     x976
                     (match
                        match modelParams102 with ModelParams1 x1353
                        then
                          x1353.embeddedQMatrix
                        else
                          let #var"2123" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1343
                      then
                        x1343.mat
                      else
                        let #var"2124" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x971
  in
  let getLossRate2 =
    lam st609.
      lam repertoire1.
        lam hostIndex21.
          lam modelParams101.
            match
              p_traverseSeq
                st609
                (lam st610.
                   lam x954.
                     (st610, x954))
                repertoire1
            with
              (st611, x955)
            in
            match p_map st611 get x955 with (st612, x956)
            in
            match
              p_map
                st612 (lam x957.
                   subi x957 1) hostIndex21
            with
              (st613, x958)
            in
            match p_apply st613 x956 x958 with (st614, fromState31)
            in
            match
              p_bind
                st614
                hrmStoreSubmodel
                (hrmInit {})
                (lam st615.
                   lam x959.
                     match eqi x959 2 with true
                     then
                       match fold1 st615 0 repertoire1 with (st616, x960)
                       in
                       p_map
                         st616 (lam x961.
                            eqi x961 1) x960
                     else
                       (st615, p_pure false))
                fromState31
            with
              (st617, x962)
            in
            p_bind
              st617
              hrmStoreSubmodel
              (hrmInit {})
              (lam st618.
                 lam x963.
                   match x963 with true
                   then
                     (st618, p_pure 0.)
                   else match
                     p_map
                       st618
                       (lam x964.
                          addi x964 1)
                       fromState31
                   with
                     (st619, x965)
                   in
                   match
                     p_map
                       st619
                       (lam x966.
                          addi (subi x966 1) 1)
                       fromState31
                   with
                     (st620, x967)
                   in
                   mtxGet2
                     st620
                     x965
                     x967
                     (match
                        match modelParams101 with ModelParams1 x1352
                        then
                          x1352.embeddedQMatrix
                        else
                          let #var"2121" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1342
                      then
                        x1342.mat
                      else
                        let #var"2122" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x962
  in
  let getLossRate3 =
    lam st599.
      lam repertoire.
        lam hostIndex2.
          lam modelParams10.
            match p_map st599 get repertoire with (st600, x938)
            in
            match
              p_map st600 (lam x939.
                   subi x939 1) hostIndex2
            with
              (st601, x940)
            in
            match p_apply st601 x938 x940 with (st602, fromState3)
            in
            match
              p_bind
                st602
                hrmStoreSubmodel
                (hrmInit {})
                (lam st603.
                   lam x942.
                     match eqi x942 2 with true
                     then
                       match
                         p_map
                           st603
                           (lam x943.
                              match x943 with [ _ ] ++ _
                              then
                                match splitAt x943 1 with {#label"1" = x944}
                                in
                                rec26 (anon14 0 (get x943 0)) x944
                              else match x943 with ""
                              in
                              0)
                           repertoire
                       with
                         (st604, x945)
                       in
                       p_map
                         st604 (lam x946.
                            eqi x946 1) x945
                     else
                       (st603, p_pure false))
                fromState3
            with
              (st605, x947)
            in
            p_bind
              st605
              hrmStoreSubmodel
              (hrmInit {})
              (lam st606.
                 lam x948.
                   match x948 with true
                   then
                     (st606, p_pure 0.)
                   else match
                     p_map
                       st606
                       (lam x949.
                          addi x949 1)
                       fromState3
                   with
                     (st607, x950)
                   in
                   match
                     p_map
                       st607
                       (lam x952.
                          addi (subi x952 1) 1)
                       fromState3
                   with
                     (st608, x953)
                   in
                   mtxGet2
                     st608
                     x950
                     x953
                     (match
                        match modelParams10 with ModelParams1 x1351
                        then
                          x1351.embeddedQMatrix
                        else
                          let #var"2119" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1341
                      then
                        x1341.mat
                      else
                        let #var"2120" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x947
  in
  recursive
    let rec28 =
      lam st84.
        lam c24.
          lam c25.
            lam acc8.
              lam s29.
                match s29 with [ _ ] ++ _
                then
                  let x95 = get s29 0 in
                  match
                    p_bind
                      st84
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st85.
                         lam x96.
                           match eqi x96 2 with true
                           then
                             (st85, acc8)
                           else match
                             p_map
                               st85
                               (lam x97.
                                  lam x98.
                                    addf x97 x98)
                               acc8
                           with
                             (st86, x99)
                           in
                           match getGainRate1 st86 c24 x95 c25 with (st87, x100)
                           in
                           p_apply st87 x99 x100)
                      (get c24 (subi x95 1))
                  with
                    (st88, x101)
                  in
                  match splitAt s29 1 with {#label"1" = x102}
                  in
                  rec28 st88 c24 c25 x101 x102
                else match s29 with ""
                in
                (st84, acc8)
    let rec29 =
      lam st89.
        lam c26.
          lam c27.
            lam acc9.
              lam s210.
                match s210 with [ _ ] ++ _
                then
                  let x103 = get s210 0 in
                  match
                    p_bind
                      st89
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st90.
                         lam x104.
                           match eqi (get x104 (subi x103 1)) 2 with true
                           then
                             (st90, acc9)
                           else match
                             p_map
                               st90
                               (lam x105.
                                  lam x106.
                                    addf x105 x106)
                               acc9
                           with
                             (st91, x107)
                           in
                           match getGainRate st91 x104 x103 c27 with (st92, x108)
                           in
                           p_apply st92 x107 x108)
                      c26
                  with
                    (st93, x109)
                  in
                  match splitAt s210 1 with {#label"1" = x110}
                  in
                  rec29 st93 c26 c27 x109 x110
                else match s210 with ""
                in
                (st89, acc9)
  in
  let anon15 = lam x937.
      addi x937 1 in
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
    let rec210 =
      lam st94.
        lam c28.
          lam c29.
            lam acc10.
              lam s211.
                match s211 with [ _ ] ++ _
                then
                  let x111 = get s211 0 in
                  match
                    p_bind
                      st94
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st95.
                         lam x112.
                           match eqi x112 0 with true
                           then
                             (st95, acc10)
                           else match
                             p_map
                               st95
                               (lam x113.
                                  lam x114.
                                    addf x113 x114)
                               acc10
                           with
                             (st96, x115)
                           in
                           match getLossRate1 st96 c28 x111 c29 with (st97, x116)
                           in
                           p_apply st97 x115 x116)
                      (get c28 (subi x111 1))
                  with
                    (st98, x117)
                  in
                  match splitAt s211 1 with {#label"1" = x118}
                  in
                  rec210 st98 c28 c29 x117 x118
                else match s211 with ""
                in
                (st94, acc10)
    let rec211 =
      lam st99.
        lam c30.
          lam c31.
            lam acc15.
              lam s212.
                match s212 with [ _ ] ++ _
                then
                  let x119 = get s212 0 in
                  match
                    p_bind
                      st99
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st100.
                         lam x120.
                           match eqi (get x120 (subi x119 1)) 0 with true
                           then
                             (st100, acc15)
                           else match
                             p_map
                               st100
                               (lam x121.
                                  lam x122.
                                    addf x121 x122)
                               acc15
                           with
                             (st101, x123)
                           in
                           match getLossRate st101 x120 x119 c31 with (st102, x124)
                           in
                           p_apply st102 x123 x124)
                      c30
                  with
                    (st103, x125)
                  in
                  match splitAt s212 1 with {#label"1" = x126}
                  in
                  rec211 st103 c30 c31 x125 x126
                else match s212 with ""
                in
                (st99, acc15)
  in
  let anon16 = lam x936.
      addi x936 1 in
  recursive
    let rec34 =
      lam i14.
        lam acc16.
          match geqi i14 0 with true
          then
            rec34 (subi i14 1) (cons (anon16 i14) acc16)
          else
            acc16
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
    lam st589.
      lam currRep51.
        lam modelParams81.
          lam nhosts61.
            let s224 = create1 (addi (subi nhosts61 1) 1) in
            match
              match s224 with [ _ ] ++ _
              then
                let x919 = get s224 0 in
                match
                  p_bind
                    st589
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st590.
                       lam x920.
                         match eqi x920 2 with true
                         then
                           (st590, p_pure 0.)
                         else match getGainRate1 st590 currRep51 x919 modelParams81 with (st591, x921)
                         in
                         p_map
                           st591
                           (lam x922.
                              addf 0. x922)
                           x921)
                    (get currRep51 (subi x919 1))
                with
                  (st592, x923)
                in
                match splitAt s224 1 with {#label"1" = x924}
                in
                rec28 st592 currRep51 modelParams81 x923 x924
              else match s224 with ""
              in
              (st589, p_pure 0.)
            with
              (st593, x925)
            in
            match
              p_map
                st593
                (lam x926.
                   lam x927.
                     addf x926 x927)
                x925
            with
              (st594, x928)
            in
            let s225 = create11 (addi (subi nhosts61 1) 1) in
            match
              match s225 with [ _ ] ++ _
              then
                let x929 = get s225 0 in
                match
                  p_bind
                    st594
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st595.
                       lam x930.
                         match eqi x930 0 with true
                         then
                           (st595, p_pure 0.)
                         else match getLossRate1 st595 currRep51 x929 modelParams81 with (st596, x931)
                         in
                         p_map
                           st596
                           (lam x932.
                              addf 0. x932)
                           x931)
                    (get currRep51 (subi x929 1))
                with
                  (st597, x933)
                in
                match splitAt s225 1 with {#label"1" = x934}
                in
                rec210 st597 currRep51 modelParams81 x933 x934
              else match s225 with ""
              in
              (st594, p_pure 0.)
            with
              (st598, x935)
            in
            p_apply st598 x928 x935
  in
  let getTotalRate1 =
    lam st579.
      lam currRep5.
        lam modelParams8.
          lam nhosts6.
            let s222 = create1 (addi (subi nhosts6 1) 1) in
            match
              match s222 with [ _ ] ++ _
              then
                let x900 = get s222 0 in
                match
                  p_bind
                    st579
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st580.
                       lam x902.
                         match eqi (get x902 (subi x900 1)) 2 with true
                         then
                           (st580, p_pure 0.)
                         else match getGainRate st580 x902 x900 modelParams8 with (st581, x903)
                         in
                         p_map
                           st581
                           (lam x904.
                              addf 0. x904)
                           x903)
                    currRep5
                with
                  (st582, x905)
                in
                match splitAt s222 1 with {#label"1" = x906}
                in
                rec29 st582 currRep5 modelParams8 x905 x906
              else match s222 with ""
              in
              (st579, p_pure 0.)
            with
              (st583, x907)
            in
            match
              p_map
                st583
                (lam x908.
                   lam x909.
                     addf x908 x909)
                x907
            with
              (st584, x910)
            in
            let s223 = create11 (addi (subi nhosts6 1) 1) in
            match
              match s223 with [ _ ] ++ _
              then
                let x912 = get s223 0 in
                match
                  p_bind
                    st584
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st585.
                       lam x913.
                         match eqi (get x913 (subi x912 1)) 0 with true
                         then
                           (st585, p_pure 0.)
                         else match getLossRate st585 x913 x912 modelParams8 with (st586, x914)
                         in
                         p_map
                           st586
                           (lam x915.
                              addf 0. x915)
                           x914)
                    currRep5
                with
                  (st587, x916)
                in
                match splitAt s223 1 with {#label"1" = x917}
                in
                rec211 st587 currRep5 modelParams8 x916 x917
              else match s223 with ""
              in
              (st584, p_pure 0.)
            with
              (st588, x918)
            in
            p_apply st588 x910 x918
  in
  recursive
    let fullModelWeight =
      lam st104.
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
                                st104
                                (lam x127.
                                   lam x128.
                                     mulf (negf (subf x127 finalAge)) x128)
                                currAge
                            with
                              (st105, x129)
                            in
                            match
                              getTotalRate1 st105 currRep3 modelParams nhosts5
                            with
                              (st106, x130)
                            in
                            p_apply st106 x129 x130
                          else match
                            p_map
                              st104
                              (lam x131.
                                 get x131 (subi nextIndex 1))
                              eventSeq3
                          with
                            (st107, nextEvent)
                          in
                          match
                            p_map
                              st107
                              (lam x132.
                                 match x132 with Event1 x311
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
                            (st108, newAge)
                          in
                          match
                            getTotalRate1 st108 currRep3 modelParams nhosts5
                          with
                            (st109, totalLeavingRate1)
                          in
                          match
                            p_map
                              st109
                              (lam x133.
                                 match x133 with Event1 x1321
                                 then
                                   x1321.host
                                 else
                                   let #var"219" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st110, hostIndex1)
                          in
                          match
                            p_map
                              st110
                              (lam x134.
                                 lam x135.
                                   lam st111.
                                     match
                                       gti
                                         (match x134 with Event1 x1301
                                          then
                                            x1301.fromState
                                          else
                                            let #var"220" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x135
                                     with
                                       true
                                     then
                                       getLossRate3 st111 currRep3 hostIndex1 modelParams
                                     else
                                       getGainRate3 st111 currRep3 hostIndex1 modelParams)
                              nextEvent
                          with
                            (st112, x136)
                          in
                          match
                            p_map
                              st112
                              (lam x137.
                                 match x137 with Event1 x1311
                                 then
                                   x1311.toState
                                 else
                                   let #var"221" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st113, x138)
                          in
                          match
                            p_subApply st113 hrmStoreSubmodel (hrmInit {}) x136 x138
                          with
                            (st114, x139)
                          in
                          match p_join st114 x139 with (st115, x140)
                          in
                          match
                            p_map
                              st115
                              (lam x141.
                                 lam x142.
                                   divf x141 x142)
                              x140
                          with
                            (st116, x143)
                          in
                          match p_apply st116 x143 totalLeavingRate1 with (st117, x144)
                          in
                          match log11 st117 x144 with (st118, x145)
                          in
                          match
                            p_map
                              st118
                              (lam x146.
                                 lam x147.
                                   lam x148.
                                     addf (subf x146 x147) x148)
                              x145
                          with
                            (st119, x149)
                          in
                          match
                            p_map
                              st119
                              (lam x150.
                                 lam x151.
                                   lam x154.
                                     mulf (subf x150 x151) x154)
                              currAge
                          with
                            (st120, x155)
                          in
                          match p_apply st120 x155 newAge with (st121, x156)
                          in
                          match p_apply st121 x156 totalLeavingRate1 with (st122, x157)
                          in
                          match p_apply st122 x149 x157 with (st123, x158)
                          in
                          match
                            updateRepertoire1 st123 currRep3 nextEvent nhosts5
                          with
                            (st124, x159)
                          in
                          match
                            fullModelWeight
                              st124
                              (addi nextIndex 1)
                              x159
                              finalRep
                              newAge
                              finalAge
                              eventSeq3
                              nEvents3
                              nhosts5
                              modelParams
                          with
                            (st125, x160)
                          in
                          p_apply st125 x158 x160
    let fullModelWeight1 =
      lam st126.
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
                                st126
                                (lam x161.
                                   lam x162.
                                     mulf (negf (subf x161 finalAge1)) x162)
                                currAge1
                            with
                              (st127, x163)
                            in
                            match
                              getTotalRate1 st127 currRep31 modelParams1 nhosts51
                            with
                              (st128, x164)
                            in
                            p_apply st128 x163 x164
                          else match
                            p_map
                              st126
                              (lam x165.
                                 get x165 (subi nextIndex1 1))
                              eventSeq31
                          with
                            (st129, nextEvent1)
                          in
                          match
                            p_map
                              st129
                              (lam x166.
                                 match x166 with Event1 x312
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
                            (st130, newAge1)
                          in
                          match
                            getTotalRate1 st130 currRep31 modelParams1 nhosts51
                          with
                            (st131, totalLeavingRate11)
                          in
                          match
                            p_map
                              st131
                              (lam x167.
                                 match x167 with Event1 x1322
                                 then
                                   x1322.host
                                 else
                                   let #var"223" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st132, hostIndex11)
                          in
                          match
                            p_map
                              st132
                              (lam x168.
                                 lam x169.
                                   lam st133.
                                     match
                                       gti
                                         (match x168 with Event1 x1302
                                          then
                                            x1302.fromState
                                          else
                                            let #var"224" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x169
                                     with
                                       true
                                     then
                                       getLossRate3 st133 currRep31 hostIndex11 modelParams1
                                     else
                                       getGainRate3 st133 currRep31 hostIndex11 modelParams1)
                              nextEvent1
                          with
                            (st134, x170)
                          in
                          match
                            p_map
                              st134
                              (lam x171.
                                 match x171 with Event1 x1312
                                 then
                                   x1312.toState
                                 else
                                   let #var"225" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st135, x172)
                          in
                          match
                            p_subApply st135 hrmStoreSubmodel (hrmInit {}) x170 x172
                          with
                            (st136, x173)
                          in
                          match p_join st136 x173 with (st137, x174)
                          in
                          match
                            p_map
                              st137
                              (lam x175.
                                 lam x176.
                                   divf x175 x176)
                              x174
                          with
                            (st138, x177)
                          in
                          match p_apply st138 x177 totalLeavingRate11 with (st139, x178)
                          in
                          match log11 st139 x178 with (st140, x179)
                          in
                          match
                            p_map
                              st140
                              (lam x180.
                                 lam x181.
                                   lam x182.
                                     addf (subf x180 x181) x182)
                              x179
                          with
                            (st141, x183)
                          in
                          match
                            p_map
                              st141
                              (lam x184.
                                 lam x185.
                                   lam x186.
                                     mulf (subf x184 x185) x186)
                              currAge1
                          with
                            (st142, x187)
                          in
                          match p_apply st142 x187 newAge1 with (st143, x188)
                          in
                          match p_apply st143 x188 totalLeavingRate11 with (st144, x189)
                          in
                          match p_apply st144 x183 x189 with (st145, x190)
                          in
                          match
                            updateRepertoire1 st145 currRep31 nextEvent1 nhosts51
                          with
                            (st146, x191)
                          in
                          match
                            fullModelWeight1
                              st146
                              (addi nextIndex1 1)
                              x191
                              finalRep1
                              newAge1
                              finalAge1
                              eventSeq31
                              nEvents31
                              nhosts51
                              modelParams1
                          with
                            (st147, x192)
                          in
                          p_apply st147 x190 x192
  in
  recursive
    let hostIndepLikelihood =
      lam st148.
        lam nextIndex11.
          lam currState.
            lam finalState.
              lam currAge11.
                lam finalAge11.
                  lam eventSeq4.
                    lam embeddedQMatrix.
                      match length13 st148 eventSeq4 with (st149, x193)
                      in
                      p_bind
                        st149
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st150.
                           lam x194.
                             match gti nextIndex11 x194 with true
                             then
                               match
                                 p_traverseSeq
                                   st150
                                   (lam st151.
                                      lam x195.
                                        (st151, x195))
                                   (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x321
                                    then
                                      x321.totalRates
                                    else
                                      let #var"226" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x196.
                                           p_pure x196)
                                        (exit 1))
                               with
                                 (st152, x197)
                               in
                               match
                                 p_map
                                   st152
                                   (lam x198.
                                      lam x199.
                                        mulf (negf (subf currAge11 finalAge11)) (get x198 x199))
                                   x197
                               with
                                 (st153, x200)
                               in
                               match
                                 p_map
                                   st153
                                   (lam x201.
                                      subi (addi x201 1) 1)
                                   currState
                               with
                                 (st154, x202)
                               in
                               p_apply st154 x200 x202
                             else match
                               p_map
                                 st150
                                 (lam x203.
                                    get x203 (subi nextIndex11 1))
                                 eventSeq4
                             with
                               (st155, nextEvent11)
                             in
                             match
                               p_map
                                 st155
                                 (lam x204.
                                    match x204 with Event1 x361
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
                               (st156, nextState)
                             in
                             match
                               p_map
                                 st156
                                 (lam x205.
                                    match x205 with Event1 x351
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
                               (st157, nextAge)
                             in
                             match
                               p_traverseSeq
                                 st157
                                 (lam st158.
                                    lam x206.
                                      p_traverseSeq
                                        st158
                                        (lam st159.
                                           lam x207.
                                             (st159, x207))
                                        x206)
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x331
                                  then
                                    x331.transitionProbs
                                  else
                                    let #var"229" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x208.
                                         map
                                           (lam x209.
                                              p_pure x209)
                                           x208)
                                      (exit 1))
                             with
                               (st160, x210)
                             in
                             match
                               p_map
                                 st160
                                 (lam x211.
                                    lam x212.
                                      get (get x211 x212))
                                 x210
                             with
                               (st161, x213)
                             in
                             match
                               p_map
                                 st161
                                 (lam x214.
                                    subi (addi x214 1) 1)
                                 currState
                             with
                               (st162, x215)
                             in
                             match p_apply st162 x213 x215 with (st163, x216)
                             in
                             match
                               p_map
                                 st163
                                 (lam x217.
                                    subi (addi x217 1) 1)
                                 nextState
                             with
                               (st164, x218)
                             in
                             match p_apply st164 x216 x218 with (st165, x219)
                             in
                             match log11 st165 x219 with (st166, x220)
                             in
                             match
                               p_map
                                 st166
                                 (lam x222.
                                    lam x223.
                                      lam x224.
                                        addf (subf x222 x223) x224)
                                 x220
                             with
                               (st167, x225)
                             in
                             match
                               p_map
                                 st167
                                 (lam x226.
                                    lam x227.
                                      mulf (subf currAge11 x226) x227)
                                 nextAge
                             with
                               (st168, x228)
                             in
                             match
                               p_traverseSeq
                                 st168
                                 (lam st169.
                                    lam x229.
                                      (st169, x229))
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x341
                                  then
                                    x341.totalRates
                                  else
                                    let #var"230" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x230.
                                         p_pure x230)
                                      (exit 1))
                             with
                               (st170, x232)
                             in
                             match p_map st170 get x232 with (st171, x233)
                             in
                             match
                               p_map
                                 st171
                                 (lam x234.
                                    subi (addi x234 1) 1)
                                 currState
                             with
                               (st172, x235)
                             in
                             match p_apply st172 x233 x235 with (st173, x236)
                             in
                             match p_apply st173 x228 x236 with (st174, x237)
                             in
                             match p_apply st174 x225 x237 with (st175, x238)
                             in
                             match
                               hostIndepLikelihood1
                                 st175
                                 (addi nextIndex11 1)
                                 nextState
                                 finalState
                                 nextAge
                                 finalAge11
                                 eventSeq4
                                 embeddedQMatrix
                             with
                               (st176, x239)
                             in
                             p_apply st176 x238 x239)
                        x193
    let hostIndepLikelihood1 =
      lam st177.
        lam nextIndex12.
          lam currState1.
            lam finalState1.
              lam currAge12.
                lam finalAge12.
                  lam eventSeq41.
                    lam embeddedQMatrix1.
                      match length13 st177 eventSeq41 with (st178, x240)
                      in
                      p_bind
                        st178
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st179.
                           lam x241.
                             match gti nextIndex12 x241 with true
                             then
                               match
                                 p_map
                                   st179
                                   (lam x242.
                                      lam x243.
                                        mulf (negf (subf x242 finalAge12)) x243)
                                   currAge12
                               with
                                 (st180, x244)
                               in
                               match
                                 p_traverseSeq
                                   st180
                                   (lam st181.
                                      lam x245.
                                        (st181, x245))
                                   (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x322
                                    then
                                      x322.totalRates
                                    else
                                      let #var"231" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x246.
                                           p_pure x246)
                                        (exit 1))
                               with
                                 (st182, x247)
                               in
                               match p_map st182 get x247 with (st183, x248)
                               in
                               match
                                 p_map
                                   st183
                                   (lam x249.
                                      subi (addi x249 1) 1)
                                   currState1
                               with
                                 (st184, x250)
                               in
                               match p_apply st184 x248 x250 with (st185, x251)
                               in
                               p_apply st185 x244 x251
                             else match
                               p_map
                                 st179
                                 (lam x252.
                                    get x252 (subi nextIndex12 1))
                                 eventSeq41
                             with
                               (st186, nextEvent12)
                             in
                             match
                               p_map
                                 st186
                                 (lam x253.
                                    match x253 with Event1 x362
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
                               (st187, nextState1)
                             in
                             match
                               p_map
                                 st187
                                 (lam x254.
                                    match x254 with Event1 x352
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
                               (st188, nextAge1)
                             in
                             match
                               p_traverseSeq
                                 st188
                                 (lam st189.
                                    lam x255.
                                      p_traverseSeq
                                        st189
                                        (lam st190.
                                           lam x256.
                                             (st190, x256))
                                        x255)
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x332
                                  then
                                    x332.transitionProbs
                                  else
                                    let #var"234" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x257.
                                         map
                                           (lam x258.
                                              p_pure x258)
                                           x257)
                                      (exit 1))
                             with
                               (st191, x259)
                             in
                             match
                               p_map
                                 st191
                                 (lam x260.
                                    lam x261.
                                      get (get x260 x261))
                                 x259
                             with
                               (st192, x262)
                             in
                             match
                               p_map
                                 st192
                                 (lam x263.
                                    subi (addi x263 1) 1)
                                 currState1
                             with
                               (st193, x264)
                             in
                             match p_apply st193 x262 x264 with (st194, x265)
                             in
                             match
                               p_map
                                 st194
                                 (lam x266.
                                    subi (addi x266 1) 1)
                                 nextState1
                             with
                               (st195, x267)
                             in
                             match p_apply st195 x265 x267 with (st196, x268)
                             in
                             match log11 st196 x268 with (st197, x269)
                             in
                             match
                               p_map
                                 st197
                                 (lam x270.
                                    lam x271.
                                      lam x272.
                                        addf (subf x270 x271) x272)
                                 x269
                             with
                               (st198, x273)
                             in
                             match
                               p_map
                                 st198
                                 (lam x274.
                                    lam x275.
                                      lam x276.
                                        mulf (subf x274 x275) x276)
                                 currAge12
                             with
                               (st199, x277)
                             in
                             match p_apply st199 x277 nextAge1 with (st200, x278)
                             in
                             match
                               p_traverseSeq
                                 st200
                                 (lam st201.
                                    lam x279.
                                      (st201, x279))
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x342
                                  then
                                    x342.totalRates
                                  else
                                    let #var"235" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x280.
                                         p_pure x280)
                                      (exit 1))
                             with
                               (st202, x281)
                             in
                             match p_map st202 get x281 with (st203, x282)
                             in
                             match
                               p_map
                                 st203
                                 (lam x283.
                                    subi (addi x283 1) 1)
                                 currState1
                             with
                               (st204, x284)
                             in
                             match p_apply st204 x282 x284 with (st205, x285)
                             in
                             match p_apply st205 x278 x285 with (st206, x286)
                             in
                             match p_apply st206 x273 x286 with (st207, x287)
                             in
                             match
                               hostIndepLikelihood1
                                 st207
                                 (addi nextIndex12 1)
                                 nextState1
                                 finalState1
                                 nextAge1
                                 finalAge12
                                 eventSeq41
                                 embeddedQMatrix1
                             with
                               (st208, x288)
                             in
                             p_apply st208 x287 x288)
                        x240
    let hostIndepLikelihood2 =
      lam st209.
        lam nextIndex13.
          lam currState2.
            lam finalState2.
              lam currAge13.
                lam finalAge13.
                  lam eventSeq42.
                    lam embeddedQMatrix2.
                      match length13 st209 eventSeq42 with (st210, x289)
                      in
                      p_bind
                        st210
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st211.
                           lam x290.
                             match gti nextIndex13 x290 with true
                             then
                               match
                                 p_traverseSeq
                                   st211
                                   (lam st212.
                                      lam x291.
                                        (st212, x291))
                                   (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x323
                                    then
                                      x323.totalRates
                                    else
                                      let #var"236" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x292.
                                           p_pure x292)
                                        (exit 1))
                               with
                                 (st213, x293)
                               in
                               match
                                 p_map
                                   st213
                                   (lam x294.
                                      lam x295.
                                        mulf (negf (subf currAge13 finalAge13)) (get x294 x295))
                                   x293
                               with
                                 (st214, x296)
                               in
                               match
                                 p_map
                                   st214
                                   (lam x297.
                                      subi (addi x297 1) 1)
                                   currState2
                               with
                                 (st215, x298)
                               in
                               p_apply st215 x296 x298
                             else match
                               p_map
                                 st211
                                 (lam x299.
                                    get x299 (subi nextIndex13 1))
                                 eventSeq42
                             with
                               (st216, nextEvent13)
                             in
                             match
                               p_map
                                 st216
                                 (lam x300.
                                    match x300 with Event1 x363
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
                               (st217, nextState2)
                             in
                             match
                               p_map
                                 st217
                                 (lam x303.
                                    match x303 with Event1 x353
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
                               (st218, nextAge2)
                             in
                             match
                               p_traverseSeq
                                 st218
                                 (lam st219.
                                    lam x304.
                                      p_traverseSeq
                                        st219
                                        (lam st220.
                                           lam x305.
                                             (st220, x305))
                                        x304)
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x333
                                  then
                                    x333.transitionProbs
                                  else
                                    let #var"239" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x306.
                                         map
                                           (lam x307.
                                              p_pure x307)
                                           x306)
                                      (exit 1))
                             with
                               (st221, x308)
                             in
                             match
                               p_map
                                 st221
                                 (lam x309.
                                    lam x310.
                                      get (get x309 x310))
                                 x308
                             with
                               (st222, x313)
                             in
                             match
                               p_map
                                 st222
                                 (lam x314.
                                    subi (addi x314 1) 1)
                                 currState2
                             with
                               (st223, x315)
                             in
                             match p_apply st223 x313 x315 with (st224, x316)
                             in
                             match
                               p_map
                                 st224
                                 (lam x317.
                                    subi (addi x317 1) 1)
                                 nextState2
                             with
                               (st225, x318)
                             in
                             match p_apply st225 x316 x318 with (st226, x319)
                             in
                             match log11 st226 x319 with (st227, x320)
                             in
                             match
                               p_map
                                 st227
                                 (lam x324.
                                    lam x325.
                                      lam x326.
                                        addf (subf x324 x325) x326)
                                 x320
                             with
                               (st228, x327)
                             in
                             match
                               p_map
                                 st228
                                 (lam x328.
                                    lam x329.
                                      mulf (subf currAge13 x328) x329)
                                 nextAge2
                             with
                               (st229, x330)
                             in
                             match
                               p_traverseSeq
                                 st229
                                 (lam st230.
                                    lam x334.
                                      (st230, x334))
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x343
                                  then
                                    x343.totalRates
                                  else
                                    let #var"240" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x335.
                                         p_pure x335)
                                      (exit 1))
                             with
                               (st231, x336)
                             in
                             match p_map st231 get x336 with (st232, x337)
                             in
                             match
                               p_map
                                 st232
                                 (lam x338.
                                    subi (addi x338 1) 1)
                                 currState2
                             with
                               (st233, x339)
                             in
                             match p_apply st233 x337 x339 with (st234, x340)
                             in
                             match p_apply st234 x330 x340 with (st235, x344)
                             in
                             match p_apply st235 x327 x344 with (st236, x345)
                             in
                             match
                               hostIndepLikelihood3
                                 st236
                                 (addi nextIndex13 1)
                                 nextState2
                                 finalState2
                                 nextAge2
                                 finalAge13
                                 eventSeq42
                                 embeddedQMatrix2
                             with
                               (st237, x346)
                             in
                             p_apply st237 x345 x346)
                        x289
    let hostIndepLikelihood3 =
      lam st238.
        lam nextIndex14.
          lam currState3.
            lam finalState3.
              lam currAge14.
                lam finalAge14.
                  lam eventSeq43.
                    lam embeddedQMatrix3.
                      match length13 st238 eventSeq43 with (st239, x347)
                      in
                      p_bind
                        st239
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st240.
                           lam x348.
                             match gti nextIndex14 x348 with true
                             then
                               match
                                 p_map
                                   st240
                                   (lam x349.
                                      lam x350.
                                        mulf (negf (subf x349 finalAge14)) x350)
                                   currAge14
                               with
                                 (st241, x354)
                               in
                               match
                                 p_traverseSeq
                                   st241
                                   (lam st242.
                                      lam x355.
                                        (st242, x355))
                                   (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3210
                                    then
                                      x3210.totalRates
                                    else
                                      let #var"241" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x356.
                                           p_pure x356)
                                        (exit 1))
                               with
                                 (st243, x357)
                               in
                               match p_map st243 get x357 with (st244, x358)
                               in
                               match
                                 p_map
                                   st244
                                   (lam x359.
                                      subi (addi x359 1) 1)
                                   currState3
                               with
                                 (st245, x360)
                               in
                               match p_apply st245 x358 x360 with (st246, x364)
                               in
                               p_apply st246 x354 x364
                             else match
                               p_map
                                 st240
                                 (lam x365.
                                    get x365 (subi nextIndex14 1))
                                 eventSeq43
                             with
                               (st247, nextEvent14)
                             in
                             match
                               p_map
                                 st247
                                 (lam x366.
                                    match x366 with Event1 x367
                                    then
                                      x367.toState
                                    else
                                      let #var"242" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent14
                             with
                               (st248, nextState3)
                             in
                             match
                               p_map
                                 st248
                                 (lam x368.
                                    match x368 with Event1 x3510
                                    then
                                      x3510.eventTime
                                    else
                                      let #var"243" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent14
                             with
                               (st249, nextAge3)
                             in
                             match
                               p_traverseSeq
                                 st249
                                 (lam st250.
                                    lam x369.
                                      p_traverseSeq
                                        st250
                                        (lam st251.
                                           lam x370.
                                             (st251, x370))
                                        x369)
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3310
                                  then
                                    x3310.transitionProbs
                                  else
                                    let #var"244" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x371.
                                         map
                                           (lam x372.
                                              p_pure x372)
                                           x371)
                                      (exit 1))
                             with
                               (st252, x373)
                             in
                             match
                               p_map
                                 st252
                                 (lam x374.
                                    lam x375.
                                      get (get x374 x375))
                                 x373
                             with
                               (st253, x376)
                             in
                             match
                               p_map
                                 st253
                                 (lam x377.
                                    subi (addi x377 1) 1)
                                 currState3
                             with
                               (st254, x378)
                             in
                             match p_apply st254 x376 x378 with (st255, x379)
                             in
                             match
                               p_map
                                 st255
                                 (lam x380.
                                    subi (addi x380 1) 1)
                                 nextState3
                             with
                               (st256, x381)
                             in
                             match p_apply st256 x379 x381 with (st257, x382)
                             in
                             match log11 st257 x382 with (st258, x383)
                             in
                             match
                               p_map
                                 st258
                                 (lam x384.
                                    lam x385.
                                      lam x386.
                                        addf (subf x384 x385) x386)
                                 x383
                             with
                               (st259, x387)
                             in
                             match
                               p_map
                                 st259
                                 (lam x388.
                                    lam x389.
                                      lam x390.
                                        mulf (subf x388 x389) x390)
                                 currAge14
                             with
                               (st260, x391)
                             in
                             match p_apply st260 x391 nextAge3 with (st261, x392)
                             in
                             match
                               p_traverseSeq
                                 st261
                                 (lam st262.
                                    lam x393.
                                      (st262, x393))
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3410
                                  then
                                    x3410.totalRates
                                  else
                                    let #var"245" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x394.
                                         p_pure x394)
                                      (exit 1))
                             with
                               (st263, x395)
                             in
                             match p_map st263 get x395 with (st264, x396)
                             in
                             match
                               p_map
                                 st264
                                 (lam x397.
                                    subi (addi x397 1) 1)
                                 currState3
                             with
                               (st265, x398)
                             in
                             match p_apply st265 x396 x398 with (st266, x399)
                             in
                             match p_apply st266 x392 x399 with (st267, x400)
                             in
                             match p_apply st267 x387 x400 with (st268, x401)
                             in
                             match
                               hostIndepLikelihood3
                                 st268
                                 (addi nextIndex14 1)
                                 nextState3
                                 finalState3
                                 nextAge3
                                 finalAge14
                                 eventSeq43
                                 embeddedQMatrix3
                             with
                               (st269, x402)
                             in
                             p_apply st269 x401 x402)
                        x347
  in
  let anon17 = lam x899.
      addi x899 1 in
  recursive
    let rec35 =
      lam i15.
        lam acc17.
          match geqi i15 0 with true
          then
            rec35 (subi i15 1) (cons (anon17 i15) acc17)
          else
            acc17
  in
  let anon18 =
    lam st574.
      lam msg1.
        lam nodeLabel51.
          lam x893.
            match
              mtx3ToSeq st574 msg1 (addi x893 (muli nodeLabel51 0))
            with
              (st575, x894)
            in
            match
              p_traverseSeq
                st575
                (lam st576.
                   lam x895.
                     (st576, x895))
                x894
            with
              (st577, x896)
            in
            match
              p_map st577 (lam x897.
                   mkCategorical x897) x896
            with
              (st578, x898)
            in
            p_assume "assume here" st578 (hrmStoreNode nodeLabel51 x893) x898
  in
  recursive
    let rec9 =
      lam st270.
        lam c32.
          lam c33.
            lam s8.
              match s8 with [ _,
                  _ ] ++ _
              then
                match anon18 st270 c32 c33 (get s8 0) with (st271, x403)
                in
                match splitAt s8 1 with {#label"1" = x404}
                in
                match rec9 st271 c32 c33 x404 with (st272, x405)
                in
                (st272, cons x403 x405)
              else match s8 with [ e10 ]
              then
                match splitAt s8 1 with {#label"1" = x406}
                in
                let slice9 = x406 in
                match anon18 st270 c32 c33 e10 with (st273, x407)
                in
                (st273, [ x407 ])
              else match s8 with ""
              in
              (st270, "")
  in
  let suggestNodeRep =
    lam st573.
      lam msg.
        lam nHosts4.
          lam nodeLabel5.
            let i110 = subi (addi (subi nHosts4 1) 1) 1 in
            rec9
              st573
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
      lam st274.
        lam currentState.
          lam finalState11.
            lam currentAge.
              lam finalAge2.
                lam host.
                  lam nodeLabel.
                    lam embeddedQMatrix11.
                      p_bind
                        st274
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st275.
                           lam x408.
                             match
                               match ltf x408 finalAge2 with true
                               then
                                 match
                                   p_map
                                     st275
                                     (lam x409.
                                        eqi x409 finalState11)
                                     currentState
                                 with
                                   (st276, x410)
                                 in
                                 match
                                   p_traverseSeq
                                     st276
                                     (lam st277.
                                        lam x411.
                                          (st277, x411))
                                     ""
                                 with
                                   (st278, x412)
                                 in
                                 (st278, Bridge1
                                   { success = x410, events = x412 })
                               else match
                                 p_traverseSeq
                                   st275
                                   (lam st279.
                                      lam x413.
                                        p_traverseSeq
                                          st279
                                          (lam st280.
                                             lam x414.
                                               (st280, x414))
                                          x413)
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x4010
                                    then
                                      x4010.transitionProbs
                                    else
                                      let #var"246" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 323:16-323:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x415.
                                           map
                                             (lam x416.
                                                p_pure x416)
                                             x415)
                                        (exit 1))
                               with
                                 (st281, x417)
                               in
                               match
                                 p_map
                                   st281
                                   (lam x418.
                                      lam x419.
                                        mkCategorical (get x418 x419))
                                   x417
                               with
                                 (st282, x420)
                               in
                               match
                                 p_map
                                   st282
                                   (lam x421.
                                      subi (addi x421 1) 1)
                                   currentState
                               with
                                 (st283, x422)
                               in
                               match p_apply st283 x420 x422 with (st284, x423)
                               in
                               match p_assume "assume here" st284 (hrmStoreBranchState nodeLabel host) x423 with (st285, nextState11)
                               in
                               match
                                 p_traverseSeq
                                   st285
                                   (lam st286.
                                      lam x424.
                                        (st286, x424))
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x3910
                                    then
                                      x3910.totalRates
                                    else
                                      let #var"247" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 327:20-327:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x425.
                                           p_pure x425)
                                        (exit 1))
                               with
                                 (st287, x426)
                               in
                               match
                                 p_map
                                   st287
                                   (lam x427.
                                      lam x428.
                                        mkExponential
                                          (addf
                                             (addf (get x427 x428) (mulf (int2float host) 0.))
                                             (mulf (int2float nodeLabel) 0.)))
                                   x426
                               with
                                 (st288, x429)
                               in
                               match
                                 p_map
                                   st288
                                   (lam x430.
                                      subi (addi x430 1) 1)
                                   nextState11
                               with
                                 (st289, x431)
                               in
                               match p_apply st289 x429 x431 with (st290, x432)
                               in
                               match p_assume "assume here" st290 (hrmStoreBranchTime nodeLabel host) x432 with (st291, x433)
                               in
                               match
                                 p_map
                                   st291
                                   (lam x434.
                                      subf x408 x434)
                                   x433
                               with
                                 (st292, x435)
                               in
                               match
                                 sampleHostHistoryRec
                                   st292
                                   nextState11
                                   finalState11
                                   x435
                                   finalAge2
                                   host
                                   nodeLabel
                                   embeddedQMatrix11
                               with
                                 (st293, restOfHistory)
                               in
                               match
                                 p_map
                                   st293
                                   (lam x436.
                                      match x436 with Bridge1 x3710
                                      then
                                        x3710.success
                                      else
                                        let #var"248" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 345:18-345:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st294, x437)
                               in
                               match
                                 p_map
                                   st294
                                   (lam x438.
                                      match x438 with Bridge1 x3810
                                      then
                                        x3810.events
                                      else
                                        let #var"249" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 343:10-343:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st295, x439)
                               in
                               match
                                 cons11
                                   st295
                                   (Event1
                                      { host = host,
                                        toState = nextState11,
                                        eventTime = x408,
                                        fromState = currentState })
                                   x439
                               with
                                 (st296, x440)
                               in
                               (st296, Bridge1
                                 { success = x437, events = x440 })
                             with
                               (st297, x441)
                             in
                             match x441 with Bridge1 x442
                             in
                             match x442 with {success = x443}
                             in
                             match
                               p_map
                                 st297
                                 (lam x444.
                                    lam x445.
                                      Bridge1
                                        { success = x444, events = x445 })
                                 x443
                             with
                               (st298, x446)
                             in
                             match x442 with {events = x447}
                             in
                             p_apply st298 x446 x447)
                        currentAge
    let sampleHostHistoryRec1 =
      lam st299.
        lam currentState1.
          lam finalState12.
            lam currentAge1.
              lam finalAge21.
                lam host1.
                  lam nodeLabel1.
                    lam embeddedQMatrix12.
                      p_bind
                        st299
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st300.
                           lam x448.
                             match
                               match ltf x448 finalAge21 with true
                               then
                                 match
                                   p_map
                                     st300
                                     (lam x449.
                                        lam x450.
                                          eqi x449 x450)
                                     currentState1
                                 with
                                   (st301, x451)
                                 in
                                 match p_apply st301 x451 finalState12 with (st302, x452)
                                 in
                                 match
                                   p_traverseSeq
                                     st302
                                     (lam st303.
                                        lam x453.
                                          (st303, x453))
                                     ""
                                 with
                                   (st304, x454)
                                 in
                                 (st304, Bridge1
                                   { success = x452, events = x454 })
                               else match
                                 p_traverseSeq
                                   st300
                                   (lam st305.
                                      lam x455.
                                        p_traverseSeq
                                          st305
                                          (lam st306.
                                             lam x456.
                                               (st306, x456))
                                          x455)
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x4011
                                    then
                                      x4011.transitionProbs
                                    else
                                      let #var"250" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 323:16-323:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x457.
                                           map
                                             (lam x458.
                                                p_pure x458)
                                             x457)
                                        (exit 1))
                               with
                                 (st307, x459)
                               in
                               match
                                 p_map
                                   st307
                                   (lam x460.
                                      lam x461.
                                        mkCategorical (get x460 x461))
                                   x459
                               with
                                 (st308, x462)
                               in
                               match
                                 p_map
                                   st308
                                   (lam x463.
                                      subi (addi x463 1) 1)
                                   currentState1
                               with
                                 (st309, x464)
                               in
                               match p_apply st309 x462 x464 with (st310, x465)
                               in
                               match p_assume "assume here" st310 (hrmStoreBranchState nodeLabel1 host1) x465 with (st311, nextState12)
                               in
                               match
                                 p_traverseSeq
                                   st311
                                   (lam st312.
                                      lam x466.
                                        (st312, x466))
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x3911
                                    then
                                      x3911.totalRates
                                    else
                                      let #var"251" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 327:20-327:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x467.
                                           p_pure x467)
                                        (exit 1))
                               with
                                 (st313, x468)
                               in
                               match
                                 p_map
                                   st313
                                   (lam x469.
                                      lam x470.
                                        mkExponential
                                          (addf
                                             (addf (get x469 x470) (mulf (int2float host1) 0.))
                                             (mulf (int2float nodeLabel1) 0.)))
                                   x468
                               with
                                 (st314, x471)
                               in
                               match
                                 p_map
                                   st314
                                   (lam x472.
                                      subi (addi x472 1) 1)
                                   nextState12
                               with
                                 (st315, x473)
                               in
                               match p_apply st315 x471 x473 with (st316, x474)
                               in
                               match p_assume "assume here" st316 (hrmStoreBranchTime nodeLabel1 host1) x474 with (st317, x475)
                               in
                               match
                                 p_map
                                   st317
                                   (lam x476.
                                      subf x448 x476)
                                   x475
                               with
                                 (st318, x477)
                               in
                               match
                                 sampleHostHistoryRec1
                                   st318
                                   nextState12
                                   finalState12
                                   x477
                                   finalAge21
                                   host1
                                   nodeLabel1
                                   embeddedQMatrix12
                               with
                                 (st319, restOfHistory1)
                               in
                               match
                                 p_map
                                   st319
                                   (lam x478.
                                      match x478 with Bridge1 x3711
                                      then
                                        x3711.success
                                      else
                                        let #var"252" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 345:18-345:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st320, x479)
                               in
                               match
                                 p_map
                                   st320
                                   (lam x480.
                                      match x480 with Bridge1 x3811
                                      then
                                        x3811.events
                                      else
                                        let #var"253" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 343:10-343:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st321, x481)
                               in
                               match
                                 cons11
                                   st321
                                   (Event1
                                      { host = host1,
                                        toState = nextState12,
                                        eventTime = x448,
                                        fromState = currentState1 })
                                   x481
                               with
                                 (st322, x482)
                               in
                               (st322, Bridge1
                                 { success = x479, events = x482 })
                             with
                               (st323, x483)
                             in
                             match x483 with Bridge1 x484
                             in
                             match x484 with {success = x485}
                             in
                             match
                               p_map
                                 st323
                                 (lam x486.
                                    lam x487.
                                      Bridge1
                                        { success = x486, events = x487 })
                                 x485
                             with
                               (st324, x488)
                             in
                             match x484 with {events = x489}
                             in
                             p_apply st324 x488 x489)
                        currentAge1
  in
  let anon19 = lam x892.
      addi x892 1 in
  recursive
    let rec36 =
      lam i16.
        lam acc18.
          match geqi i16 0 with true
          then
            rec36 (subi i16 1) (cons (anon19 i16) acc18)
          else
            acc18
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
    lam st561.
      lam startRep1.
        lam finalRep12.
          lam startAge1.
            lam finalAge33.
              lam nodeLabel12.
                lam modelParams31.
                  lam x872.
                    let startState1 = get startRep1 (subi x872 1) in
                    let embeddedQMatrix51 =
                      match modelParams31 with ModelParams1 x1042
                      then
                        x1042.embeddedQMatrix
                      else
                        let #var"2118" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 201:4-201:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st561
                        (lam st562.
                           lam x873.
                             (st562, x873))
                        (match embeddedQMatrix51 with EmbeddedMarkovChainMatrix1 x1082
                         then
                           x1082.totalRates
                         else
                           let #var"2115" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 292:18-292:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x874.
                                p_pure x874)
                             (exit 1))
                    with
                      (st563, x875)
                    in
                    match
                      p_map
                        st563
                        (lam x876.
                           lam x877.
                             mkExponential
                               (addf
                                  (addf (get x876 x877) (mulf (int2float x872) 0.))
                                  (mulf (int2float nodeLabel12) 0.)))
                        x875
                    with
                      (st564, x878)
                    in
                    match
                      p_map
                        st564
                        (lam x879.
                           subi (addi x879 1) 1)
                        startState1
                    with
                      (st565, x880)
                    in
                    match p_apply st565 x878 x880 with (st566, x882)
                    in
                    match p_assume "assume here" st566 (hrmStoreBranchTime nodeLabel12 x872) x882 with (st567, x883)
                    in
                    match
                      p_map
                        st567
                        (lam x884.
                           subf startAge1 x884)
                        x883
                    with
                      (st568, x885)
                    in
                    match
                      sampleHostHistoryRec
                        st568
                        startState1
                        (get finalRep12 (subi x872 1))
                        x885
                        finalAge33
                        x872
                        nodeLabel12
                        embeddedQMatrix51
                    with
                      (st569, bridge1)
                    in
                    match
                      p_map
                        st569
                        (lam x886.
                           match x886 with Bridge1 x1072
                           then
                             x1072.success
                           else
                             let #var"2116" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 304:19-304:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge1
                    with
                      (st570, x887)
                    in
                    match bool2real st570 x887 with (st571, x888)
                    in
                    let st572 =
                      p_weight
                        st571
                        (hrmStoreBridgeSuppWeight nodeLabel12 x872)
                        (lam x890.
                           externalLog
                             (addf
                                (addf x890 (mulf (int2float x872) 0.))
                                (mulf (int2float nodeLabel12) 0.)))
                        x888
                    in
                    let foo51 = {} in
                    p_map
                      st572
                      (lam x889.
                         match x889 with Bridge1 x1062
                         then
                           x1062.events
                         else
                           let #var"2117" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 305:9-305:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge1
  in
  let anon21 =
    lam st549.
      lam startRep.
        lam finalRep11.
          lam startAge.
            lam finalAge32.
              lam nodeLabel11.
                lam modelParams3.
                  lam x854.
                    let startState = get startRep (subi x854 1) in
                    let embeddedQMatrix5 =
                      match modelParams3 with ModelParams1 x1041
                      then
                        x1041.embeddedQMatrix
                      else
                        let #var"2114" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 201:4-201:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st549
                        (lam st550.
                           lam x855.
                             (st550, x855))
                        (match embeddedQMatrix5 with EmbeddedMarkovChainMatrix1 x1081
                         then
                           x1081.totalRates
                         else
                           let #var"2111" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 292:18-292:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x856.
                                p_pure x856)
                             (exit 1))
                    with
                      (st551, x857)
                    in
                    match
                      p_map
                        st551
                        (lam x858.
                           lam x859.
                             mkExponential
                               (addf
                                  (addf (get x858 x859) (mulf (int2float x854) 0.))
                                  (mulf (int2float nodeLabel11) 0.)))
                        x857
                    with
                      (st552, x860)
                    in
                    match
                      p_map
                        st552
                        (lam x861.
                           subi (addi x861 1) 1)
                        startState
                    with
                      (st553, x862)
                    in
                    match p_apply st553 x860 x862 with (st554, x863)
                    in
                    match p_assume "assume here" st554 (hrmStoreBranchTime nodeLabel11 x854) x863 with (st555, x864)
                    in
                    match
                      p_map
                        st555
                        (lam x865.
                           subf startAge x865)
                        x864
                    with
                      (st556, x866)
                    in
                    match
                      sampleHostHistoryRec1
                        st556
                        startState
                        (get finalRep11 (subi x854 1))
                        x866
                        finalAge32
                        x854
                        nodeLabel11
                        embeddedQMatrix5
                    with
                      (st557, bridge)
                    in
                    match
                      p_map
                        st557
                        (lam x867.
                           match x867 with Bridge1 x1071
                           then
                             x1071.success
                           else
                             let #var"2112" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 304:19-304:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge
                    with
                      (st558, x868)
                    in
                    match bool2real st558 x868 with (st559, x869)
                    in
                    let st560 =
                      p_weight
                        st559
                        (hrmStoreBridgeSuppWeight nodeLabel11 x854)
                        (lam x871.
                           externalLog
                             (addf
                                (addf x871 (mulf (int2float x854) 0.))
                                (mulf (int2float nodeLabel11) 0.)))
                        x869
                    in
                    let foo5 = {} in
                    p_map
                      st560
                      (lam x870.
                         match x870 with Bridge1 x1061
                         then
                           x1061.events
                         else
                           let #var"2113" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 305:9-305:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge
  in
  recursive
    let rec10 =
      lam st325.
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
                        match anon20 st325 c34 c35 c36 c37 c38 c39 (get s9 0) with (st326, x490)
                        in
                        match splitAt s9 1 with {#label"1" = x491}
                        in
                        match rec10 st326 c34 c35 c36 c37 c38 c39 x491 with (st327, x492)
                        in
                        (st327, cons x490 x492)
                      else match s9 with [ e11 ]
                      then
                        match splitAt s9 1 with {#label"1" = x493}
                        in
                        let slice10 = x493 in
                        match anon20 st325 c34 c35 c36 c37 c38 c39 e11 with (st328, x494)
                        in
                        (st328, [ x494 ])
                      else match s9 with ""
                      in
                      (st325, "")
    let rec13 =
      lam st329.
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
                          anon21 st329 c40 c41 c42 c43 c44 c45 (get s10 0)
                        with
                          (st330, x495)
                        in
                        match splitAt s10 1 with {#label"1" = x496}
                        in
                        match rec13 st330 c40 c41 c42 c43 c44 c45 x496 with (st331, x497)
                        in
                        (st331, cons x495 x497)
                      else match s10 with [ e12 ]
                      then
                        match splitAt s10 1 with {#label"1" = x498}
                        in
                        let slice11 = x498 in
                        match anon21 st329 c40 c41 c42 c43 c44 c45 e12 with (st332, x499)
                        in
                        (st332, [ x499 ])
                      else match s10 with ""
                      in
                      (st329, "")
  in
  let anon22 =
    lam h2.
      lam x853.
        lti
          (match
             isNaN1
               (match h2 with Event1 x1091
                then
                  x1091.eventTime
                else
                  let #var"2107" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 241:12-241:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             negi 1
           else match
             isNaN1
               (match x853 with Event1 x1131
                then
                  x1131.eventTime
                else
                  let #var"2108" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 244:12-244:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             1
           else match
             geqf
               (match h2 with Event1 x1141
                then
                  x1141.eventTime
                else
                  let #var"2109" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 247:6-247:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
                  in
                  exit 1)
               (match x853 with Event1 x1151
                then
                  x1151.eventTime
                else
                  let #var"2110" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 247:25-247:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
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
                match splitAt seq1 1 with {#label"1" = x500}
                in
                let seq2 = x500 in
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
                match splitAt seq11 1 with {#label"1" = x501}
                in
                let seq21 = x501 in
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
                match splitAt seq12 1 with {#label"1" = x502}
                in
                let seq22 = x502 in
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
                match splitAt seq13 1 with {#label"1" = x503}
                in
                let seq23 = x503 in
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
      lam st333.
        lam seq31.
          p_map
            st333
            (lam x504.
               match null x504 with true
               then
                 x504
               else
                 let h1 = head x504 in
                 let lr1 = work14 h1 "" "" (reverse (tail x504)) in
                 match lr1 with (#var"X6",)
                 in
                 match lr1 with {#label"1" = #var"X7"}
                 in
                 concat (quickSort #var"X6") (cons h1 (quickSort #var"X7")))
            seq31
  in
  recursive
    let rec212 =
      lam st334.
        lam c50.
          lam c51.
            lam c52.
              lam c53.
                lam c54.
                  lam c55.
                    lam acc19.
                      lam s213.
                        match s213 with [ _ ] ++ _
                        then
                          let x505 = get s213 0 in
                          match
                            p_map
                              st334
                              (lam x506.
                                 lam x507.
                                   addf x506 x507)
                              acc19
                          with
                            (st335, x508)
                          in
                          match
                            hostIndepLikelihood
                              st335
                              1
                              (get c50 (subi x505 1))
                              (get c51 (subi x505 1))
                              c52
                              c53
                              (get c55 (subi x505 1))
                              (match c54 with ModelParams1 x1191
                               then
                                 x1191.embeddedQMatrix
                               else
                                 let #var"254" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st336, x509)
                          in
                          match p_apply st336 x508 x509 with (st337, x510)
                          in
                          match splitAt s213 1 with {#label"1" = x511}
                          in
                          rec212 st337 c50 c51 c52 c53 c54 c55 x510 x511
                        else match s213 with ""
                        in
                        (st334, acc19)
    let rec213 =
      lam st338.
        lam c56.
          lam c57.
            lam c58.
              lam c59.
                lam c60.
                  lam c61.
                    lam acc20.
                      lam s214.
                        match s214 with [ _ ] ++ _
                        then
                          let x512 = get s214 0 in
                          match
                            p_map
                              st338
                              (lam x513.
                                 lam x514.
                                   addf x513 x514)
                              acc20
                          with
                            (st339, x515)
                          in
                          match
                            hostIndepLikelihood2
                              st339
                              1
                              (get c56 (subi x512 1))
                              (get c57 (subi x512 1))
                              c58
                              c59
                              (get c61 (subi x512 1))
                              (match c60 with ModelParams1 x1192
                               then
                                 x1192.embeddedQMatrix
                               else
                                 let #var"255" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st340, x516)
                          in
                          match p_apply st340 x515 x516 with (st341, x517)
                          in
                          match splitAt s214 1 with {#label"1" = x518}
                          in
                          rec213 st341 c56 c57 c58 c59 c60 c61 x517 x518
                        else match s214 with ""
                        in
                        (st338, acc20)
  in
  let anon23 = lam x852.
      addi x852 1 in
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
    let rec214 =
      lam st342.
        lam acc23.
          lam s215.
            match s215 with [ _ ] ++ _
            then
              match
                p_map
                  st342
                  (lam x519.
                     lam x520.
                       addf x519 x520)
                  acc23
              with
                (st343, x521)
              in
              match p_apply st343 x521 (get s215 0) with (st344, x522)
              in
              match splitAt s215 1 with {#label"1" = x523}
              in
              rec214 st344 x522 x523
            else match s215 with ""
            in
            (st342, acc23)
  in
  let fold2 =
    lam st547.
      lam init11.
        lam seq51.
          match seq51 with [ _ ] ++ _
          then
            match
              p_map
                st547
                (lam x849.
                   addf init11 x849)
                (get seq51 0)
            with
              (st548, x850)
            in
            match splitAt seq51 1 with {#label"1" = x851}
            in
            rec214 st548 x850 x851
          else match seq51 with ""
          in
          (st547, p_pure init11)
  in
  recursive
    let rec215 =
      lam st345.
        lam c62.
          lam acc24.
            lam s216.
              match s216 with [ _ ] ++ _
              then
                match acc24 with (field2, field3)
                in
                match
                  match field3 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st345
                        (lam x524.
                           addi x524 1)
                        (get field3 0)
                    with
                      (st346, x525)
                    in
                    match mtxGet1 st346 x525 (addi (get s216 0) 1) c62 with (st347, x526)
                    in
                    match log11 st347 x526 with (st348, x527)
                    in
                    match splitAt field3 1 with {#label"1" = x528}
                    in
                    (st348, (snoc field2 x527, x528))
                  else
                    let x529 = error "foldl2: Cannot happen!" in
                    match x529 with (x530,)
                    in
                    match x529 with {#label"1" = x531}
                    in
                    (st345, (map (lam x532.
                         p_pure x532) x530, map (lam x533.
                         p_pure x533) x531))
                with
                  (st349, x534)
                in
                match splitAt s216 1 with {#label"1" = x535}
                in
                rec215 st349 c62 x534 x535
              else match s216 with ""
              in
              (st345, acc24)
    let rec216 =
      lam st350.
        lam c63.
          lam acc25.
            lam s217.
              match s217 with [ _ ] ++ _
              then
                match acc25 with (field4, field5)
                in
                match
                  match field5 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st350
                        (lam x536.
                           addi x536 1)
                        (get field5 0)
                    with
                      (st351, x537)
                    in
                    match
                      p_map
                        st351
                        (lam x538.
                           addi x538 1)
                        (get s217 0)
                    with
                      (st352, x539)
                    in
                    match mtxGet2 st352 x537 x539 c63 with (st353, x540)
                    in
                    match log11 st353 x540 with (st354, x541)
                    in
                    match splitAt field5 1 with {#label"1" = x542}
                    in
                    (st354, (snoc field4 x541, x542))
                  else
                    let x543 = error "foldl2: Cannot happen!" in
                    match x543 with (x544,)
                    in
                    match x543 with {#label"1" = x545}
                    in
                    (st350, (map (lam x546.
                         p_pure x546) x544, map (lam x547.
                         p_pure x547) x545))
                with
                  (st355, x548)
                in
                match splitAt s217 1 with {#label"1" = x549}
                in
                rec216 st355 c63 x548 x549
              else match s217 with ""
              in
              (st350, acc25)
  in
  recursive
    let rec217 =
      lam st356.
        lam c64.
          lam acc26.
            lam s218.
              match s218 with [ _ ] ++ _
              then
                match acc26 with (field6, field7)
                in
                match
                  match field7 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st356
                        (lam x550.
                           addi x550 1)
                        (get s218 0)
                    with
                      (st357, x551)
                    in
                    match mtxGet1 st357 x551 (addi (get field7 0) 1) c64 with (st358, x552)
                    in
                    match log11 st358 x552 with (st359, x553)
                    in
                    match splitAt field7 1 with {#label"1" = x554}
                    in
                    (st359, (snoc field6 x553, x554))
                  else
                    let x555 = error "foldl2: Cannot happen!" in
                    match x555 with (x556,)
                    in
                    match x555 with {#label"1" = x557}
                    in
                    (st356, (map (lam x558.
                         p_pure x558) x556, x557))
                with
                  (st360, x559)
                in
                match splitAt s218 1 with {#label"1" = x560}
                in
                rec217 st360 c64 x559 x560
              else match s218 with ""
              in
              (st356, acc26)
    let rec218 =
      lam st361.
        lam c65.
          lam acc27.
            lam s219.
              match s219 with [ _ ] ++ _
              then
                match acc27 with (field8, field9)
                in
                match
                  match field9 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st361
                        (lam x561.
                           addi x561 1)
                        (get s219 0)
                    with
                      (st362, x562)
                    in
                    match
                      p_map
                        st362
                        (lam x563.
                           addi x563 1)
                        (get field9 0)
                    with
                      (st363, x564)
                    in
                    match mtxGet2 st363 x562 x564 c65 with (st364, x565)
                    in
                    match log11 st364 x565 with (st365, x566)
                    in
                    match splitAt field9 1 with {#label"1" = x567}
                    in
                    (st365, (snoc field8 x566, x567))
                  else
                    let x568 = error "foldl2: Cannot happen!" in
                    match x568 with (x569,)
                    in
                    match x568 with {#label"1" = x570}
                    in
                    (st361, (map (lam x571.
                         p_pure x571) x569, map (lam x572.
                         p_pure x572) x570))
                with
                  (st366, x573)
                in
                match splitAt s219 1 with {#label"1" = x574}
                in
                rec218 st366 c65 x573 x574
              else match s219 with ""
              in
              (st361, acc27)
  in
  recursive
    let sampleTreeHistory =
      lam st367.
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 115:14-115:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 121:6-121:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                            in
                            exit 1
                        in
                        match
                          rec10
                            st367
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
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 123:6-123:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create12 (addi (subi nHosts 1) 1))
                        with
                          (st368, unorderedBranch)
                        in
                        match paste0 st368 unorderedBranch with (st369, x575)
                        in
                        match quickSort1 st369 x575 with (st370, orderedEvents)
                        in
                        match length13 st370 orderedEvents with (st371, nEvents4)
                        in
                        match
                          allTimesValidBranch st371 parentRep orderedEvents 1 nEvents4 nHosts
                        with
                          (st372, x576)
                        in
                        match
                          p_bind
                            st372
                            hrmStoreSubmodel
                            (hrmInit {})
                            (lam st373.
                               lam x577.
                                 match
                                   match x577 with true
                                   then
                                     let s220 = create13 (addi (subi (length11 unorderedBranch) 1) 1)
                                     in
                                     match
                                       match s220 with [ _ ] ++ _
                                       then
                                         let x578 = get s220 0 in
                                         match
                                           hostIndepLikelihood
                                             st373
                                             1
                                             (get parentRep (subi x578 1))
                                             (get rep1 (subi x578 1))
                                             parentAge
                                             finalAge3
                                             (get unorderedBranch (subi x578 1))
                                             (match modelParams11 with ModelParams1 x1193
                                              then
                                                x1193.embeddedQMatrix
                                              else
                                                let #var"257" =
                                                  print
                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                                in
                                                exit 1)
                                         with
                                           (st374, x579)
                                         in
                                         match
                                           p_map
                                             st374
                                             (lam x580.
                                                addf 0. x580)
                                             x579
                                         with
                                           (st375, x581)
                                         in
                                         match splitAt s220 1 with {#label"1" = x582}
                                         in
                                         rec212
                                           st375
                                           parentRep
                                           rep1
                                           parentAge
                                           finalAge3
                                           modelParams11
                                           unorderedBranch
                                           x581
                                           x582
                                       else match s220 with ""
                                       in
                                       (st373, p_pure 0.)
                                     with
                                       (st376, x583)
                                     in
                                     match
                                       p_map
                                         st376
                                         (lam x584.
                                            lam x585.
                                              subf x584 x585)
                                         x583
                                     with
                                       (st377, x586)
                                     in
                                     match
                                       match geqi (length parentRep) (length rep1) with true
                                       then
                                         let acc28 = ("", parentRep) in
                                         match
                                           match rep1 with [ _ ] ++ _
                                           then
                                             match acc28 with (field10, field11)
                                             in
                                             match
                                               match field11 with [ _ ] ++ _
                                               then
                                                 match
                                                   p_map
                                                     st377
                                                     (lam x587.
                                                        addi x587 1)
                                                     (get field11 0)
                                                 with
                                                   (st378, x588)
                                                 in
                                                 match
                                                   mtxGet1 st378 x588 (addi (get rep1 0) 1) branchKernel
                                                 with
                                                   (st379, x589)
                                                 in
                                                 match log11 st379 x589 with (st380, x590)
                                                 in
                                                 match splitAt field11 1 with {#label"1" = x591}
                                                 in
                                                 (st380, (snoc field10 x590, x591))
                                               else
                                                 let x592 = error "foldl2: Cannot happen!" in
                                                 match x592 with (x593,)
                                                 in
                                                 match x592 with {#label"1" = x594}
                                                 in
                                                 (st377, (map
                                                   (lam x595.
                                                      p_pure x595)
                                                   x593, map
                                                   (lam x596.
                                                      p_pure x596)
                                                   x594))
                                             with
                                               (st381, x597)
                                             in
                                             match splitAt rep1 1 with {#label"1" = x598}
                                             in
                                             rec215 st381 branchKernel x597 x598
                                           else match rep1 with ""
                                           in
                                           (st377, acc28)
                                         with
                                           (st382, x599)
                                         in
                                         match x599 with (field12, field13)
                                         in
                                         (st382, field12)
                                       else
                                         let acc29 = ("", rep1) in
                                         match
                                           match parentRep with [ _ ] ++ _
                                           then
                                             match acc29 with (field14, field15)
                                             in
                                             match
                                               match field15 with [ _ ] ++ _
                                               then
                                                 match
                                                   p_map
                                                     st377
                                                     (lam x600.
                                                        addi x600 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st383, x601)
                                                 in
                                                 match
                                                   mtxGet1 st383 x601 (addi (get field15 0) 1) branchKernel
                                                 with
                                                   (st384, x602)
                                                 in
                                                 match log11 st384 x602 with (st385, x603)
                                                 in
                                                 match splitAt field15 1 with {#label"1" = x604}
                                                 in
                                                 (st385, (snoc field14 x603, x604))
                                               else
                                                 let x605 = error "foldl2: Cannot happen!" in
                                                 match x605 with (x606,)
                                                 in
                                                 match x605 with {#label"1" = x607}
                                                 in
                                                 (st377, (map
                                                   (lam x608.
                                                      p_pure x608)
                                                   x606, x607))
                                             with
                                               (st386, x609)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x610}
                                             in
                                             rec217 st386 branchKernel x609 x610
                                           else match parentRep with ""
                                           in
                                           (st377, acc29)
                                         with
                                           (st387, x611)
                                         in
                                         match x611 with (field16, field17)
                                         in
                                         (st387, field16)
                                     with
                                       (st388, x612)
                                     in
                                     match fold2 st388 0. x612 with (st389, x613)
                                     in
                                     match p_apply st389 x586 x613 with (st390, x614)
                                     in
                                     match
                                       p_bind
                                         st390
                                         hrmStoreSubmodel
                                         (hrmInit {})
                                         (lam st391.
                                            lam x615.
                                              match gti 1 x615 with true
                                              then
                                                match
                                                  getTotalRate st391 parentRep modelParams11 nHosts
                                                with
                                                  (st392, x616)
                                                in
                                                p_map
                                                  st392
                                                  (lam x617.
                                                     mulf (negf (subf parentAge finalAge3)) x617)
                                                  x616
                                              else match
                                                p_map
                                                  st391
                                                  (lam x618.
                                                     get x618 (subi 1 1))
                                                  orderedEvents
                                              with
                                                (st393, nextEvent2)
                                              in
                                              match
                                                p_map
                                                  st393
                                                  (lam x619.
                                                     match x619 with Event1 x3110
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
                                                (st394, newAge2)
                                              in
                                              match
                                                getTotalRate st394 parentRep modelParams11 nHosts
                                              with
                                                (st395, totalLeavingRate12)
                                              in
                                              match
                                                p_map
                                                  st395
                                                  (lam x620.
                                                     match x620 with Event1 x1323
                                                     then
                                                       x1323.host
                                                     else
                                                       let #var"259" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st396, hostIndex12)
                                              in
                                              match
                                                p_map
                                                  st396
                                                  (lam x621.
                                                     lam x622.
                                                       lam st397.
                                                         match
                                                           gti
                                                             (match x621 with Event1 x1303
                                                              then
                                                                x1303.fromState
                                                              else
                                                                let #var"260" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x622
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st397 parentRep hostIndex12 modelParams11
                                                         else
                                                           getGainRate2 st397 parentRep hostIndex12 modelParams11)
                                                  nextEvent2
                                              with
                                                (st398, x623)
                                              in
                                              match
                                                p_map
                                                  st398
                                                  (lam x624.
                                                     match x624 with Event1 x1313
                                                     then
                                                       x1313.toState
                                                     else
                                                       let #var"261" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st399, x625)
                                              in
                                              match
                                                p_subApply st399 hrmStoreSubmodel (hrmInit {}) x623 x625
                                              with
                                                (st400, x626)
                                              in
                                              match p_join st400 x626 with (st401, x627)
                                              in
                                              match
                                                p_map
                                                  st401
                                                  (lam x628.
                                                     lam x629.
                                                       divf x628 x629)
                                                  x627
                                              with
                                                (st402, x630)
                                              in
                                              match p_apply st402 x630 totalLeavingRate12 with (st403, x631)
                                              in
                                              match log11 st403 x631 with (st404, x632)
                                              in
                                              match
                                                p_map
                                                  st404
                                                  (lam x633.
                                                     lam x634.
                                                       lam x635.
                                                         addf (subf x633 x634) x635)
                                                  x632
                                              with
                                                (st405, x636)
                                              in
                                              match
                                                p_map
                                                  st405
                                                  (lam x637.
                                                     lam x638.
                                                       mulf (subf parentAge x637) x638)
                                                  newAge2
                                              with
                                                (st406, x639)
                                              in
                                              match p_apply st406 x639 totalLeavingRate12 with (st407, x640)
                                              in
                                              match p_apply st407 x636 x640 with (st408, x641)
                                              in
                                              match
                                                updateRepertoire st408 parentRep nextEvent2 nHosts
                                              with
                                                (st409, x642)
                                              in
                                              match
                                                fullModelWeight
                                                  st409
                                                  (addi 1 1)
                                                  x642
                                                  rep1
                                                  newAge2
                                                  finalAge3
                                                  orderedEvents
                                                  x615
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st410, x643)
                                              in
                                              p_apply st410 x641 x643)
                                         nEvents4
                                     with
                                       (st411, x644)
                                     in
                                     (st411, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = x614,
                                         logModelDensity = x644,
                                         success = true })
                                   else
                                     (st373, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = p_pure (log1 0.),
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st412, x645)
                                 in
                                 match x645 with CorrectedBranchSample1 x646
                                 in
                                 match x646 with {history = x647}
                                 in
                                 match
                                   p_map
                                     st412
                                     (lam x648.
                                        lam x649.
                                          lam x650.
                                            match x646 with {success = x651}
                                            in
                                            CorrectedBranchSample1
                                              { history = x648,
                                                logSamplingDensity = x649,
                                                logModelDensity = x650,
                                                success = x651 })
                                     x647
                                 with
                                   (st413, x652)
                                 in
                                 match x646 with {logSamplingDensity = x653}
                                 in
                                 match p_apply st413 x652 x653 with (st414, x654)
                                 in
                                 match x646 with {logModelDensity = x655}
                                 in
                                 p_apply st414 x654 x655)
                            x576
                        with
                          (st415, branchSample)
                        in
                        match
                          p_map
                            st415
                            (lam x656.
                               lam x657.
                                 mulf
                                   (subf
                                      (match x656 with CorrectedBranchSample1 x4610
                                       then
                                         x4610.logModelDensity
                                       else
                                         let #var"262" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:15-129:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x657)
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
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:90-129:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1))
                                         0.)))
                            branchSample
                        with
                          (st416, x658)
                        in
                        match
                          p_map
                            st416
                            (lam x659.
                               match x659 with CorrectedBranchSample1 x4710
                               then
                                 x4710.logSamplingDensity
                               else
                                 let #var"264" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:46-129:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st417, x660)
                        in
                        match p_apply st417 x658 x660 with (st418, x661)
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
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:90-129:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1) in
                        let st419 =
                          p_weight
                            st418
                            (hrmStoreLikrWeight nl)
                            (/-temp-/lam x664.
                               x664)
                            x661
                        in
                        let foo = {} in
                        match
                          p_map
                            st419
                            (lam x662.
                               match x662 with CorrectedBranchSample1 x4510
                               then
                                 x4510.history
                               else
                                 let #var"265" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 135:16-135:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st420, x663)
                        in
                        (st420, HistoryLeaf
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
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 132:12-132:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 133:14-133:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            history = x663,
                            repertoire = rep1 })
                      else match
                        mtxElemMul
                          st367
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 138:34-138:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                             in
                             p_pure (exit 1))
                          preorderMsg
                      with
                        (st421, samplingProb)
                      in
                      match
                        suggestNodeRep
                          st421
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 139:51-139:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                             in
                             exit 1)
                      with
                        (st422, rep2)
                      in
                      match any1 st422 rep2 with (st423, x665)
                      in
                      match bool2real st423 x665 with (st424, x666)
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
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 141:43-141:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1) in
                      let st425 =
                        p_weight
                          st424
                          (hrmStoreNodeSuppWeight nl)
                          (lam x772.
                             externalLog
                               (addf
                                  x772
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
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 141:43-141:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1))
                                     0.)))
                          x666
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
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 149:6-149:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                          in
                          exit 1
                      in
                      match
                        rec13
                          st425
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 151:6-151:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                             in
                             exit 1)
                          modelParams11
                          (create12 (addi (subi nHosts 1) 1))
                      with
                        (st426, unorderedBranch1)
                      in
                      match paste0 st426 unorderedBranch1 with (st427, x667)
                      in
                      match quickSort1 st427 x667 with (st428, orderedEvents1)
                      in
                      match length13 st428 orderedEvents1 with (st429, nEvents41)
                      in
                      match
                        allTimesValidBranch st429 parentRep orderedEvents1 1 nEvents41 nHosts
                      with
                        (st430, x668)
                      in
                      match
                        p_bind
                          st430
                          hrmStoreSubmodel
                          (hrmInit {})
                          (lam st431.
                             lam x669.
                               match
                                 match x669 with true
                                 then
                                   let s221 = create13 (addi (subi (length11 unorderedBranch1) 1) 1)
                                   in
                                   match
                                     match s221 with [ _ ] ++ _
                                     then
                                       let x670 = get s221 0 in
                                       match
                                         hostIndepLikelihood2
                                           st431
                                           1
                                           (get parentRep (subi x670 1))
                                           (get rep2 (subi x670 1))
                                           parentAge
                                           finalAge31
                                           (get unorderedBranch1 (subi x670 1))
                                           (match modelParams11 with ModelParams1 x1194
                                            then
                                              x1194.embeddedQMatrix
                                            else
                                              let #var"273" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                              in
                                              exit 1)
                                       with
                                         (st432, x671)
                                       in
                                       match
                                         p_map
                                           st432
                                           (lam x672.
                                              addf 0. x672)
                                           x671
                                       with
                                         (st433, x673)
                                       in
                                       match splitAt s221 1 with {#label"1" = x674}
                                       in
                                       rec213
                                         st433
                                         parentRep
                                         rep2
                                         parentAge
                                         finalAge31
                                         modelParams11
                                         unorderedBranch1
                                         x673
                                         x674
                                     else match s221 with ""
                                     in
                                     (st431, p_pure 0.)
                                   with
                                     (st434, x675)
                                   in
                                   match
                                     p_map
                                       st434
                                       (lam x676.
                                          lam x677.
                                            subf x676 x677)
                                       x675
                                   with
                                     (st435, x678)
                                   in
                                   match
                                     match geqi (length parentRep) (length rep2) with true
                                     then
                                       let acc30 = ("", parentRep) in
                                       match
                                         match rep2 with [ _ ] ++ _
                                         then
                                           match acc30 with (field18, field19)
                                           in
                                           match
                                             match field19 with [ _ ] ++ _
                                             then
                                               match
                                                 p_map
                                                   st435
                                                   (lam x679.
                                                      addi x679 1)
                                                   (get field19 0)
                                               with
                                                 (st436, x680)
                                               in
                                               match
                                                 p_map
                                                   st436
                                                   (lam x681.
                                                      addi x681 1)
                                                   (get rep2 0)
                                               with
                                                 (st437, x682)
                                               in
                                               match mtxGet2 st437 x680 x682 branchKernel with (st438, x683)
                                               in
                                               match log11 st438 x683 with (st439, x684)
                                               in
                                               match splitAt field19 1 with {#label"1" = x685}
                                               in
                                               (st439, (snoc field18 x684, x685))
                                             else
                                               let x686 = error "foldl2: Cannot happen!" in
                                               match x686 with (x687,)
                                               in
                                               match x686 with {#label"1" = x688}
                                               in
                                               (st435, (map
                                                 (lam x689.
                                                    p_pure x689)
                                                 x687, map
                                                 (lam x690.
                                                    p_pure x690)
                                                 x688))
                                           with
                                             (st440, x691)
                                           in
                                           match splitAt rep2 1 with {#label"1" = x692}
                                           in
                                           rec216 st440 branchKernel x691 x692
                                         else match rep2 with ""
                                         in
                                         (st435, acc30)
                                       with
                                         (st441, x693)
                                       in
                                       match x693 with (field20, field21)
                                       in
                                       (st441, field20)
                                     else
                                       let acc33 = ("", rep2) in
                                       match
                                         match parentRep with [ _ ] ++ _
                                         then
                                           match acc33 with (field22, field23)
                                           in
                                           match
                                             match field23 with [ _ ] ++ _
                                             then
                                               match
                                                 p_map
                                                   st435
                                                   (lam x694.
                                                      addi x694 1)
                                                   (get parentRep 0)
                                               with
                                                 (st442, x695)
                                               in
                                               match
                                                 p_map
                                                   st442
                                                   (lam x696.
                                                      addi x696 1)
                                                   (get field23 0)
                                               with
                                                 (st443, x697)
                                               in
                                               match mtxGet2 st443 x695 x697 branchKernel with (st444, x698)
                                               in
                                               match log11 st444 x698 with (st445, x699)
                                               in
                                               match splitAt field23 1 with {#label"1" = x700}
                                               in
                                               (st445, (snoc field22 x699, x700))
                                             else
                                               let x701 = error "foldl2: Cannot happen!" in
                                               match x701 with (x702,)
                                               in
                                               match x701 with {#label"1" = x703}
                                               in
                                               (st435, (map
                                                 (lam x704.
                                                    p_pure x704)
                                                 x702, map
                                                 (lam x705.
                                                    p_pure x705)
                                                 x703))
                                           with
                                             (st446, x706)
                                           in
                                           match splitAt parentRep 1 with {#label"1" = x707}
                                           in
                                           rec218 st446 branchKernel x706 x707
                                         else match parentRep with ""
                                         in
                                         (st435, acc33)
                                       with
                                         (st447, x708)
                                       in
                                       match x708 with (field24, field25)
                                       in
                                       (st447, field24)
                                   with
                                     (st448, x709)
                                   in
                                   match fold2 st448 0. x709 with (st449, x710)
                                   in
                                   match p_apply st449 x678 x710 with (st450, x711)
                                   in
                                   match
                                     p_bind
                                       st450
                                       hrmStoreSubmodel
                                       (hrmInit {})
                                       (lam st451.
                                          lam x712.
                                            match gti 1 x712 with true
                                            then
                                              match
                                                getTotalRate st451 parentRep modelParams11 nHosts
                                              with
                                                (st452, x713)
                                              in
                                              p_map
                                                st452
                                                (lam x714.
                                                   mulf (negf (subf parentAge finalAge31)) x714)
                                                x713
                                            else match
                                              p_map
                                                st451
                                                (lam x715.
                                                   get x715 (subi 1 1))
                                                orderedEvents1
                                            with
                                              (st453, nextEvent3)
                                            in
                                            match
                                              p_map
                                                st453
                                                (lam x716.
                                                   match x716 with Event1 x3111
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
                                              (st454, newAge3)
                                            in
                                            match
                                              getTotalRate st454 parentRep modelParams11 nHosts
                                            with
                                              (st455, totalLeavingRate13)
                                            in
                                            match
                                              p_map
                                                st455
                                                (lam x717.
                                                   match x717 with Event1 x1324
                                                   then
                                                     x1324.host
                                                   else
                                                     let #var"275" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st456, hostIndex13)
                                            in
                                            match
                                              p_map
                                                st456
                                                (lam x718.
                                                   lam x719.
                                                     lam st457.
                                                       match
                                                         gti
                                                           (match x718 with Event1 x1304
                                                            then
                                                              x1304.fromState
                                                            else
                                                              let #var"276" =
                                                                print
                                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                              in
                                                              exit 1)
                                                           x719
                                                       with
                                                         true
                                                       then
                                                         getLossRate2 st457 parentRep hostIndex13 modelParams11
                                                       else
                                                         getGainRate2 st457 parentRep hostIndex13 modelParams11)
                                                nextEvent3
                                            with
                                              (st458, x720)
                                            in
                                            match
                                              p_map
                                                st458
                                                (lam x721.
                                                   match x721 with Event1 x1314
                                                   then
                                                     x1314.toState
                                                   else
                                                     let #var"277" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st459, x722)
                                            in
                                            match
                                              p_subApply st459 hrmStoreSubmodel (hrmInit {}) x720 x722
                                            with
                                              (st460, x723)
                                            in
                                            match p_join st460 x723 with (st461, x724)
                                            in
                                            match
                                              p_map
                                                st461
                                                (lam x725.
                                                   lam x726.
                                                     divf x725 x726)
                                                x724
                                            with
                                              (st462, x727)
                                            in
                                            match p_apply st462 x727 totalLeavingRate13 with (st463, x728)
                                            in
                                            match log11 st463 x728 with (st464, x729)
                                            in
                                            match
                                              p_map
                                                st464
                                                (lam x730.
                                                   lam x731.
                                                     lam x732.
                                                       addf (subf x730 x731) x732)
                                                x729
                                            with
                                              (st465, x733)
                                            in
                                            match
                                              p_map
                                                st465
                                                (lam x734.
                                                   lam x735.
                                                     mulf (subf parentAge x734) x735)
                                                newAge3
                                            with
                                              (st466, x736)
                                            in
                                            match p_apply st466 x736 totalLeavingRate13 with (st467, x737)
                                            in
                                            match p_apply st467 x733 x737 with (st468, x738)
                                            in
                                            match
                                              updateRepertoire st468 parentRep nextEvent3 nHosts
                                            with
                                              (st469, x739)
                                            in
                                            match
                                              fullModelWeight1
                                                st469
                                                (addi 1 1)
                                                x739
                                                rep2
                                                newAge3
                                                finalAge31
                                                orderedEvents1
                                                x712
                                                nHosts
                                                modelParams11
                                            with
                                              (st470, x740)
                                            in
                                            p_apply st470 x738 x740)
                                       nEvents41
                                   with
                                     (st471, x741)
                                   in
                                   (st471, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = x711,
                                       logModelDensity = x741,
                                       success = true })
                                 else
                                   (st431, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = p_pure (log1 0.),
                                       logModelDensity = p_pure (log1 0.),
                                       success = false })
                               with
                                 (st472, x742)
                               in
                               match x742 with CorrectedBranchSample1 x743
                               in
                               match x743 with {history = x744}
                               in
                               match
                                 p_map
                                   st472
                                   (lam x745.
                                      lam x746.
                                        lam x747.
                                          match x743 with {success = x748}
                                          in
                                          CorrectedBranchSample1
                                            { history = x745,
                                              logSamplingDensity = x746,
                                              logModelDensity = x747,
                                              success = x748 })
                                   x744
                               with
                                 (st473, x749)
                               in
                               match x743 with {logSamplingDensity = x750}
                               in
                               match p_apply st473 x749 x750 with (st474, x751)
                               in
                               match x743 with {logModelDensity = x752}
                               in
                               p_apply st474 x751 x752)
                          x668
                      with
                        (st475, branchSample1)
                      in
                      match
                        p_map
                          st475
                          (lam x753.
                             lam x754.
                               lam x755.
                                 subf
                                   (subf
                                      (match x753 with CorrectedBranchSample1 x7010
                                       then
                                         x7010.logModelDensity
                                       else
                                         let #var"278" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:14-157:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x754)
                                   x755)
                          branchSample1
                      with
                        (st476, x756)
                      in
                      match
                        p_map
                          st476
                          (lam x757.
                             match x757 with CorrectedBranchSample1 x7110
                             then
                               x7110.logSamplingDensity
                             else
                               let #var"279" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:45-157:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st477, x758)
                      in
                      match p_apply st477 x756 x758 with (st478, x759)
                      in
                      match
                        getRepertoireSamplingDensity st478 rep2 samplingProb nHosts
                      with
                        (st479, x760)
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
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:113-157:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1) in
                      match
                        p_map
                          st479
                          (lam x761.
                             mulf
                               x761
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
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:113-157:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1))
                                     0.)))
                          x760
                      with
                        (st480, x762)
                      in
                      match p_apply st480 x759 x762 with (st481, x763)
                      in
                      let st482 =
                        p_weight
                          st481
                          (hrmStoreLikrWeight nl)
                          (/-temp-/lam x771.
                             x771)
                          x763
                      in
                      let foo2 = {} in
                      match observationMessage1 st482 rep2 1 nHosts with (st483, x764)
                      in
                      match mtxCreate1 st483 nHosts 3 x764 with (st484, newMsg) in
                      let st484 = p_export st484 (hrmStoreNodeMsg nl) newMsg in
                      let st484 = p_export st484 (hrmStorePreorderMsg nl) preorderMsg in
                      match
                        mtxMul
                          st484
                          newMsg
                          (match tree2 with MsgNode x6910
                           then
                             x6910.leftKernel
                           else
                             let #var"281" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 161:33-161:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st485, x765)
                      in
                      match
                        sampleTreeHistory
                          st485
                          (match tree2 with MsgNode x6410
                           then
                             x6410.left
                           else
                             let #var"282" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:6-166:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          nHosts
                          x765
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:39-166:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6710
                           then
                             x6710.leftKernel
                           else
                             let #var"284" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:62-166:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st486, x766)
                      in
                      match
                        mtxMul
                          st486
                          newMsg
                          (match tree2 with MsgNode x6810
                           then
                             x6810.rightKernel
                           else
                             let #var"285" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 162:34-162:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st487, x767)
                      in
                      match
                        sampleTreeHistory
                          st487
                          (match tree2 with MsgNode x6010
                           then
                             x6010.right
                           else
                             let #var"286" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 169:6-169:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          nHosts
                          x767
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 169:41-169:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6310
                           then
                             x6310.rightKernel
                           else
                             let #var"288" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 169:64-169:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st488, x768)
                      in
                      match
                        p_map
                          st488
                          (lam x769.
                             match x769 with CorrectedBranchSample1 x5910
                             then
                               x5910.history
                             else
                               let #var"289" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 176:16-176:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st489, x770)
                      in
                      (st489, HistoryNode
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
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 173:12-173:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 174:14-174:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                              in
                              exit 1,
                          left = x766,
                          right = x768,
                          history = x770,
                          repertoire = rep2 })
  in
  let input1 =
  { symbiontTree = Node
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
      [ [0., 1., 1., 1., 1.]
      , [1., 0., 1., 1., 1.]
      , [1., 1., 0., 1., 1.]
      , [1., 1., 1., 0., 1.]
      , [1., 1., 1., 1., 0.]
      ]
  , dMean = 1.
  } in
  match input1 with {symbiontTree = #var"X9"}
  in
  let symbiontTree = #var"X9" in
  match input1 with {hostDistances = #var"X10"}
  in
  let hostDistances = #var"X10" in
  let nHosts1 = length1 hostDistances in
  match
    p_assume "assume here"
      st hrmStoreLambda (p_pure (mkDirichlet [ 1., 1., 1., 1. ]))
  with
    (st490, lambda)
  in
  match
    p_assume "assume here" st490 hrmStoreMu (p_pure (mkExponential 10.))
  with
    (st491, mu)
  in
  match
    p_assume "assume here" st491 hrmStoreBeta (p_pure (mkExponential 1.))
  with
    (st492, beta)
  in
  recursive let buildTree = lam stree.
    match stree with Leaf { label = label, age = _ } then 
      HRMLeaf { label = label }
    else match stree with Node { label = label, age = _, left = left, right = right } in 
      HRMNode { label = label, left = buildTree left, right = buildTree right } in
  match p_export st492 (hrmStoreTree (buildTree symbiontTree) (match input1 with {interactions = ints} in ints)) (p_pure ()) with st492 in
  match
    p_map
      st492
      (lam x773.
         subf 0. (get x773 (subi 1 1)))
      lambda
  with
    (st493, x774)
  in
  match
    p_map st493 (lam x775.
         get x775 (subi 1 1)) lambda
  with
    (st494, x776)
  in
  match
    p_map st494 (lam x777.
         get x777 (subi 2 1)) lambda
  with
    (st495, x778)
  in
  match
    p_map
      st495
      (lam x779.
         lam x780.
           subf 0. (addf (get x779 (subi 2 1)) x780))
      lambda
  with
    (st496, x781)
  in
  match
    p_map st496 (lam x782.
         get x782 (subi 3 1)) lambda
  with
    (st497, x783)
  in
  match p_apply st497 x781 x783 with (st498, x784)
  in
  match
    p_map st498 (lam x785.
         get x785 (subi 3 1)) lambda
  with
    (st499, x786)
  in
  match
    p_map st499 (lam x787.
         get x787 (subi 4 1)) lambda
  with
    (st500, x788)
  in
  match
    p_map
      st500
      (lam x789.
         subf 0. (get x789 (subi 4 1)))
      lambda
  with
    (st501, x790)
  in
  match
    mtxCreate1
      st501
      3
      3
      [ x774,
        x776,
        p_pure 0.,
        x778,
        x784,
        x786,
        p_pure 0.,
        x788,
        x790 ]
  with
    (st502, mtx4)
  in
  match p_map st502 (lam x791.
         x791.m) mtx4 with (st503, m2)
  in
  match p_map st503 (lam x792.
         x792.n) mtx4 with (st504, n4)
  in
  match
    p_map
      st504
      (lam x793.
         lam x794.
           lam x795.
             lam x796.
               lam x797.
                 tmOpaque (let b14 = matMakeUninit (externalExtArrKind x797.arr) x793 x794
                  in
                  let #var"14" = externalCblasCopy x795 x797.arr 1 b14.arr 1 in
                  let #var"15" = externalCblasScal x795 x796 b14.arr 1 in
                  b14))
      m2
  with
    (st505, x798)
  in
  match p_apply st505 x798 n4 with (st506, x799)
  in
  match
    p_map
      st506
      (lam x800.
         lam x801.
           muli x800 x801)
      m2
  with
    (st507, x802)
  in
  match p_apply st507 x802 n4 with (st508, x803)
  in
  match p_apply st508 x799 x803 with (st509, x804)
  in
  match p_apply st509 x804 mu with (st510, x805)
  in
  match p_apply st510 x805 mtx4 with (st511, qMatrix2)
  in
  match input1 with {interactions = #var"X11"}
  in
  match
    postorderTraverse st511 symbiontTree qMatrix2 #var"X11" nHosts1
  with
    (st512, postorderTree)
  in
  let a36 =
    match postorderTree with MsgLeaf carried66
    then
      match carried66 with {outMsg = #var"X17"}
      in
      p_pure #var"X17"
    else match postorderTree with MsgNode carried67
    then
      carried67.outMsg
    else
      let #var"2106" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 39:36-39:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n"
      in
      p_pure (exit 1)
  in
  let b4 = mtxCreate nHosts1 3 (ones (muli 3 nHosts1)) in
  match
    p_map
      st512
      (lam x806.
         match x806 with {m = #var"X12"}
         in
         match b4 with {m = #var"X13"}
         in
         eqi #var"X12" #var"X13")
      a36
  with
    (st513, x807)
  in
  match
    p_map
      st513
      (lam x808.
         match x808 with {n = #var"X14"}
         in
         match b4 with {n = #var"X15"}
         in
         eqi #var"X14" #var"X15")
      a36
  with
    (st514, x809)
  in
  match and1 st514 x807 x809 with (st515, x810)
  in
  match
    p_bind
      st515
      hrmStoreSubmodel
      (hrmInit {})
      (lam st516.
         lam x811.
           match
             match x811 with true
             then
               match
                 p_map
                   st516
                   (lam x812.
                      tmOpaque (let c310 = matMakeUninit (externalExtArrKind x812.arr) x812.m x812.n
                       in
                       let #var"16" = matElemMulNoAlloc x812 b4 c310 in
                       c310))
                   a36
               with
                 (st517, x813)
               in
               (st517, Right
                 x813)
             else
               (st516, Left
                 (DimensionMismatch
                    {}))
           with
             (st518, n3)
           in
           match n3 with Right x814
           then
             p_map
               st518
               (lam x815.
                  Right
                    x815)
               x814
           else match n3 with Left x816
           in
           (st518, p_pure (Left
                x816)))
      x810
  with
    (st519, x817)
  in
  match eitherEither st519 x817 with (st520, rootSamplingProb)
  in
  match
    suggestNodeRep
      st520
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
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 40:57-40:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
         in
         exit 1)
  with
    (st521, rootRep)
  in
  match any1 st521 rootRep with (st522, x818)
  in
  match bool2real st522 x818 with (st523, x819)
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
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 42:45-42:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1) in
  let st524 =
    p_weight
      st523
      (hrmStoreNodeSuppWeight rl)
      (lam x848.
         externalLog
           (addf
              x848
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
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 42:45-42:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1))
                 0.)))
      x819
  in
  let foo3 = {} in
  match
    getRepertoireSamplingDensity st524 rootRep rootSamplingProb nHosts1
  with
    (st525, x820)
  in
  
  let st526 =
    p_weight
      st525
      (hrmStoreLikrWeight rl)
      (lam x847.
         mulf
           (subf
              (negf
                 (log1
                    (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1)))))
              x847)
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
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 49:70-49:89>:\nField \'label\' not found\n[0m  logWeight (rootLogModelDensity - rootLogSamplingDensity) * exp(Real([31mpostorderTree.label[0m[0m) * 0.);\n"
                       in
                       exit 1))
                 0.)))
      x820
  in
  let foo4 = {} in
  match observationMessage1 st526 rootRep 1 nHosts1 with (st527, x821)
  in
  match mtxCreate1 st527 nHosts1 3 x821 with (st528, newMsg1) in
  let st528 = p_export st528 (hrmStoreNodeMsg rl) newMsg1 in
  let st528 = p_export st528 (hrmStorePreorderMsg rl) (p_pure b4) in
  match input1 with {dMean = #var"X16"}
  in
  match mtxGet st528 2 2 qMatrix2 with (st529, x822)
  in
  match p_map st529 (lam x823.
         negf x823) x822 with (st530, q2)
  in
  match mtxGet st530 1 1 qMatrix2 with (st531, x824)
  in
  match p_map st531 (lam x825.
         negf x825) x824 with (st532, x826)
  in
  match mtxGet st532 3 3 qMatrix2 with (st533, x827)
  in
  match p_map st533 (lam x828.
         negf x828) x827 with (st534, x829)
  in
  match mtxGet st534 2 1 qMatrix2 with (st535, x830)
  in
  match
    p_map
      st535
      (lam x831.
         lam x832.
           divf x831 x832)
      x830
  with
    (st536, x833)
  in
  match p_apply st536 x833 q2 with (st537, x834)
  in
  match mtxGet st537 2 3 qMatrix2 with (st538, x835)
  in
  match
    p_map
      st538
      (lam x836.
         lam x837.
           divf x836 x837)
      x835
  with
    (st539, x838)
  in
  match p_apply st539 x838 q2 with (st540, x839)
  in
  let modelParams2 =
    ModelParams1
      { beta = beta,
        meanDist = #var"X16",
        hostMetric =
          mtxCreate
            (length1 hostDistances)
            (length (get hostDistances (subi 1 1)))
            (match hostDistances with [ _ ] ++ _
             then
               match splitAt hostDistances 1 with {#label"1" = x846}
               in
               rec2 (concat "" (get hostDistances 0)) x846
             else match hostDistances with ""
             in
             ""),
        embeddedQMatrix =
          EmbeddedMarkovChainMatrix1
            { totalRates =
                [ x826,
                  q2,
                  x829 ],
              transitionProbs =
                [ [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ],
                  [ x834,
                    p_pure 0.,
                    x839 ],
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
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 65:16-65:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    mtxMul
      st540
      newMsg1
      (match postorderTree with MsgNode x951
       then
         x951.leftKernel
       else
         let #var"295" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 53:31-53:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st541, x840)
  in
  match
    sampleTreeHistory
      st541
      (match postorderTree with MsgNode x901
       then
         x901.left
       else
         let #var"296" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 67:4-67:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
         in
         exit 1)
      nHosts1
      x840
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x911
       then
         x911.leftKernel
       else
         let #var"297" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 67:72-67:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st542, x841)
  in
  match
    mtxMul
      st542
      newMsg1
      (match postorderTree with MsgNode x941
       then
         x941.rightKernel
       else
         let #var"298" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 54:32-54:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st543, x842)
  in
  match
    sampleTreeHistory
      st543
      (match postorderTree with MsgNode x881
       then
         x881.right
       else
         let #var"299" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 71:4-71:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
         in
         exit 1)
      nHosts1
      x842
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x891
       then
         x891.rightKernel
       else
         let #var"2100" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 71:74-71:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st544, x843)
  in
  match
    p_traverseSeq
      st544
      (lam st545.
         lam x844.
           (st545, x844))
      ""
  with
    (st546, x845)
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
  match makeDirtyArray st546 rootRep with (st546, dRootRep) in
  let m = mapInsert rl dRootRep m in
  match extractSamples st546 m x841 with (st546, m) in
  match extractSamples st546 m x843 with (st546, m) in
  let dirtyKeyVal = lam st. lam kv. match kv with (k, v) in p_map st (lam v. (k, v)) v in 
  match p_traverseSeq st546 dirtyKeyVal (mapToSeq m) with (st546, wrappedReps) in
  match p_map st546 (
    lam mu. lam beta. lam lambda. lam reps.
      -- printLn (join ["Export root rep: [", int2string rootRep1, ", ", int2string rootRep2, "]"]);
      { mu = mu
      , beta = beta
      , lambda = lambda
      , reps = mapFromSeq subi reps 
      }
  ) mu with (st546, partres) in
  match p_apply st546 partres beta with (st546, partres) in
  match p_apply st546 partres lambda with (st546, partres) in
  match p_apply st546 partres wrappedReps with (st546, res) in
  p_export
    st546
    hrmStoreExport
    res