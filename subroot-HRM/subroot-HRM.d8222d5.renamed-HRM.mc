lam st.
  type Either p p1 in
  con Left: all p2. all p3. p2 -> Either p2 p3 in
  con Right: all p4. all p5. p5 -> Either p4 p5 in
  type ExtArrKind in
  type ExtArr in
  type CBLASLayout in
  type CBLASTranspose in
  type MatError p6 p7 in
  con DimensionMismatch: all p8. all p9. p8 -> MatError p8 p9 in
  con NotSquare: all p10. all p11. p11 -> MatError p10 p11 in
  type TreeLabeled p12 p13 p14 in
  con Leaf: all p15. all p16. all p17. p15 -> TreeLabeled p15 p16 p17
  in
  con Node: all p18. all p19. all p20. {age: p19, left: TreeLabeled p18 p19 p20, label: p20, right: TreeLabeled p18 p19 p20} -> TreeLabeled p18 p19 p20
  in
  type MsgTree p21 p22 p23 p24 p25 p26 p27 p28 in
  con MsgLeaf: all p29. all p30. all p31. all p32. all p33. all p34. all p35. all p36. p29 -> MsgTree p29 p30 p31 p32 p33 p34 p35 p36
  in
  con MsgNode: all p37. all p38. all p39. all p40. all p41. all p42. all p43. all p44. {age: p38, left: MsgTree p37 p38 p39 p40 p41 p42 p43 p44, label: p39, right: MsgTree p37 p38 p39 p40 p41 p42 p43 p44, outMsg: p42, leftInMsg: p43, leftKernel: p41, rightInMsg: p44, rightKernel: p40} -> MsgTree p37 p38 p39 p40 p41 p42 p43 p44
  in
  type HistoryTree p45 p46 p47 p48 p49 in
  con HistoryLeaf: all p50. all p51. all p52. all p53. all p54. p50 -> HistoryTree p50 p51 p52 p53 p54
  in
  con HistoryNode: all p55. all p56. all p57. all p58. all p59. {age: p56, left: HistoryTree p55 p56 p57 p58 p59, label: p57, right: HistoryTree p55 p56 p57 p58 p59, history: p58, repertoire: p59} -> HistoryTree p55 p56 p57 p58 p59
  in
  type Event p60 in
  con Event1: all p61. p61 -> Event p61 in
  type CorrectedBranchSample p62 in
  con CorrectedBranchSample1: all p63. p63 -> CorrectedBranchSample p63
  in
  type ModelParams p64 in
  con ModelParams1: all p65. p65 -> ModelParams p65 in
  type EmbeddedMarkovChainMatrix p66 in
  con EmbeddedMarkovChainMatrix1: all p67. p67 -> EmbeddedMarkovChainMatrix p67
  in
  type ReturnType p68 in
  con ReturnType1: all p69. p69 -> ReturnType p69 in
  type SubrootInfo p70 in
  con SubrootInfo1: all p71. p71 -> SubrootInfo p71 in
  type Bridge p72 in
  con Bridge1: all p73. p73 -> Bridge p73 in
  let and =
    lam a921.
      lam b311.
        match a921 with true
        then
          b311
        else
          false
  in
  let and1 =
    lam st974.
      lam a92.
        lam b31.
          p_select
            st974
            (lam x1536.
               match x1536 with true
               then
                 b31
               else
                 p_pure false)
            a92
  in
  let pow = lam x1873.
      lam y2.
        externalPow x1873 y2
  in
  let pow1 =
    lam st973.
      lam x1872.
        lam y1.
          p_map
            st973 (lam x1535.
               externalPow x1872 x1535) y1
  in
  let pow2 =
    lam st971.
      lam x1871.
        lam y.
          match
            p_map
              st971
              (lam x1528.
                 lam x1529.
                   externalPow x1528 x1529)
              x1871
          with
            (st972, x1530)
          in
          p_apply st972 x1530 y
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
    let rec24 =
      lam st7.
        lam acc4.
          lam s24.
            match s24 with [ _ ] ++ _
            then
              match p_map st7 concat acc4 with (st8, x8)
              in
              match p_apply st8 x8 (get s24 0) with (st9, x9)
              in
              match splitAt s24 1 with {#label"1" = x10}
              in
              rec24 st9 x9 x10
            else match s24 with ""
            in
            (st7, acc4)
  in
  let anon = lam v3.
      lam x1527.
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
      lam st10.
        lam c1.
          lam i11.
            lam acc12.
              match geqi i11 0 with true
              then
                match
                  p_map
                    st10
                    (lam x11.
                       externalExtArrGet x11 i11)
                    c1
                with
                  (st11, x12)
                in
                rec31 st11 c1 (subi i11 1) (cons x12 acc12)
              else
                (st10, acc12)
  in
  let extArrMakeUninit =
    lam kind2.
      lam n7.
        externalExtArrMakeUninit kind2 n7
  in
  let extArrGetExn =
    lam st970.
      lam a75.
        lam i24.
          p_map
            st970
            (lam x1526.
               externalExtArrGet x1526 i24)
            a75
  in
  let extArrOfSeq =
    lam st969.
      lam kind11.
        lam seq6.
          p_map
            st969
            (lam x1525.
               tmOpaque (let len2 = length x1525 in
                let a712 = externalExtArrMakeUninit kind11 len2 in
                recursive
                  let work32 =
                    lam i222.
                      match eqi i222 len2 with true
                      then
                        {}
                      else
                        let #var"2165" = externalExtArrSet a712 i222 (get x1525 i222)
                        in
                        work32 (addi i222 1)
                in
                let #var"2212" = work32 0 in
                a712))
            seq6
  in
  let matErrorToString =
    lam err3.
      match err3 with DimensionMismatch carried77
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
    lam st967.
      lam kind.
        lam m4.
          lam n61.
            match
              p_map
                st967
                (lam x1519.
                   externalExtArrMakeUninit kind (muli m4 x1519))
                n61
            with
              (st968, x1520)
            in
            (st968, { arr = x1520, n = n61, m = m4 })
  in
  let matGetExn =
    lam a661.
      lam i212.
        lam j31.
          match a661 with {arr = #var"X72"}
          in
          match a661 with {n = #var"X73"}
          in
          externalExtArrGet #var"X72" (addi (muli i212 #var"X73") j31)
  in
  let matGetExn1 =
    lam st964.
      lam a66.
        lam i211.
          lam j3.
            match
              p_map
                st964
                (lam x1510.
                   lam x1515.
                     match x1510 with {arr = #var"X70"}
                     in
                     externalExtArrGet #var"X70" x1515)
                a66
            with
              (st965, x1516)
            in
            match
              p_map
                st965
                (lam x1517.
                   match x1517 with {n = #var"X71"}
                   in
                   addi (muli i211 #var"X71") j3)
                a66
            with
              (st966, x1518)
            in
            p_apply st966 x1516 x1518
  in
  let matFromArrExn =
    lam st963.
      lam m3.
        lam n51.
          lam a622.
            p_map
              st963
              (lam x1509.
                 match eqi (muli m3 n51) (externalExtArrLength x1509) with true
                 then
                   { arr = x1509, n = n51, m = m3 }
                 else
                   error "matFromArrExn: dimensions mismatch")
              a622
  in
  let matCopy =
    lam st956.
      lam a60.
        match
          p_map
            st956
            (lam x1488.
               lam x1489.
                 { x1488 with arr = x1489 })
            a60
        with
          (st957, x1490)
        in
        match
          p_map
            st957
            (lam x1495.
               lam x1496.
                 tmOpaque (let b23 = extArrMakeUninit (externalExtArrKind x1495.arr) x1496
                  in
                  let #var"20" = externalCblasCopy x1496 x1495.arr 1 b23 1 in
                  b23))
            a60
        with
          (st958, x1497)
        in
        match
          p_map
            st958
            (lam x1498.
               lam x1499.
                 match x1498 with {m = #var"X69"}
                 in
                 muli #var"X69" x1499)
            a60
        with
          (st959, x1500)
        in
        match
          p_map st959 (lam x1505.
               x1505.n) a60
        with
          (st960, x1506)
        in
        match p_apply st960 x1500 x1506 with (st961, x1507)
        in
        match p_apply st961 x1497 x1507 with (st962, x1508)
        in
        p_apply st962 x1490 x1508
  in
  let matHasSameShape2 =
    lam a58.
      lam b21.
        match a58 with {m = #var"X65"}
        in
        match b21 with {m = #var"X66"}
        in
        match a58 with {n = #var"X67"}
        in
        match b21 with {n = #var"X68"}
        in
        and (eqi #var"X65" #var"X66") (eqi #var"X67" #var"X68")
  in
  let matTranposeNoAlloc =
    lam a55.
      lam b19.
        match a55 with {m = #var"X57"}
        in
        match b19 with {n = #var"X58"}
        in
        match a55 with {n = #var"X59"}
        in
        match b19 with {m = #var"X60"}
        in
        match and (eqi #var"X57" #var"X58") (eqi #var"X59" #var"X60") with true
        then
          match a55 with {m = #var"X61"}
          in
          match a55 with {n = #var"X62"}
          in
          match a55 with {arr = #var"X63"}
          in
          match b19 with {arr = #var"X64"}
          in
          let #var"19" = externalMatTranspose #var"X61" #var"X62" #var"X63" #var"X64"
          in
          Right
            {}
        else
          Left
            (DimensionMismatch
               {})
  in
  let matElemMulNoAlloc =
    lam a54.
      lam b18.
        lam c310.
          match
            and (matHasSameShape2 a54 b18) (matHasSameShape2 b18 c310)
          with
            true
          then
            match a54 with {m = #var"X52"}
            in
            match a54 with {n = #var"X53"}
            in
            match a54 with {arr = #var"X54"}
            in
            match b18 with {arr = #var"X55"}
            in
            match c310 with {arr = #var"X56"}
            in
            let #var"18" =
              externalMatElemMul #var"X52" #var"X53" #var"X54" #var"X55" #var"X56"
            in
            Right
              {}
          else
            Left
              (DimensionMismatch
                 {})
  in
  let matMulExn =
    lam st942.
      lam a48.
        lam b12.
          match
            p_map st942 (lam x1455.
                 x1455.n) a48
          with
            (st943, x1456)
          in
          match
            p_map
              st943
              (lam x1457.
                 lam x1458.
                   lam st944.
                     match
                       match eqi x1457 x1458 with true
                       then
                         match
                           p_map
                             st944
                             (lam x1459.
                                x1459.m)
                             a48
                         with
                           (st945, x1460)
                         in
                         match
                           p_map
                             st945
                             (lam x1465.
                                lam x1466.
                                  lam x1467.
                                    lam x1468.
                                      tmOpaque (let c110 = matMakeUninit (externalExtArrKind x1468.arr) x1465 x1466
                                       in
                                       let #var"13" =
                                         externalCblasGemm
                                           cblasRowMajor
                                           cblasNoTrans
                                           cblasNoTrans
                                           x1465
                                           x1466
                                           x1457
                                           1.
                                           x1467.arr
                                           x1457
                                           x1468.arr
                                           x1466
                                           0.
                                           c110.arr
                                           x1466
                                       in
                                       c110))
                             x1460
                         with
                           (st946, x1469)
                         in
                         match
                           p_map
                             st946
                             (lam x1470.
                                x1470.n)
                             b12
                         with
                           (st947, x1471)
                         in
                         match p_apply st947 x1469 x1471 with (st948, x1472)
                         in
                         match p_apply st948 x1472 a48 with (st949, x1473)
                         in
                         match p_apply st949 x1473 b12 with (st950, x1474)
                         in
                         (st950, Right
                           x1474)
                       else
                         (st944, Left
                           (DimensionMismatch
                              {}))
                     with
                       (st951, n6)
                     in
                     match n6 with Right x1475
                     then
                       p_map
                         st951
                         (lam x1476.
                            Right
                              x1476)
                         x1475
                     else match n6 with Left x1477
                     in
                     (st951, p_pure (Left
                          x1477)))
              x1456
          with
            (st952, x1478)
          in
          match
            p_map st952 (lam x1479.
                 x1479.m) b12
          with
            (st953, x1480)
          in
          match
            p_subApply st953 hrmStoreSubmodel (hrmInit {}) x1478 x1480
          with
            (st954, x1485)
          in
          match p_join st954 x1485 with (st955, x1486)
          in
          p_map
            st955
            (lam x1487.
               match x1487 with Left carried75
               then
                 error (matErrorToString carried75)
               else match x1487 with Right carried76
               in
               carried76)
            x1486
  in
  let matExpExn =
    lam st938.
      lam a46.
        match
          p_map
            st938
            (lam x1444.
               lam x1445.
                 match x1444 with {m = #var"X48"}
                 in
                 match eqi #var"X48" x1445 with true
                 then
                   match x1444 with {m = #var"X49"}
                   in
                   match x1444 with {n = #var"X50"}
                   in
                   match x1444 with {arr = #var"X51"}
                   in
                   Right
                     { x1444 with arr = externalMatExp #var"X49" #var"X50" #var"X51" }
                 else
                   Left
                     (NotSquare
                        {}))
            a46
        with
          (st939, x1446)
        in
        match
          p_map st939 (lam x1447.
               x1447.n) a46
        with
          (st940, x1448)
        in
        match p_apply st940 x1446 x1448 with (st941, x1449)
        in
        p_map
          st941
          (lam x1450.
             match x1450 with Left carried72
             then
               match carried72 with NotSquare carried73
               in
               error "Not square"
             else match x1450 with Right carried74
             in
             carried74)
          x1449
  in
  let exp1 = lam x1721.
      externalExp x1721 in
  let log1 = lam x1712.
      externalLog x1712 in
  let log11 =
    lam st937.
      lam x1711.
        p_map st937 (lam x1443.
             externalLog x1443) x1711
  in
  let isNaN1 =
    lam r21.
      match eqf r21 r21 with true
      then
        false
      else
        true
  in
  let rep =
    lam count1.
      lam elem1.
        let i116 = subi count1 1 in
        match geqi i116 0 with true
        then
          rec3 elem1 (subi i116 1) (cons (anon elem1 i116) "")
        else
          ""
  in
  let paste0 =
    lam l52.
      match l52 with [ _ ] ++ _
      then
        match splitAt l52 1 with {#label"1" = x1442}
        in
        rec2 (concat "" (get l52 0)) x1442
      else match l52 with ""
      in
      ""
  in
  let paste01 =
    lam st931.
      lam l51.
        match l51 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st931
              (lam st932.
                 lam x1436.
                   (st932, x1436))
              ""
          with
            (st933, x1437)
          in
          match p_map st933 concat x1437 with (st934, x1438)
          in
          match p_apply st934 x1438 (get l51 0) with (st935, x1439)
          in
          match splitAt l51 1 with {#label"1" = x1440}
          in
          rec22 st935 x1439 x1440
        else match l51 with ""
        in
        p_traverseSeq
          st931
          (lam st936.
             lam x1441.
               (st936, x1441))
          ""
  in
  let paste02 =
    lam st925.
      lam l5.
        match l5 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st925
              (lam st926.
                 lam x1427.
                   (st926, x1427))
              ""
          with
            (st927, x1428)
          in
          match p_map st927 concat x1428 with (st928, x1429)
          in
          match p_apply st928 x1429 (get l5 0) with (st929, x1430)
          in
          match splitAt l5 1 with {#label"1" = x1434}
          in
          rec24 st929 x1430 x1434
        else match l5 with ""
        in
        p_traverseSeq
          st925
          (lam st930.
             lam x1435.
               (st930, x1435))
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
  let length13 = lam st924.
      lam l31.
        p_map st924 length l31
  in
  recursive
    let rec25 =
      lam acc5.
        lam s25.
          match s25 with [ _ ] ++ _
          then
            match splitAt s25 1 with {#label"1" = x13}
            in
            rec25 (addf acc5 (get s25 0)) x13
          else match s25 with ""
          in
          acc5
    let rec26 =
      lam st12.
        lam acc6.
          lam s26.
            match s26 with [ _ ] ++ _
            then
              match
                p_map
                  st12
                  (lam x14.
                     lam x15.
                       addf x14 x15)
                  acc6
              with
                (st13, x16)
              in
              match p_apply st13 x16 (get s26 0) with (st14, x17)
              in
              match splitAt s26 1 with {#label"1" = x18}
              in
              rec26 st14 x17 x18
            else match s26 with ""
            in
            (st12, acc6)
  in
  let seqSumReal =
    lam st922.
      lam s81.
        match s81 with [ _ ] ++ _
        then
          match
            p_map
              st922 (lam x1424.
                 addf 0. x1424) (get s81 0)
          with
            (st923, x1425)
          in
          match splitAt s81 1 with {#label"1" = x1426}
          in
          rec26 st923 x1425 x1426
        else match s81 with ""
        in
        (st922, p_pure 0.)
  in
  let anon1 =
    lam x1418.
      lam x1419.
        lam x1420.
          match x1420 with true
          then
            snoc x1418 (addi x1419 1)
          else
            x1418
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
      lam st15.
        lam acc22.
          lam i21.
            lam s31.
              match s31 with [ e1 ] ++ rest1
              then
                match
                  p_bind
                    st15
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st16.
                       lam x19.
                         match x19 with true
                         then
                           p_map
                             st16
                             (lam x20.
                                snoc x20 (addi i21 1))
                             acc22
                         else
                           (st16, acc22))
                    e1
                with
                  (st17, x21)
                in
                work1 st17 x21 (addi i21 1) rest1
              else
                (st15, acc22)
  in
  let whichTrue =
    lam s63.
      match s63 with [ e25 ] ++ rest4
      then
        work (anon1 "" 0 e25) (addi 0 1) rest4
      else
        ""
  in
  let whichTrue1 =
    lam st919.
      lam s62.
        match s62 with [ e24 ] ++ rest3
        then
          match
            p_map
              st919
              (lam x1415.
                 match x1415 with true
                 then
                   snoc "" (addi 0 1)
                 else
                   "")
              e24
          with
            (st920, x1416)
          in
          work1 st920 x1416 (addi 0 1) rest3
        else
          p_traverseSeq
            st919
            (lam st921.
               lam x1417.
                 (st921, x1417))
            ""
  in
  let whichTrue2 =
    lam st918.
      lam s61.
        p_map
          st918
          (lam x1414.
             match x1414 with [ e23 ] ++ rest2
             then
               work (anon1 "" 0 e23) (addi 0 1) rest2
             else
               "")
          s61
  in
  let bool2real =
    lam st917.
      lam v.
        p_map
          st917
          (lam x1410.
             match x1410 with true
             then
               1.
             else
               0.)
          v
  in
  let mtxCreate =
    lam rows.
      lam cols11.
        lam data.
          let a621 =
            tmOpaque (let len1 = length data in
             let a711 = externalExtArrMakeUninit extArrKindFloat64 len1 in
             recursive
               let work31 =
                 lam i221.
                   match eqi i221 len1 with true
                   then
                     {}
                   else
                     let #var"2164" = externalExtArrSet a711 i221 (get data i221) in
                     work31 (addi i221 1)
             in
             let #var"2211" = work31 0 in
             a711)
          in
          match eqi (muli rows cols11) (externalExtArrLength a621) with true
          then
            { arr = a621, n = cols11, m = rows }
          else
            error "matFromArrExn: dimensions mismatch"
  in
  let mtxGet =
    lam st916.
      lam row13.
        lam col2.
          lam mtx82.
            matGetExn1 st916 mtx82 (subi row13 1) (subi col2 1)
  in
  let mtxGet1 =
    lam st910.
      lam row12.
        lam col1.
          lam mtx81.
            match
              p_map
                st910
                (lam x1395.
                   lam x1396.
                     match x1395 with {arr = #var"X47"}
                     in
                     externalExtArrGet #var"X47" x1396)
                mtx81
            with
              (st911, x1397)
            in
            match
              p_map st911 (lam x1398.
                   subi x1398 1) row12
            with
              (st912, x1399)
            in
            match
              p_map
                st912
                (lam x1400.
                   lam x1405.
                     addi (muli x1400 x1405) (subi col1 1))
                x1399
            with
              (st913, x1406)
            in
            match
              p_map st913 (lam x1407.
                   x1407.n) mtx81
            with
              (st914, x1408)
            in
            match p_apply st914 x1406 x1408 with (st915, x1409)
            in
            p_apply st915 x1397 x1409
  in
  let mtxGet2 =
    lam st902.
      lam row11.
        lam col.
          lam mtx8.
            match
              p_map
                st902
                (lam x1380.
                   lam x1381.
                     match x1380 with {arr = #var"X46"}
                     in
                     externalExtArrGet #var"X46" x1381)
                mtx8
            with
              (st903, x1382)
            in
            match
              p_map st903 (lam x1383.
                   subi x1383 1) row11
            with
              (st904, x1384)
            in
            match
              p_map
                st904
                (lam x1385.
                   lam x1386.
                     lam x1387.
                       addi (muli x1385 x1386) x1387)
                x1384
            with
              (st905, x1388)
            in
            match
              p_map st905 (lam x1389.
                   x1389.n) mtx8
            with
              (st906, x1390)
            in
            match p_apply st906 x1388 x1390 with (st907, x1391)
            in
            match
              p_map st907 (lam x1392.
                   subi x1392 1) col
            with
              (st908, x1393)
            in
            match p_apply st908 x1391 x1393 with (st909, x1394)
            in
            p_apply st909 x1382 x1394
  in
  let anon2 =
    lam new5.
      lam mtx75.
        lam row5.
          lam x1378.
            lam x1379.
              match new5 with {arr = #var"X44"}
              in
              match new5 with {n = #var"X45"}
              in
              externalExtArrSet
                #var"X44"
                (addi (muli 0 #var"X45") x1378)
                (matGetExn mtx75 (subi row5 1) (subi x1379 1))
  in
  let anon3 =
    lam st899.
      lam new4.
        lam mtx74.
          lam row4.
            lam x1371.
              lam x1372.
                match new4 with {arr = #var"X42"}
                in
                match
                  p_map
                    st899
                    (lam x1373.
                       lam x1374.
                         externalExtArrSet x1373 x1374 (matGetExn mtx74 (subi row4 1) (subi x1372 1)))
                    #var"X42"
                with
                  (st900, x1375)
                in
                match new4 with {n = #var"X43"}
                in
                match
                  p_map
                    st900
                    (lam x1376.
                       addi (muli 0 x1376) x1371)
                    #var"X43"
                with
                  (st901, x1377)
                in
                p_apply st901 x1375 x1377
  in
  let anon4 =
    lam st893.
      lam new3.
        lam mtx73.
          lam row3.
            lam x1358.
              lam x1359.
                match new3 with {arr = #var"X38"}
                in
                match
                  p_map
                    st893
                    (lam x1360.
                       lam x1361.
                         lam x1362.
                           externalExtArrSet x1360 x1361 x1362)
                    #var"X38"
                with
                  (st894, x1363)
                in
                match new3 with {n = #var"X39"}
                in
                match
                  p_map
                    st894
                    (lam x1364.
                       addi (muli 0 x1364) x1358)
                    #var"X39"
                with
                  (st895, x1365)
                in
                match p_apply st895 x1363 x1365 with (st896, x1366)
                in
                match
                  p_map st896 (lam x1367.
                       subi x1367 1) row3
                with
                  (st897, x1368)
                in
                match
                  p_map
                    st897
                    (lam x1369.
                       match mtx73 with {arr = #var"X40"}
                       in
                       match mtx73 with {n = #var"X41"}
                       in
                       externalExtArrGet #var"X40" (addi (muli x1369 #var"X41") (subi x1359 1)))
                    x1368
                with
                  (st898, x1370)
                in
                p_apply st898 x1366 x1370
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
                  match splitAt s1 1 with {#label"1" = x22}
                  in
                  cons
                    (anon2 c2 c3 c4 i (get s1 0)) (rec1 c2 c3 c4 (addi i 1) x22)
                else match s1 with [ e2 ]
                then
                  match splitAt s1 1 with {#label"1" = x23}
                  in
                  let slice1 = x23 in
                  [ anon2 c2 c3 c4 i e2 ]
                else match s1 with ""
                in
                ""
    let rec11 =
      lam st18.
        lam c5.
          lam c6.
            lam c7.
              lam i3.
                lam s11.
                  match s11 with [ _,
                      _ ] ++ _
                  then
                    match anon3 st18 c5 c6 c7 i3 (get s11 0) with (st19, x24)
                    in
                    match splitAt s11 1 with {#label"1" = x25}
                    in
                    match rec11 st19 c5 c6 c7 (addi i3 1) x25 with (st20, x26)
                    in
                    (st20, cons x24 x26)
                  else match s11 with [ e3 ]
                  then
                    match splitAt s11 1 with {#label"1" = x27}
                    in
                    let slice2 = x27 in
                    match anon3 st18 c5 c6 c7 i3 e3 with (st21, x28)
                    in
                    (st21, [ x28 ])
                  else match s11 with ""
                  in
                  (st18, "")
    let rec12 =
      lam st22.
        lam c8.
          lam c9.
            lam c10.
              lam i4.
                lam s12.
                  match s12 with [ _,
                      _ ] ++ _
                  then
                    match anon4 st22 c8 c9 c10 i4 (get s12 0) with (st23, x29)
                    in
                    match splitAt s12 1 with {#label"1" = x30}
                    in
                    match rec12 st23 c8 c9 c10 (addi i4 1) x30 with (st24, x31)
                    in
                    (st24, cons x29 x31)
                  else match s12 with [ e4 ]
                  then
                    match splitAt s12 1 with {#label"1" = x32}
                    in
                    let slice3 = x32 in
                    match anon4 st22 c8 c9 c10 i4 e4 with (st25, x33)
                    in
                    (st25, [ x33 ])
                  else match s12 with ""
                  in
                  (st22, "")
  in
  let mtxRowCols =
    lam mtx72.
      lam row2.
        lam cols2.
          match mtx72 with {arr = #var"X37"}
          in
          let new2 =
            matMakeUninit (externalExtArrKind #var"X37") 1 (length cols2)
          in
          let #var"2412" = rec1 new2 mtx72 row2 0 cols2 in
          let #var"102" = {} in
          new2
  in
  let mtxRowCols1 =
    lam st883.
      lam mtx71.
        lam row1.
          lam cols1.
            match mtx71 with {arr = #var"X36"}
            in
            match p_map st883 length cols1 with (st884, x1349)
            in
            match
              matMakeUninit1 st884 (externalExtArrKind #var"X36") 1 x1349
            with
              (st885, new1)
            in
            match
              p_bind
                st885
                hrmStoreSubmodel
                (hrmInit {})
                (lam st886.
                   lam x1350.
                     match
                       match x1350 with [ _,
                           _ ] ++ _
                       then
                         match anon3 st886 new1 mtx71 row1 0 (get x1350 0) with (st887, x1351)
                         in
                         match splitAt x1350 1 with {#label"1" = x1352}
                         in
                         match rec11 st887 new1 mtx71 row1 (addi 0 1) x1352 with (st888, x1353)
                         in
                         (st888, cons x1351 x1353)
                       else match x1350 with [ e22 ]
                       then
                         match splitAt x1350 1 with {#label"1" = x1354}
                         in
                         let slice21 = x1354 in
                         match anon3 st886 new1 mtx71 row1 0 e22 with (st889, x1355)
                         in
                         (st889, [ x1355 ])
                       else match x1350 with ""
                       in
                       (st886, "")
                     with
                       (st890, x1356)
                     in
                     p_traverseSeq
                       st890
                       (lam st891.
                          lam x1357.
                            (st891, x1357))
                       x1356)
                cols1
            with
              (st892, #var"2411")
            in
            let #var"101" = {} in
            (st892, new1)
  in
  let mtxRowCols2 =
    lam st873.
      lam mtx7.
        lam row.
          lam cols.
            match mtx7 with {arr = #var"X35"}
            in
            match p_map st873 length cols with (st874, x1340)
            in
            match
              matMakeUninit1 st874 (externalExtArrKind #var"X35") 1 x1340
            with
              (st875, new)
            in
            match
              p_bind
                st875
                hrmStoreSubmodel
                (hrmInit {})
                (lam st876.
                   lam x1341.
                     match
                       match x1341 with [ _,
                           _ ] ++ _
                       then
                         match anon4 st876 new mtx7 row 0 (get x1341 0) with (st877, x1342)
                         in
                         match splitAt x1341 1 with {#label"1" = x1343}
                         in
                         match rec12 st877 new mtx7 row (addi 0 1) x1343 with (st878, x1344)
                         in
                         (st878, cons x1342 x1344)
                       else match x1341 with [ e21 ]
                       then
                         match splitAt x1341 1 with {#label"1" = x1345}
                         in
                         let slice20 = x1345 in
                         match anon4 st876 new mtx7 row 0 e21 with (st879, x1346)
                         in
                         (st879, [ x1346 ])
                       else match x1341 with ""
                       in
                       (st876, "")
                     with
                       (st880, x1347)
                     in
                     p_traverseSeq
                       st880
                       (lam st881.
                          lam x1348.
                            (st881, x1348))
                       x1347)
                cols
            with
              (st882, #var"2410")
            in
            let #var"10" = {} in
            (st882, new)
  in
  let mtxSclrMul =
    lam st865.
      lam scalar.
        lam mtx61.
          match
            p_map st865 (lam x1327.
                 x1327.m) mtx61
          with
            (st866, m21)
          in
          match
            p_map st866 (lam x1328.
                 x1328.n) mtx61
          with
            (st867, n41)
          in
          match
            p_map
              st867
              (lam x1329.
                 lam x1330.
                   lam x1331.
                     lam x1332.
                       tmOpaque (let b141 = matMakeUninit (externalExtArrKind x1332.arr) x1329 x1330
                        in
                        let #var"141" = externalCblasCopy x1331 x1332.arr 1 b141.arr 1
                        in
                        let #var"151" = externalCblasScal x1331 scalar b141.arr 1 in
                        b141))
              m21
          with
            (st868, x1333)
          in
          match p_apply st868 x1333 n41 with (st869, x1334)
          in
          match
            p_map
              st869
              (lam x1335.
                 lam x1336.
                   muli x1335 x1336)
              m21
          with
            (st870, x1337)
          in
          match p_apply st870 x1337 n41 with (st871, x1338)
          in
          match p_apply st871 x1334 x1338 with (st872, x1339)
          in
          p_apply st872 x1339 mtx61
  in
  let mtxTrans =
    lam st864.
      lam mtx5.
        p_map
          st864
          (lam x1326.
             tmOpaque (let b17 = matMakeUninit (externalExtArrKind x1326.arr) x1326.n x1326.m
              in
              let #var"17" = matTranposeNoAlloc x1326 b17 in
              b17))
          mtx5
  in
  let anon5 =
    lam st859.
      lam mtx131.
        lam mtx241.
          lam x1317.
            match
              p_map
                st859
                (lam x1318.
                   lam x1319.
                     match x1318 with {arr = #var"X34"}
                     in
                     externalExtArrSet #var"X34" x1317 x1319)
                mtx241
            with
              (st860, x1320)
            in
            match
              p_map st860 (lam x1321.
                   x1321.arr) mtx131
            with
              (st861, x1322)
            in
            match extArrGetExn st861 x1322 x1317 with (st862, x1323)
            in
            match
              p_map
                st862
                (lam x1324.
                   match gtf x1324 0. with true
                   then
                     x1324
                   else
                     0.)
                x1323
            with
              (st863, x1325)
            in
            p_apply st863 x1320 x1325
  in
  recursive
    let rec4 =
      lam st26.
        lam c11.
          lam c12.
            lam n.
              lam i31.
                match geqi i31 n with true
                then
                  (st26, {})
                else match anon5 st26 c11 c12 i31 with (st27, #var"")
                in
                rec4 st27 c11 c12 n (addi i31 1)
  in
  let anon6 =
    lam st832.
      lam mtx102.
        lam mtx213.
          lam x1265.
            lam x1266.
              match
                p_map
                  st832
                  (lam x1267.
                     lam x1268.
                       lam x1269.
                         match x1267 with {arr = #var"X32"}
                         in
                         externalExtArrSet #var"X32" x1268 x1269)
                  mtx213
              with
                (st833, x1270)
              in
              match
                p_map
                  st833
                  (lam x1271.
                     match x1271 with {n = #var"X33"}
                     in
                     addi (muli x1265 #var"X33") x1266)
                  mtx213
              with
                (st834, x1272)
              in
              match p_apply st834 x1270 x1272 with (st835, x1273)
              in
              match matGetExn1 st835 mtx102 x1265 x1266 with (st836, x1274)
              in
              match
                p_map
                  st836
                  (lam x1275.
                     lam x1276.
                       divf x1275 x1276)
                  x1274
              with
                (st837, x1277)
              in
              match
                p_map st837 (lam x1278.
                     x1278.m) mtx102
              with
                (st838, x1279)
              in
              match
                p_map st838 (lam x1280.
                     subi x1280 1) x1279
              with
                (st839, x1281)
              in
              match
                p_map
                  st839
                  (lam x1282.
                     match geqi x1282 0 with true
                     then
                       rec3 1. (subi x1282 1) (cons (anon 1. x1282) "")
                     else
                       "")
                  x1281
              with
                (st840, x1283)
              in
              match extArrOfSeq st840 extArrKindFloat64 x1283 with (st841, a62)
              in
              match
                p_map st841 (lam x1284.
                     x1284.m) mtx102
              with
                (st842, x1285)
              in
              match
                p_map
                  st842
                  (lam x1286.
                     lam x1287.
                       lam st843.
                         let x1288 =
                           match eqi (muli x1286 1) x1287 with true
                           then
                             { arr = a62, n = 1, m = x1286 }
                           else
                             let x1293 = error "matFromArrExn: dimensions mismatch" in
                             match x1293 with {arr = x1294}
                             in
                             match x1293 with {n = x1295}
                             in
                             match x1293 with {m = x1296}
                             in
                             { arr = p_pure x1294, n = x1295, m = x1296 }
                         in
                         match x1288 with {arr = x1289}
                         in
                         p_map
                           st843
                           (lam x1290.
                              match x1288 with {n = x1291}
                              in
                              match x1288 with {m = x1292}
                              in
                              { arr = x1290, n = x1291, m = x1292 })
                           x1289)
                  x1285
              with
                (st844, x1297)
              in
              match
                p_map
                  st844
                  (lam x1298.
                     externalExtArrLength x1298)
                  a62
              with
                (st845, x1299)
              in
              match
                p_subApply st845 hrmStoreSubmodel (hrmInit {}) x1297 x1299
              with
                (st846, x1300)
              in
              match p_join st846 x1300 with (st847, x1301)
              in
              match matMulExn st847 mtx102 x1301 with (st848, x1302)
              in
              match
                p_map
                  st848
                  (lam x1303.
                     match x1303 with {arr = field24, n = field25, m = field26}
                     in
                     field24)
                  x1302
              with
                (st849, a69)
              in
              match
                p_map
                  st849
                  (lam x1304.
                     externalExtArrLength x1304)
                  a69
              with
                (st850, x1305)
              in
              match
                p_map st850 (lam x1306.
                     subi x1306 1) x1305
              with
                (st851, x1307)
              in
              match
                p_bind
                  st851
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st852.
                     lam x1308.
                       match
                         match geqi x1308 0 with true
                         then
                           match
                             p_map
                               st852
                               (lam x1309.
                                  externalExtArrGet x1309 x1308)
                               a69
                           with
                             (st853, x1310)
                           in
                           rec31 st853 a69 (subi x1308 1) (cons x1310 "")
                         else
                           (st852, "")
                       with
                         (st854, x1311)
                       in
                       p_traverseSeq
                         st854
                         (lam st855.
                            lam x1312.
                              (st855, x1312))
                         x1311)
                  x1307
              with
                (st856, x1313)
              in
              match
                p_map
                  st856 (lam x1314.
                     get x1314 x1265) x1313
              with
                (st857, x1315)
              in
              match p_apply st857 x1277 x1315 with (st858, x1316)
              in
              p_apply st858 x1273 x1316
  in
  recursive
    let rec41 =
      lam st28.
        lam c13.
          lam c14.
            lam c15.
              lam n1.
                lam i32.
                  match geqi i32 n1 with true
                  then
                    (st28, {})
                  else match anon6 st28 c13 c14 c15 i32 with (st29, #var"1")
                  in
                  rec41 st29 c13 c14 c15 n1 (addi i32 1)
  in
  let anon7 =
    lam st828.
      lam mtx101.
        lam mtx212.
          lam x1260.
            match
              p_map st828 (lam x1262.
                   x1262.n) mtx101
            with
              (st829, x1263)
            in
            p_subMap
              st829
              hrmStoreSubmodel
              (hrmInit {})
              (lam x1264.
                 lam st830.
                   match geqi 0 x1264 with true
                   then
                     (st830, {})
                   else match anon6 st830 mtx101 mtx212 #frozen"x1260" 0 with (st831, #var"6")
                   in
                   rec41 st831 mtx101 mtx212 #frozen"x1260" x1264 (addi 0 1))
              x1263
  in
  recursive
    let rec42 =
      lam st30.
        lam c16.
          lam c17.
            lam n2.
              lam i33.
                match geqi i33 n2 with true
                then
                  (st30, {})
                else match anon7 st30 c16 c17 i33 with (st31, #var"2")
                in
                rec42 st31 c16 c17 n2 (addi i33 1)
  in
  let mtxExpRateSafe =
    lam st814.
      lam mtx3.
        match matExpExn st814 mtx3 with (st815, mtx13)
        in
        match matCopy st815 mtx13 with (st816, mtx24)
        in
        match
          p_map
            st816
            (lam x1249.
               lam x1250.
                 match x1249 with {m = #var"X31"}
                 in
                 muli #var"X31" x1250)
            mtx13
        with
          (st817, x1252)
        in
        match
          p_map st817 (lam x1253.
               x1253.n) mtx13
        with
          (st818, x1254)
        in
        match p_apply st818 x1252 x1254 with (st819, x1255)
        in
        match
          p_subMap
            st819
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1256.
               lam st820.
                 match geqi 0 x1256 with true
                 then
                   (st820, {})
                 else match anon5 st820 mtx13 mtx24 0 with (st821, #var"4")
                 in
                 rec4 st821 mtx13 mtx24 x1256 (addi 0 1))
            x1255
        with
          (st822, #var"12")
        in
        let mtx10 = mtx24 in
        match matCopy st822 mtx10 with (st823, mtx211)
        in
        match
          p_map st823 (lam x1257.
               x1257.m) mtx10
        with
          (st824, x1258)
        in
        match
          p_subMap
            st824
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1259.
               lam st825.
                 match geqi 0 x1259 with true
                 then
                   (st825, {})
                 else match anon7 st825 mtx10 mtx211 0 with (st826, #var"5")
                 in
                 rec42 st826 mtx10 mtx211 x1259 (addi 0 1))
            x1258
        with
          (st827, #var"11")
        in
        (st827, mtx211)
  in
  let mtxMul =
    lam st813.
      lam a33.
        lam b5.
          matMulExn st813 a33 b5
  in
  let eitherEither =
    lam st812.
      lam e31.
        p_map
          st812
          (lam x1248.
             match x1248 with Left carried70
             then
               error (matErrorToString carried70)
             else match x1248 with Right carried71
             in
             carried71)
          e31
  in
  let mtxElemMul =
    lam st799.
      lam a321.
        lam b41.
          match
            p_map
              st799
              (lam x1225.
                 lam x1226.
                   match x1225 with {m = #var"X29"}
                   in
                   eqi #var"X29" x1226)
              a321
          with
            (st800, x1227)
          in
          match
            p_map st800 (lam x1228.
                 x1228.m) b41
          with
            (st801, x1229)
          in
          match p_apply st801 x1227 x1229 with (st802, x1230)
          in
          match
            p_map
              st802
              (lam x1231.
                 lam x1232.
                   match x1231 with {n = #var"X30"}
                   in
                   eqi #var"X30" x1232)
              a321
          with
            (st803, x1233)
          in
          match
            p_map st803 (lam x1234.
                 x1234.n) b41
          with
            (st804, x1235)
          in
          match p_apply st804 x1233 x1235 with (st805, x1236)
          in
          match and1 st805 x1230 x1236 with (st806, x1237)
          in
          match
            p_bind
              st806
              hrmStoreSubmodel
              (hrmInit {})
              (lam st807.
                 lam x1238.
                   match
                     match x1238 with true
                     then
                       match
                         p_map
                           st807
                           (lam x1239.
                              lam x1240.
                                tmOpaque (let c211 = matMakeUninit (externalExtArrKind x1239.arr) x1239.m x1239.n
                                 in
                                 let #var"161" = matElemMulNoAlloc x1239 x1240 c211 in
                                 c211))
                           a321
                       with
                         (st808, x1242)
                       in
                       match p_apply st808 x1242 b41 with (st809, x1243)
                       in
                       (st809, Right
                         x1243)
                     else
                       (st807, Left
                         (DimensionMismatch
                            {}))
                   with
                     (st810, n5)
                   in
                   match n5 with Right x1244
                   then
                     p_map
                       st810
                       (lam x1245.
                          Right
                            x1245)
                       x1244
                   else match n5 with Left x1246
                   in
                   (st810, p_pure (Left
                        x1246)))
              x1237
          with
            (st811, x1247)
          in
          eitherEither st811 x1247
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
      lam st32.
        lam bound1.
          lam c19.
            lam i42.
              lam acc32.
                match lti i42 bound1 with true
                then
                  match
                    p_map
                      st32
                      (lam x34.
                         lam x35.
                           addf x34 x35)
                      acc32
                  with
                    (st33, x36)
                  in
                  match c19 with {arr = #var"X1"}
                  in
                  match extArrGetExn st33 #var"X1" i42 with (st34, x37)
                  in
                  match p_apply st34 x36 x37 with (st35, x38)
                  in
                  work21 st35 bound1 c19 (addi i42 1) x38
                else
                  (st32, acc32)
  in
  let mtxMean =
    lam mtx21.
      match mtx21 with {m = #var"X25"}
      in
      match mtx21 with {n = #var"X26"}
      in
      match mtx21 with {m = #var"X27"}
      in
      match mtx21 with {n = #var"X28"}
      in
      divf
        (work2 (muli #var"X25" #var"X26") mtx21 0 0.)
        (int2float (muli #var"X27" #var"X28"))
  in
  let mtxMean1 =
    lam st791.
      lam mtx2.
        match mtx2 with {n = #var"X20"}
        in
        match
          p_map
            st791
            (lam x1213.
               match mtx2 with {m = #var"X21"}
               in
               muli #var"X21" x1213)
            #var"X20"
        with
          (st792, x1214)
        in
        match
          p_bind
            st792
            hrmStoreSubmodel
            (hrmInit {})
            (lam st793.
               lam x1215.
                 match lti 0 x1215 with true
                 then
                   match mtx2 with {arr = #var"X22"}
                   in
                   match extArrGetExn st793 #var"X22" 0 with (st794, x1216)
                   in
                   match
                     p_map
                       st794
                       (lam x1217.
                          addf 0. x1217)
                       x1216
                   with
                     (st795, x1218)
                   in
                   work21 st795 x1215 mtx2 (addi 0 1) x1218
                 else
                   (st793, p_pure 0.))
            x1214
        with
          (st796, x1219)
        in
        match
          p_map
            st796
            (lam x1220.
               lam x1221.
                 divf x1220 x1221)
            x1219
        with
          (st797, x1222)
        in
        match mtx2 with {n = #var"X23"}
        in
        match
          p_map
            st797
            (lam x1223.
               match mtx2 with {m = #var"X24"}
               in
               int2float (muli #var"X24" x1223))
            #var"X23"
        with
          (st798, x1224)
        in
        p_apply st798 x1222 x1224
  in
  let anon8 =
    lam x1211.
      lam x1212.
        match eqi (addi x1211 1) (addi x1212 1) with true
        then
          1.
        else
          0.
  in
  recursive
    let rec32 =
      lam c20.
        lam i12.
          lam acc13.
            match geqi i12 0 with true
            then
              rec32 c20 (subi i12 1) (cons (anon8 c20 i12) acc13)
            else
              acc13
  in
  let create1 =
    lam l64.
      lam c71.
        let i115 = subi l64 1 in
        match geqi i115 0 with true
        then
          rec32 c71 (subi i115 1) (cons (anon8 c71 i115) "")
        else
          ""
  in
  let anon9 =
    lam x1210.
      match
        match geqi x1210 0 with true
        then
          leqi x1210 2
        else
          false
      with
        true
      then
        create1 3 #frozen"x1210"
      else
        rep 3 1.
  in
  let anon10 =
    lam st790.
      lam x1208.
        p_map
          st790
          (lam x1209.
             match
               match geqi x1209 0 with true
               then
                 leqi x1209 2
               else
                 false
             with
               true
             then
               create1 3 x1209
             else
               rep 3 1.)
          x1208
  in
  recursive
    let rec =
      lam s.
        match s with [ _,
            _ ] ++ _
        then
          match splitAt s 1 with {#label"1" = x39}
          in
          cons (anon9 (get s 0)) (rec x39)
        else match s with [ e5 ]
        then
          match splitAt s 1 with {#label"1" = x40}
          in
          let slice4 = x40 in
          [ anon9 e5 ]
        else match s with ""
        in
        ""
    let rec5 =
      lam st36.
        lam s4.
          match s4 with [ _,
              _ ] ++ _
          then
            match anon10 st36 (get s4 0) with (st37, x41)
            in
            match splitAt s4 1 with {#label"1" = x42}
            in
            match rec5 st37 x42 with (st38, x43)
            in
            (st38, cons x41 x43)
          else match s4 with [ e6 ]
          then
            match splitAt s4 1 with {#label"1" = x44}
            in
            let slice5 = x44 in
            match anon10 st36 e6 with (st39, x45)
            in
            (st39, [ x45 ])
          else match s4 with ""
          in
          (st36, "")
  in
  let observationMessage =
    lam obsRepertoire1.
      mtxCreate (length1 obsRepertoire1) 3 (paste0 (rec obsRepertoire1))
  in
  let observationMessage1 =
    lam st781.
      lam obsRepertoire.
        match rec5 st781 obsRepertoire with (st782, s227)
        in
        match
          match s227 with [ _ ] ++ _
          then
            match
              p_traverseSeq
                st782
                (lam st783.
                   lam x1200.
                     (st783, x1200))
                ""
            with
              (st784, x1201)
            in
            match p_map st784 concat x1201 with (st785, x1202)
            in
            match p_apply st785 x1202 (get s227 0) with (st786, x1203)
            in
            match splitAt s227 1 with {#label"1" = x1204}
            in
            rec23 st786 x1203 x1204
          else match s227 with ""
          in
          p_traverseSeq
            st782
            (lam st787.
               lam x1205.
                 (st787, x1205))
            ""
        with
          (st788, x1206)
        in
        match extArrOfSeq st788 extArrKindFloat64 x1206 with (st789, x1207)
        in
        matFromArrExn st789 (length obsRepertoire) 3 x1207
  in
  recursive
    let postorderTraverse =
      lam st40.
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
                    observationMessage
                      (get
                         interactions1
                         (subi
                            (match tree1 with Leaf carried4
                             then
                               carried4.label
                             else match tree1 with Node carried5
                             then
                               carried5.label
                             else
                               let #var"23" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 8:49-8:59>:\nField \'label\' not found\n[0m    let outmsg = observationMessage(interactions[[31mtree.label[0m[0m]);\n"
                               in
                               exit 1)
                            1))
                  in
                  let leafInts =
                    get
                      interactions1
                      (subi
                         (match tree1 with Leaf carried2
                          then
                            carried2.label
                          else match tree1 with Node carried3
                          then
                            carried3.label
                          else
                            let #var"22" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 9:32-9:42>:\nField \'label\' not found\n[0m    let leafInts = interactions[[31mtree.label[0m[0m];\n"
                            in
                            exit 1)
                         1)
                  in
                  (st40, MsgLeaf
                    { age = 0.,
                      label =
                        match tree1 with Leaf carried
                        then
                          carried.label
                        else match tree1 with Node carried1
                        then
                          carried1.label
                        else
                          let #var"21" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 12:14-12:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                          in
                          exit 1,
                      interactions = leafInts,
                      outMsg = observationMessage leafInts })
                else match
                  postorderTraverse
                    st40
                    (match tree1 with Node x231
                     then
                       x231.left
                     else
                       let #var"24" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 18:31-18:40>:\nField \'left\' not found\n[0m  let left = postorderTraverse([31mtree.left[0m[0m, qMatrix, interactions, nhosts);\n"
                       in
                       exit 1)
                    qMatrix1
                    interactions1
                    nhosts1
                with
                  (st41, left)
                in
                match
                  postorderTraverse
                    st41
                    (match tree1 with Node x221
                     then
                       x221.right
                     else
                       let #var"25" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 19:32-19:42>:\nField \'right\' not found\n[0m  let right = postorderTraverse([31mtree.right[0m[0m, qMatrix, interactions, nhosts);\n"
                       in
                       exit 1)
                    qMatrix1
                    interactions1
                    nhosts1
                with
                  (st42, right)
                in
                match
                  mtxSclrMul
                    st42
                    (subf
                       (match tree1 with Leaf carried6
                        then
                          carried6.age
                        else match tree1 with Node carried7
                        then
                          carried7.age
                        else
                          let #var"26" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 22:45-22:53>:\nField \'age\' not found\n[0m  let leftKernel = mtxExpRateSafe(mtxSclrMul([31mtree.age[0m[0m-left.age, qMatrix));\n"
                          in
                          exit 1)
                       (match left with MsgLeaf carried8
                        then
                          carried8.age
                        else match left with MsgNode carried9
                        then
                          carried9.age
                        else
                          let #var"27" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 22:54-22:62>:\nField \'age\' not found\n[0m  let leftKernel = mtxExpRateSafe(mtxSclrMul(tree.age-[31mleft.age[0m[0m, qMatrix));\n"
                          in
                          exit 1))
                    qMatrix1
                with
                  (st43, x46)
                in
                match mtxExpRateSafe st43 x46 with (st44, leftKernel)
                in
                match
                  mtxSclrMul
                    st44
                    (subf
                       (match tree1 with Leaf carried10
                        then
                          carried10.age
                        else match tree1 with Node carried11
                        then
                          carried11.age
                        else
                          let #var"28" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:46-23:54>:\nField \'age\' not found\n[0m  let rightKernel = mtxExpRateSafe(mtxSclrMul([31mtree.age[0m[0m-right.age, qMatrix));\n"
                          in
                          exit 1)
                       (match right with MsgLeaf carried12
                        then
                          carried12.age
                        else match right with MsgNode carried13
                        then
                          carried13.age
                        else
                          let #var"29" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:55-23:64>:\nField \'age\' not found\n[0m  let rightKernel = mtxExpRateSafe(mtxSclrMul(tree.age-[31mright.age[0m[0m, qMatrix));\n"
                          in
                          exit 1))
                    qMatrix1
                with
                  (st45, x47)
                in
                match mtxExpRateSafe st45 x47 with (st46, rightKernel)
                in
                match mtxTrans st46 leftKernel with (st47, x48)
                in
                match
                  mtxMul
                    st47
                    (match left with MsgLeaf carried14
                     then
                       match carried14 with {outMsg = #var"X2"}
                       in
                       p_pure #var"X2"
                     else match left with MsgNode carried15
                     then
                       carried15.outMsg
                     else
                       let #var"210" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 29:25-29:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n"
                       in
                       p_pure (exit 1))
                    x48
                with
                  (st48, leftInMsg)
                in
                match mtxTrans st48 rightKernel with (st49, x49)
                in
                match
                  mtxMul
                    st49
                    (match right with MsgLeaf carried16
                     then
                       match carried16 with {outMsg = #var"X3"}
                       in
                       p_pure #var"X3"
                     else match right with MsgNode carried17
                     then
                       carried17.outMsg
                     else
                       let #var"211" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:26-30:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n"
                       in
                       p_pure (exit 1))
                    x49
                with
                  (st50, rightInMsg)
                in
                match mtxElemMul st50 leftInMsg rightInMsg with (st51, x50)
                in
                (st51, MsgNode
                  { age =
                      match tree1 with Leaf carried18
                      then
                        carried18.age
                      else match tree1 with Node carried19
                      then
                        carried19.age
                      else
                        let #var"212" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 35:10-35:18>:\nField \'age\' not found\n[0m    age = [31mtree.age[0m[0m, label = tree.label,\n"
                        in
                        exit 1,
                    label =
                      match tree1 with Leaf carried20
                      then
                        carried20.label
                      else match tree1 with Node carried21
                      then
                        carried21.label
                      else
                        let #var"213" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 35:28-35:38>:\nField \'label\' not found\n[0m    age = tree.age, label = [31mtree.label[0m[0m,\n"
                        in
                        exit 1,
                    left = left,
                    right = right,
                    rightKernel = rightKernel,
                    leftKernel = leftKernel,
                    outMsg = x50,
                    leftInMsg = leftInMsg,
                    rightInMsg = rightInMsg })
  in
  let anon11 = lam x1199.
      addi x1199 1 in
  recursive
    let rec33 =
      lam i13.
        lam acc14.
          match geqi i13 0 with true
          then
            rec33 (subi i13 1) (cons (anon11 i13) acc14)
          else
            acc14
  in
  let anon12 =
    lam st780.
      lam mtx1.
        lam i101.
          lam x1198.
            mtxGet st780 i101 x1198 mtx1
  in
  recursive
    let rec6 =
      lam st52.
        lam c21.
          lam c22.
            lam s5.
              match s5 with [ _,
                  _ ] ++ _
              then
                match anon12 st52 c21 c22 (get s5 0) with (st53, x51)
                in
                match splitAt s5 1 with {#label"1" = x52}
                in
                match rec6 st53 c21 c22 x52 with (st54, x53)
                in
                (st54, cons x51 x53)
              else match s5 with [ e7 ]
              then
                match splitAt s5 1 with {#label"1" = x54}
                in
                let slice6 = x54 in
                match anon12 st52 c21 c22 e7 with (st55, x55)
                in
                (st55, [ x55 ])
              else match s5 with ""
              in
              (st52, "")
  in
  let anon13 =
    lam st777.
      lam s72.
        lam x1193.
          match
            p_map
              st777
              (lam x1194.
                 lam x1195.
                   divf x1194 x1195)
              x1193
          with
            (st778, x1196)
          in
          match seqSumReal st778 s72 with (st779, x1197)
          in
          p_apply st779 x1196 x1197
  in
  recursive
    let rec7 =
      lam st56.
        lam c23.
          lam s6.
            match s6 with [ _,
                _ ] ++ _
            then
              match anon13 st56 c23 (get s6 0) with (st57, x56)
              in
              match splitAt s6 1 with {#label"1" = x57}
              in
              match rec7 st57 c23 x57 with (st58, x58)
              in
              (st58, cons x56 x58)
            else match s6 with [ e8 ]
            then
              match splitAt s6 1 with {#label"1" = x59}
              in
              let slice7 = x59 in
              match anon13 st56 c23 e8 with (st59, x60)
              in
              (st59, [ x60 ])
            else match s6 with ""
            in
            (st56, "")
  in
  let hostMsgToProb =
    lam st775.
      lam mtx.
        lam i10.
          let i114 = subi (addi (subi 3 1) 1) 1 in
          match
            rec6
              st775
              mtx
              i10
              (match geqi i114 0 with true
               then
                 rec33 (subi i114 1) (cons (anon11 i114) "")
               else
                 "")
          with
            (st776, s71)
          in
          rec7 st776 s71 s71
  in
  let anon14 =
    lam st772.
      lam samplingProb11.
        lam x1189.
          lam x1190.
            match
              hostMsgToProb st772 samplingProb11 (addi x1189 1)
            with
              (st773, param6)
            in
            p_bind
              st773
              hrmStoreSubmodel
              (hrmInit {})
              (lam st774.
                 lam x1192.
                   match
                     match leqi 0 x1192 with true
                     then
                       lti x1192 (length param6)
                     else
                       false
                   with
                     true
                   then
                     log11 st774 (get param6 (subi (addi x1192 1) 1))
                   else
                     (st774, p_pure (log1 0.)))
              x1190
  in
  recursive
    let rec13 =
      lam st60.
        lam c24.
          lam i5.
            lam s13.
              match s13 with [ _,
                  _ ] ++ _
              then
                match anon14 st60 c24 i5 (get s13 0) with (st61, x61)
                in
                match splitAt s13 1 with {#label"1" = x62}
                in
                match rec13 st61 c24 (addi i5 1) x62 with (st62, x63)
                in
                (st62, cons x61 x63)
              else match s13 with [ e9 ]
              then
                match splitAt s13 1 with {#label"1" = x64}
                in
                let slice8 = x64 in
                match anon14 st60 c24 i5 e9 with (st63, x65)
                in
                (st63, [ x65 ])
              else match s13 with ""
              in
              (st60, "")
  in
  let getRepertoireSamplingDensity =
    lam st770.
      lam x1591.
        lam samplingProb1.
          match rec13 st770 samplingProb1 0 x1591 with (st771, x1188)
          in
          seqSumReal st771 x1188
  in
  let anon15 =
    lam x1186.
      lam x1187.
        match eqi x1187 2 with true
        then
          addi x1186 1
        else
          x1186
  in
  recursive
    let rec27 =
      lam acc7.
        lam s27.
          match s27 with [ _ ] ++ _
          then
            match splitAt s27 1 with {#label"1" = x66}
            in
            rec27 (anon15 acc7 (get s27 0)) x66
          else match s27 with ""
          in
          acc7
    let rec28 =
      lam st64.
        lam acc8.
          lam s28.
            match s28 with [ _ ] ++ _
            then
              match
                p_bind
                  st64
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st65.
                     lam x67.
                       match eqi x67 2 with true
                       then
                         p_map
                           st65 (lam x68.
                              addi x68 1) acc8
                       else
                         (st65, acc8))
                  (get s28 0)
              with
                (st66, x69)
              in
              match splitAt s28 1 with {#label"1" = x70}
              in
              rec28 st66 x69 x70
            else match s28 with ""
            in
            (st64, acc8)
  in
  let count2s =
    lam st768.
      lam repertoire21.
        match repertoire21 with [ _ ] ++ _
        then
          match
            p_map
              st768
              (lam x1183.
                 match eqi x1183 2 with true
                 then
                   addi 0 1
                 else
                   0)
              (get repertoire21 0)
          with
            (st769, x1184)
          in
          match splitAt repertoire21 1 with {#label"1" = x1185}
          in
          rec28 st769 x1184 x1185
        else match repertoire21 with ""
        in
        (st768, p_pure 0)
  in
  let updateRepertoire =
    lam st750.
      lam currRep81.
        lam event31.
          lam nhosts71.
            match
              p_map
                st750
                (lam x1155.
                   match x1155 with Event1 x1572
                   then
                     x1572.host
                   else
                     let #var"2162" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event31
            with
              (st751, hostIndex42)
            in
            match
              p_traverseSeq
                st751
                (lam st752.
                   lam x1156.
                     (st752, x1156))
                currRep81
            with
              (st753, x1157)
            in
            match
              p_map
                st753
                (lam x1158.
                   subsequence x1158 (subi 1 1))
                x1157
            with
              (st754, x1159)
            in
            match
              p_map
                st754
                (lam x1160.
                   subi x1160 1)
                hostIndex42
            with
              (st755, x1163)
            in
            match p_apply st755 x1159 x1163 with (st756, x1164)
            in
            match
              p_map
                st756
                (lam x1165.
                   match x1165 with Event1 x1562
                   then
                     x1562.toState
                   else
                     let #var"2163" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event31
            with
              (st757, x1166)
            in
            match
              p_traverseSeq
                st757
                (lam st758.
                   lam x1167.
                     (st758, x1167))
                [ x1166 ]
            with
              (st759, x1168)
            in
            match
              p_map
                st759
                (lam x1169.
                   addi x1169 1)
                hostIndex42
            with
              (st760, first1)
            in
            match
              p_traverseSeq
                st760
                (lam st761.
                   lam x1170.
                     (st761, x1170))
                currRep81
            with
              (st762, x1173)
            in
            match p_map st762 subsequence x1173 with (st763, x1174)
            in
            match
              p_map st763 (lam x1175.
                   subi x1175 1) first1
            with
              (st764, x1176)
            in
            match p_apply st764 x1174 x1176 with (st765, x1177)
            in
            match
              p_map
                st765
                (lam x1178.
                   subi (addi nhosts71 1) x1178)
                first1
            with
              (st766, x1179)
            in
            match p_apply st766 x1177 x1179 with (st767, x1180)
            in
            paste02
              st767
              [ x1164,
                x1168,
                x1180 ]
  in
  let updateRepertoire1 =
    lam st736.
      lam currRep8.
        lam event3.
          lam nhosts7.
            match
              p_map
                st736
                (lam x1135.
                   match x1135 with Event1 x1571
                   then
                     x1571.host
                   else
                     let #var"2160" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event3
            with
              (st737, hostIndex41)
            in
            match
              p_map
                st737
                (lam x1136.
                   subsequence x1136 (subi 1 1))
                currRep8
            with
              (st738, x1137)
            in
            match
              p_map
                st738
                (lam x1138.
                   subi x1138 1)
                hostIndex41
            with
              (st739, x1139)
            in
            match p_apply st739 x1137 x1139 with (st740, x1140)
            in
            match
              p_map
                st740
                (lam x1143.
                   match x1143 with Event1 x1561
                   then
                     x1561.toState
                   else
                     let #var"2161" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event3
            with
              (st741, x1144)
            in
            match
              p_traverseSeq
                st741
                (lam st742.
                   lam x1145.
                     (st742, x1145))
                [ x1144 ]
            with
              (st743, x1146)
            in
            match
              p_map
                st743
                (lam x1147.
                   addi x1147 1)
                hostIndex41
            with
              (st744, first)
            in
            match p_map st744 subsequence currRep8 with (st745, x1148)
            in
            match
              p_map st745 (lam x1149.
                   subi x1149 1) first
            with
              (st746, x1150)
            in
            match p_apply st746 x1148 x1150 with (st747, x1151)
            in
            match
              p_map
                st747
                (lam x1152.
                   subi (addi nhosts7 1) x1152)
                first
            with
              (st748, x1153)
            in
            match p_apply st748 x1151 x1153 with (st749, x1154)
            in
            paste02
              st749
              [ x1140,
                x1146,
                x1154 ]
  in
  recursive
    let ifCont3 =
      lam st67.
        lam currRep.
          lam eventSeq.
            lam eventIndex.
              lam nEvents.
                lam nhosts2.
                  lam event.
                    lam #var"3".
                      let hostIndex4 =
                        match event with Event1 x157
                        then
                          x157.host
                        else
                          let #var"216" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                          in
                          exit 1
                      in
                      let s29 =
                        [ slice currRep 1 hostIndex4,
                          [ p_pure
                              (match event with Event1 x156
                               then
                                 x156.toState
                               else
                                 let #var"215" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                                 in
                                 exit 1) ],
                          slice currRep (addi hostIndex4 1) (addi nhosts2 1) ]
                      in
                      let currRep1 =
                        match s29 with [ _ ] ++ _
                        then
                          match splitAt s29 1 with {#label"1" = x76}
                          in
                          rec21 (concat "" (get s29 0)) x76
                        else match s29 with ""
                        in
                        ""
                      in
                      let eventIndex1 = addi eventIndex 1 in
                      match gti eventIndex1 nEvents with true
                      then
                        (st67, p_pure true)
                      else match
                        p_map
                          st67
                          (lam x71.
                             get x71 (subi eventIndex1 1))
                          eventSeq
                      with
                        (st68, x72)
                      in
                      p_bind
                        st68
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st69.
                           lam x73.
                             match
                               eqi
                                 (match x73 with Event1 x301
                                  then
                                    x301.fromState
                                  else
                                    let #var"214" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 144:7-144:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                                    in
                                    exit 1)
                                 2
                             with
                               true
                             then
                               match count2s st69 currRep1 with (st70, x74)
                               in
                               p_bind
                                 st70
                                 hrmStoreSubmodel
                                 (hrmInit {})
                                 (lam st71.
                                    lam x75.
                                      match eqi x75 1 with true
                                      then
                                        (st71, p_pure false)
                                      else
                                        ifCont3 st71 currRep1 eventSeq eventIndex1 nEvents nhosts2 x73 0)
                                 x74
                             else
                               ifCont3 st69 currRep1 eventSeq eventIndex1 nEvents nhosts2 x73 0)
                        x72
    let allTimesValidBranch =
      lam st72.
        lam currRep11.
          lam eventSeq1.
            lam eventIndex11.
              lam nEvents1.
                lam nhosts3.
                  p_bind
                    st72
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st73.
                       lam x77.
                         match gti eventIndex11 x77 with true
                         then
                           (st73, p_pure true)
                         else match
                           p_map
                             st73
                             (lam x78.
                                get x78 (subi eventIndex11 1))
                             eventSeq1
                         with
                           (st74, x79)
                         in
                         p_bind
                           st74
                           hrmStoreSubmodel
                           (hrmInit {})
                           (lam st75.
                              lam x80.
                                match
                                  eqi
                                    (match x80 with Event1 x302
                                     then
                                       x302.fromState
                                     else
                                       let #var"217" =
                                         print
                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 144:7-144:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                                       in
                                       exit 1)
                                    2
                                with
                                  true
                                then
                                  match count2s st75 currRep11 with (st76, x81)
                                  in
                                  p_bind
                                    st76
                                    hrmStoreSubmodel
                                    (hrmInit {})
                                    (lam st77.
                                       lam x82.
                                         match eqi x82 1 with true
                                         then
                                           (st77, p_pure false)
                                         else
                                           ifCont3 st77 currRep11 eventSeq1 eventIndex11 x77 nhosts3 x80 0)
                                    x81
                                else
                                  ifCont3 st75 currRep11 eventSeq1 eventIndex11 x77 nhosts3 x80 0)
                           x79)
                    nEvents1
  in
  let anon16 =
    lam x1134.
      match eqi x1134 2 with true
      then
        true
      else
        eqi x1134 1
  in
  let anon17 =
    lam st735.
      lam x1132.
        p_map
          st735
          (lam x1133.
             match eqi x1133 2 with true
             then
               true
             else
               eqi x1133 1)
          x1132
  in
  recursive
    let rec8 =
      lam s7.
        match s7 with [ _,
            _ ] ++ _
        then
          match splitAt s7 1 with {#label"1" = x83}
          in
          cons (anon16 (get s7 0)) (rec8 x83)
        else match s7 with [ e10 ]
        then
          match splitAt s7 1 with {#label"1" = x84}
          in
          let slice9 = x84 in
          [ anon16 e10 ]
        else match s7 with ""
        in
        ""
    let rec9 =
      lam st78.
        lam s8.
          match s8 with [ _,
              _ ] ++ _
          then
            match anon17 st78 (get s8 0) with (st79, x85)
            in
            match splitAt s8 1 with {#label"1" = x86}
            in
            match rec9 st79 x86 with (st80, x87)
            in
            (st80, cons x85 x87)
          else match s8 with [ e11 ]
          then
            match splitAt s8 1 with {#label"1" = x88}
            in
            let slice10 = x88 in
            match anon17 st78 e11 with (st81, x89)
            in
            (st81, [ x89 ])
          else match s8 with ""
          in
          (st78, "")
  in
  let sapply = lam st734.
      lam s102.
        rec9 st734 s102
  in
  let anon18 = lam x1131.
      eqi x1131 2 in
  let anon19 =
    lam st733.
      lam x1129.
        p_map st733 (lam x1130.
             eqi x1130 2) x1129
  in
  recursive
    let rec10 =
      lam s9.
        match s9 with [ _,
            _ ] ++ _
        then
          match splitAt s9 1 with {#label"1" = x90}
          in
          cons (anon18 (get s9 0)) (rec10 x90)
        else match s9 with [ e12 ]
        then
          match splitAt s9 1 with {#label"1" = x91}
          in
          let slice11 = x91 in
          [ anon18 e12 ]
        else match s9 with ""
        in
        ""
    let rec14 =
      lam st82.
        lam s10.
          match s10 with [ _,
              _ ] ++ _
          then
            match anon19 st82 (get s10 0) with (st83, x92)
            in
            match splitAt s10 1 with {#label"1" = x93}
            in
            match rec14 st83 x93 with (st84, x94)
            in
            (st84, cons x92 x94)
          else match s10 with [ e13 ]
          then
            match splitAt s10 1 with {#label"1" = x95}
            in
            let slice12 = x95 in
            match anon19 st82 e13 with (st85, x96)
            in
            (st85, [ x96 ])
          else match s10 with ""
          in
          (st82, "")
  in
  let sapply1 = lam st732.
      lam s101.
        rec14 st732 s101
  in
  let getGainRate =
    lam st724.
      lam repertoire14.
        lam hostIndex33.
          lam modelParams123.
            let fromState53 = get repertoire14 (subi hostIndex33 1) in
            match
              mtxGet
                st724
                (addi fromState53 1)
                (addi (addi fromState53 1) 1)
                (match
                   match modelParams123 with ModelParams1 x1534
                   then
                     x1534.embeddedQMatrix
                   else
                     let #var"2154" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1524
                 then
                   x1524.mat
                 else
                   let #var"2155" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st725, baseRate13)
            in
            match eqi fromState53 0 with true
            then
              match
                p_map
                  st725
                  (lam x1117.
                     lam x1118.
                       mulf x1117 x1118)
                  baseRate13
              with
                (st726, x1119)
              in
              match
                p_map
                  st726
                  (lam x1120.
                     negf x1120)
                  (match modelParams123 with ModelParams1 x1484
                   then
                     x1484.beta
                   else
                     let #var"2156" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                     in
                     p_pure (exit 1))
              with
                (st727, x1121)
              in
              match
                pow1
                  st727
                  (mtxMean
                     (mtxRowCols
                        (match modelParams123 with ModelParams1 x1494
                         then
                           x1494.hostMetric
                         else
                           let #var"2157" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                           in
                           exit 1)
                        hostIndex33
                        (whichTrue (rec8 repertoire14))))
                  x1121
              with
                (st728, x1122)
              in
              p_apply st728 x1119 x1122
            else match
              p_map
                st725
                (lam x1123.
                   lam x1124.
                     mulf x1123 x1124)
                baseRate13
            with
              (st729, x1125)
            in
            match
              p_map
                st729
                (lam x1126.
                   negf x1126)
                (match modelParams123 with ModelParams1 x1504
                 then
                   x1504.beta
                 else
                   let #var"2158" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                   in
                   p_pure (exit 1))
            with
              (st730, x1127)
            in
            match
              pow1
                st730
                (mtxMean
                   (mtxRowCols
                      (match modelParams123 with ModelParams1 x1514
                       then
                         x1514.hostMetric
                       else
                         let #var"2159" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                         in
                         exit 1)
                      hostIndex33
                      (whichTrue (rec10 repertoire14))))
                x1127
            with
              (st731, x1128)
            in
            p_apply st731 x1125 x1128
  in
  let getGainRate1 =
    lam st705.
      lam repertoire13.
        lam hostIndex32.
          lam modelParams122.
            let fromState52 = get repertoire13 (subi hostIndex32 1) in
            match
              p_map
                st705
                (lam x1092.
                   addi x1092 1)
                fromState52
            with
              (st706, x1093)
            in
            match
              p_map
                st706
                (lam x1094.
                   addi (addi x1094 1) 1)
                fromState52
            with
              (st707, x1095)
            in
            match
              mtxGet2
                st707
                x1093
                x1095
                (match
                   match modelParams122 with ModelParams1 x1533
                   then
                     x1533.embeddedQMatrix
                   else
                     let #var"2148" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1523
                 then
                   x1523.mat
                 else
                   let #var"2149" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st708, baseRate12)
            in
            p_bind
              st708
              hrmStoreSubmodel
              (hrmInit {})
              (lam st709.
                 lam x1096.
                   match eqi x1096 0 with true
                   then
                     match
                       p_map
                         st709
                         (lam x1097.
                            lam x1098.
                              mulf x1097 x1098)
                         baseRate12
                     with
                       (st710, x1099)
                     in
                     match sapply st710 repertoire13 with (st711, x1100)
                     in
                     match whichTrue1 st711 x1100 with (st712, x1101)
                     in
                     match
                       mtxRowCols1
                         st712
                         (match modelParams122 with ModelParams1 x1493
                          then
                            x1493.hostMetric
                          else
                            let #var"2150" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex32
                         x1101
                     with
                       (st713, x1102)
                     in
                     match mtxMean1 st713 x1102 with (st714, x1103)
                     in
                     match
                       p_map
                         st714
                         (lam x1104.
                            negf x1104)
                         (match modelParams122 with ModelParams1 x1483
                          then
                            x1483.beta
                          else
                            let #var"2151" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st715, x1105)
                     in
                     match pow2 st715 x1103 x1105 with (st716, x1106)
                     in
                     p_apply st716 x1099 x1106
                   else match
                     p_map
                       st709
                       (lam x1107.
                          lam x1108.
                            mulf x1107 x1108)
                       baseRate12
                   with
                     (st717, x1109)
                   in
                   match sapply1 st717 repertoire13 with (st718, x1110)
                   in
                   match whichTrue1 st718 x1110 with (st719, x1111)
                   in
                   match
                     mtxRowCols1
                       st719
                       (match modelParams122 with ModelParams1 x1513
                        then
                          x1513.hostMetric
                        else
                          let #var"2152" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex32
                       x1111
                   with
                     (st720, x1112)
                   in
                   match mtxMean1 st720 x1112 with (st721, x1113)
                   in
                   match
                     p_map
                       st721
                       (lam x1114.
                          negf x1114)
                       (match modelParams122 with ModelParams1 x1503
                        then
                          x1503.beta
                        else
                          let #var"2153" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st722, x1115)
                   in
                   match pow2 st722 x1113 x1115 with (st723, x1116)
                   in
                   p_apply st723 x1109 x1116)
              fromState52
  in
  let getGainRate2 =
    lam st681.
      lam repertoire12.
        lam hostIndex31.
          lam modelParams121.
            match
              p_traverseSeq
                st681
                (lam st682.
                   lam x1061.
                     (st682, x1061))
                repertoire12
            with
              (st683, x1062)
            in
            match p_map st683 get x1062 with (st684, x1063)
            in
            match
              p_map
                st684
                (lam x1064.
                   subi x1064 1)
                hostIndex31
            with
              (st685, x1065)
            in
            match p_apply st685 x1063 x1065 with (st686, fromState51)
            in
            match
              p_map
                st686
                (lam x1066.
                   addi x1066 1)
                fromState51
            with
              (st687, x1067)
            in
            match
              p_map
                st687
                (lam x1068.
                   addi (addi x1068 1) 1)
                fromState51
            with
              (st688, x1069)
            in
            match
              mtxGet2
                st688
                x1067
                x1069
                (match
                   match modelParams121 with ModelParams1 x1532
                   then
                     x1532.embeddedQMatrix
                   else
                     let #var"2142" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1522
                 then
                   x1522.mat
                 else
                   let #var"2143" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st689, baseRate11)
            in
            p_bind
              st689
              hrmStoreSubmodel
              (hrmInit {})
              (lam st690.
                 lam x1070.
                   match eqi x1070 0 with true
                   then
                     match
                       p_map
                         st690
                         (lam x1071.
                            lam x1072.
                              mulf x1071 x1072)
                         baseRate11
                     with
                       (st691, x1073)
                     in
                     match sapply st691 repertoire12 with (st692, x1074)
                     in
                     match whichTrue1 st692 x1074 with (st693, x1075)
                     in
                     match
                       mtxRowCols2
                         st693
                         (match modelParams121 with ModelParams1 x1492
                          then
                            x1492.hostMetric
                          else
                            let #var"2144" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex31
                         x1075
                     with
                       (st694, x1076)
                     in
                     match mtxMean1 st694 x1076 with (st695, x1077)
                     in
                     match
                       p_map
                         st695
                         (lam x1078.
                            negf x1078)
                         (match modelParams121 with ModelParams1 x1482
                          then
                            x1482.beta
                          else
                            let #var"2145" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st696, x1079)
                     in
                     match pow2 st696 x1077 x1079 with (st697, x1080)
                     in
                     p_apply st697 x1073 x1080
                   else match
                     p_map
                       st690
                       (lam x1081.
                          lam x1082.
                            mulf x1081 x1082)
                       baseRate11
                   with
                     (st698, x1083)
                   in
                   match sapply1 st698 repertoire12 with (st699, x1084)
                   in
                   match whichTrue1 st699 x1084 with (st700, x1085)
                   in
                   match
                     mtxRowCols2
                       st700
                       (match modelParams121 with ModelParams1 x1512
                        then
                          x1512.hostMetric
                        else
                          let #var"2146" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex31
                       x1085
                   with
                     (st701, x1086)
                   in
                   match mtxMean1 st701 x1086 with (st702, x1087)
                   in
                   match
                     p_map
                       st702
                       (lam x1088.
                          negf x1088)
                       (match modelParams121 with ModelParams1 x1502
                        then
                          x1502.beta
                        else
                          let #var"2147" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st703, x1089)
                   in
                   match pow2 st703 x1087 x1089 with (st704, x1090)
                   in
                   p_apply st704 x1083 x1090)
              fromState51
  in
  let getGainRate3 =
    lam st659.
      lam repertoire11.
        lam hostIndex3.
          lam modelParams12.
            match p_map st659 get repertoire11 with (st660, x1027)
            in
            match
              p_map
                st660 (lam x1028.
                   subi x1028 1) hostIndex3
            with
              (st661, x1029)
            in
            match p_apply st661 x1027 x1029 with (st662, fromState5)
            in
            match
              p_map
                st662 (lam x1030.
                   addi x1030 1) fromState5
            with
              (st663, x1031)
            in
            match
              p_map
                st663
                (lam x1032.
                   addi (addi x1032 1) 1)
                fromState5
            with
              (st664, x1033)
            in
            match
              mtxGet2
                st664
                x1031
                x1033
                (match
                   match modelParams12 with ModelParams1 x1531
                   then
                     x1531.embeddedQMatrix
                   else
                     let #var"2136" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1521
                 then
                   x1521.mat
                 else
                   let #var"2137" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st665, baseRate1)
            in
            p_bind
              st665
              hrmStoreSubmodel
              (hrmInit {})
              (lam st666.
                 lam x1034.
                   match eqi x1034 0 with true
                   then
                     match
                       p_map
                         st666
                         (lam x1035.
                            lam x1036.
                              mulf x1035 x1036)
                         baseRate1
                     with
                       (st667, x1037)
                     in
                     match
                       p_map
                         st667
                         (lam x1038.
                            match x1038 with [ _,
                                _ ] ++ _
                            then
                              match splitAt x1038 1 with {#label"1" = x1039}
                              in
                              cons (anon16 (get x1038 0)) (rec8 x1039)
                            else match x1038 with [ e19 ]
                            then
                              match splitAt x1038 1 with {#label"1" = x1040}
                              in
                              let slice18 = x1040 in
                              [ anon16 e19 ]
                            else match x1038 with ""
                            in
                            "")
                         repertoire11
                     with
                       (st668, x1041)
                     in
                     match whichTrue2 st668 x1041 with (st669, x1042)
                     in
                     match
                       mtxRowCols2
                         st669
                         (match modelParams12 with ModelParams1 x1491
                          then
                            x1491.hostMetric
                          else
                            let #var"2138" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex3
                         x1042
                     with
                       (st670, x1043)
                     in
                     match mtxMean1 st670 x1043 with (st671, x1044)
                     in
                     match
                       p_map
                         st671
                         (lam x1045.
                            negf x1045)
                         (match modelParams12 with ModelParams1 x1481
                          then
                            x1481.beta
                          else
                            let #var"2139" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st672, x1046)
                     in
                     match pow2 st672 x1044 x1046 with (st673, x1047)
                     in
                     p_apply st673 x1037 x1047
                   else match
                     p_map
                       st666
                       (lam x1048.
                          lam x1049.
                            mulf x1048 x1049)
                       baseRate1
                   with
                     (st674, x1050)
                   in
                   match
                     p_map
                       st674
                       (lam x1051.
                          match x1051 with [ _,
                              _ ] ++ _
                          then
                            match splitAt x1051 1 with {#label"1" = x1052}
                            in
                            cons (anon18 (get x1051 0)) (rec10 x1052)
                          else match x1051 with [ e20 ]
                          then
                            match splitAt x1051 1 with {#label"1" = x1053}
                            in
                            let slice19 = x1053 in
                            [ anon18 e20 ]
                          else match x1051 with ""
                          in
                          "")
                       repertoire11
                   with
                     (st675, x1054)
                   in
                   match whichTrue2 st675 x1054 with (st676, x1055)
                   in
                   match
                     mtxRowCols2
                       st676
                       (match modelParams12 with ModelParams1 x1511
                        then
                          x1511.hostMetric
                        else
                          let #var"2140" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex3
                       x1055
                   with
                     (st677, x1056)
                   in
                   match mtxMean1 st677 x1056 with (st678, x1057)
                   in
                   match
                     p_map
                       st678
                       (lam x1058.
                          negf x1058)
                       (match modelParams12 with ModelParams1 x1501
                        then
                          x1501.beta
                        else
                          let #var"2141" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st679, x1059)
                   in
                   match pow2 st679 x1057 x1059 with (st680, x1060)
                   in
                   p_apply st680 x1050 x1060)
              fromState5
  in
  let getLossRate =
    lam st658.
      lam repertoire3.
        lam hostIndex23.
          lam modelParams103.
            let fromState33 = get repertoire3 (subi hostIndex23 1) in
            match
              match eqi fromState33 2 with true
              then
                eqi (rec27 0 repertoire3) 1
              else
                false
            with
              true
            then
              (st658, p_pure 0.)
            else
              mtxGet
                st658
                (addi fromState33 1)
                (addi (subi fromState33 1) 1)
                (match
                   match modelParams103 with ModelParams1 x1464
                   then
                     x1464.embeddedQMatrix
                   else
                     let #var"2134" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1454
                 then
                   x1454.mat
                 else
                   let #var"2135" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
  in
  let getLossRate1 =
    lam st651.
      lam repertoire2.
        lam hostIndex22.
          lam modelParams102.
            let fromState32 = get repertoire2 (subi hostIndex22 1) in
            match
              p_bind
                st651
                hrmStoreSubmodel
                (hrmInit {})
                (lam st652.
                   lam x1017.
                     match eqi x1017 2 with true
                     then
                       match count2s st652 repertoire2 with (st653, x1018)
                       in
                       p_map
                         st653
                         (lam x1019.
                            eqi x1019 1)
                         x1018
                     else
                       (st652, p_pure false))
                fromState32
            with
              (st654, x1020)
            in
            p_bind
              st654
              hrmStoreSubmodel
              (hrmInit {})
              (lam st655.
                 lam x1022.
                   match x1022 with true
                   then
                     (st655, p_pure 0.)
                   else match
                     p_map
                       st655
                       (lam x1023.
                          addi x1023 1)
                       fromState32
                   with
                     (st656, x1024)
                   in
                   match
                     p_map
                       st656
                       (lam x1025.
                          addi (subi x1025 1) 1)
                       fromState32
                   with
                     (st657, x1026)
                   in
                   mtxGet2
                     st657
                     x1024
                     x1026
                     (match
                        match modelParams102 with ModelParams1 x1463
                        then
                          x1463.embeddedQMatrix
                        else
                          let #var"2132" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1453
                      then
                        x1453.mat
                      else
                        let #var"2133" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x1020
  in
  let getLossRate2 =
    lam st639.
      lam repertoire1.
        lam hostIndex21.
          lam modelParams101.
            match
              p_traverseSeq
                st639
                (lam st640.
                   lam x1002.
                     (st640, x1002))
                repertoire1
            with
              (st641, x1003)
            in
            match p_map st641 get x1003 with (st642, x1004)
            in
            match
              p_map
                st642
                (lam x1005.
                   subi x1005 1)
                hostIndex21
            with
              (st643, x1006)
            in
            match p_apply st643 x1004 x1006 with (st644, fromState31)
            in
            match
              p_bind
                st644
                hrmStoreSubmodel
                (hrmInit {})
                (lam st645.
                   lam x1007.
                     match eqi x1007 2 with true
                     then
                       match count2s st645 repertoire1 with (st646, x1008)
                       in
                       p_map
                         st646
                         (lam x1009.
                            eqi x1009 1)
                         x1008
                     else
                       (st645, p_pure false))
                fromState31
            with
              (st647, x1010)
            in
            p_bind
              st647
              hrmStoreSubmodel
              (hrmInit {})
              (lam st648.
                 lam x1012.
                   match x1012 with true
                   then
                     (st648, p_pure 0.)
                   else match
                     p_map
                       st648
                       (lam x1013.
                          addi x1013 1)
                       fromState31
                   with
                     (st649, x1014)
                   in
                   match
                     p_map
                       st649
                       (lam x1015.
                          addi (subi x1015 1) 1)
                       fromState31
                   with
                     (st650, x1016)
                   in
                   mtxGet2
                     st650
                     x1014
                     x1016
                     (match
                        match modelParams101 with ModelParams1 x1462
                        then
                          x1462.embeddedQMatrix
                        else
                          let #var"2130" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1452
                      then
                        x1452.mat
                      else
                        let #var"2131" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x1010
  in
  let getLossRate3 =
    lam st629.
      lam repertoire.
        lam hostIndex2.
          lam modelParams10.
            match p_map st629 get repertoire with (st630, x988)
            in
            match
              p_map st630 (lam x989.
                   subi x989 1) hostIndex2
            with
              (st631, x990)
            in
            match p_apply st631 x988 x990 with (st632, fromState3)
            in
            match
              p_bind
                st632
                hrmStoreSubmodel
                (hrmInit {})
                (lam st633.
                   lam x991.
                     match eqi x991 2 with true
                     then
                       match
                         p_map
                           st633
                           (lam x992.
                              match x992 with [ _ ] ++ _
                              then
                                match splitAt x992 1 with {#label"1" = x993}
                                in
                                rec27 (anon15 0 (get x992 0)) x993
                              else match x992 with ""
                              in
                              0)
                           repertoire
                       with
                         (st634, x994)
                       in
                       p_map
                         st634 (lam x995.
                            eqi x995 1) x994
                     else
                       (st633, p_pure false))
                fromState3
            with
              (st635, x996)
            in
            p_bind
              st635
              hrmStoreSubmodel
              (hrmInit {})
              (lam st636.
                 lam x997.
                   match x997 with true
                   then
                     (st636, p_pure 0.)
                   else match
                     p_map
                       st636
                       (lam x998.
                          addi x998 1)
                       fromState3
                   with
                     (st637, x999)
                   in
                   match
                     p_map
                       st637
                       (lam x1000.
                          addi (subi x1000 1) 1)
                       fromState3
                   with
                     (st638, x1001)
                   in
                   mtxGet2
                     st638
                     x999
                     x1001
                     (match
                        match modelParams10 with ModelParams1 x1461
                        then
                          x1461.embeddedQMatrix
                        else
                          let #var"2128" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1451
                      then
                        x1451.mat
                      else
                        let #var"2129" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x996
  in
  recursive
    let rec29 =
      lam st86.
        lam c25.
          lam c26.
            lam acc9.
              lam s210.
                match s210 with [ _ ] ++ _
                then
                  let x97 = get s210 0 in
                  match
                    p_bind
                      st86
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st87.
                         lam x98.
                           match eqi x98 2 with true
                           then
                             (st87, acc9)
                           else match
                             p_map
                               st87
                               (lam x99.
                                  lam x100.
                                    addf x99 x100)
                               acc9
                           with
                             (st88, x101)
                           in
                           match getGainRate1 st88 c25 x97 c26 with (st89, x102)
                           in
                           p_apply st89 x101 x102)
                      (get c25 (subi x97 1))
                  with
                    (st90, x103)
                  in
                  match splitAt s210 1 with {#label"1" = x104}
                  in
                  rec29 st90 c25 c26 x103 x104
                else match s210 with ""
                in
                (st86, acc9)
    let rec210 =
      lam st91.
        lam c27.
          lam c28.
            lam acc10.
              lam s211.
                match s211 with [ _ ] ++ _
                then
                  let x105 = get s211 0 in
                  match
                    p_bind
                      st91
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st92.
                         lam x106.
                           match eqi (get x106 (subi x105 1)) 2 with true
                           then
                             (st92, acc10)
                           else match
                             p_map
                               st92
                               (lam x107.
                                  lam x108.
                                    addf x107 x108)
                               acc10
                           with
                             (st93, x109)
                           in
                           match getGainRate st93 x106 x105 c28 with (st94, x110)
                           in
                           p_apply st94 x109 x110)
                      c27
                  with
                    (st95, x111)
                  in
                  match splitAt s211 1 with {#label"1" = x112}
                  in
                  rec210 st95 c27 c28 x111 x112
                else match s211 with ""
                in
                (st91, acc10)
  in
  let anon20 = lam x987.
      addi x987 1 in
  recursive
    let rec34 =
      lam i14.
        lam acc15.
          match geqi i14 0 with true
          then
            rec34 (subi i14 1) (cons (anon20 i14) acc15)
          else
            acc15
  in
  let create11 =
    lam l63.
      let i113 = subi l63 1 in
      match geqi i113 0 with true
      then
        rec34 (subi i113 1) (cons (anon20 i113) "")
      else
        ""
  in
  recursive
    let rec211 =
      lam st96.
        lam c29.
          lam c30.
            lam acc16.
              lam s212.
                match s212 with [ _ ] ++ _
                then
                  let x113 = get s212 0 in
                  match
                    p_bind
                      st96
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st97.
                         lam x114.
                           match eqi x114 0 with true
                           then
                             (st97, acc16)
                           else match
                             p_map
                               st97
                               (lam x115.
                                  lam x116.
                                    addf x115 x116)
                               acc16
                           with
                             (st98, x117)
                           in
                           match getLossRate1 st98 c29 x113 c30 with (st99, x118)
                           in
                           p_apply st99 x117 x118)
                      (get c29 (subi x113 1))
                  with
                    (st100, x119)
                  in
                  match splitAt s212 1 with {#label"1" = x120}
                  in
                  rec211 st100 c29 c30 x119 x120
                else match s212 with ""
                in
                (st96, acc16)
    let rec212 =
      lam st101.
        lam c31.
          lam c32.
            lam acc17.
              lam s213.
                match s213 with [ _ ] ++ _
                then
                  let x121 = get s213 0 in
                  match
                    p_bind
                      st101
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st102.
                         lam x122.
                           match eqi (get x122 (subi x121 1)) 0 with true
                           then
                             (st102, acc17)
                           else match
                             p_map
                               st102
                               (lam x123.
                                  lam x124.
                                    addf x123 x124)
                               acc17
                           with
                             (st103, x125)
                           in
                           match getLossRate st103 x122 x121 c32 with (st104, x126)
                           in
                           p_apply st104 x125 x126)
                      c31
                  with
                    (st105, x127)
                  in
                  match splitAt s213 1 with {#label"1" = x128}
                  in
                  rec212 st105 c31 c32 x127 x128
                else match s213 with ""
                in
                (st101, acc17)
  in
  let anon21 = lam x986.
      addi x986 1 in
  recursive
    let rec35 =
      lam i15.
        lam acc18.
          match geqi i15 0 with true
          then
            rec35 (subi i15 1) (cons (anon21 i15) acc18)
          else
            acc18
  in
  let create12 =
    lam l62.
      let i112 = subi l62 1 in
      match geqi i112 0 with true
      then
        rec35 (subi i112 1) (cons (anon21 i112) "")
      else
        ""
  in
  let getTotalRate =
    lam st619.
      lam currRep51.
        lam modelParams81.
          lam nhosts61.
            let s225 = create11 (addi (subi nhosts61 1) 1) in
            match
              match s225 with [ _ ] ++ _
              then
                let x967 = get s225 0 in
                match
                  p_bind
                    st619
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st620.
                       lam x968.
                         match eqi x968 2 with true
                         then
                           (st620, p_pure 0.)
                         else match getGainRate1 st620 currRep51 x967 modelParams81 with (st621, x969)
                         in
                         p_map
                           st621
                           (lam x970.
                              addf 0. x970)
                           x969)
                    (get currRep51 (subi x967 1))
                with
                  (st622, x972)
                in
                match splitAt s225 1 with {#label"1" = x973}
                in
                rec29 st622 currRep51 modelParams81 x972 x973
              else match s225 with ""
              in
              (st619, p_pure 0.)
            with
              (st623, x974)
            in
            match
              p_map
                st623
                (lam x975.
                   lam x976.
                     addf x975 x976)
                x974
            with
              (st624, x977)
            in
            let s226 = create12 (addi (subi nhosts61 1) 1) in
            match
              match s226 with [ _ ] ++ _
              then
                let x978 = get s226 0 in
                match
                  p_bind
                    st624
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st625.
                       lam x979.
                         match eqi x979 0 with true
                         then
                           (st625, p_pure 0.)
                         else match getLossRate1 st625 currRep51 x978 modelParams81 with (st626, x980)
                         in
                         p_map
                           st626
                           (lam x982.
                              addf 0. x982)
                           x980)
                    (get currRep51 (subi x978 1))
                with
                  (st627, x983)
                in
                match splitAt s226 1 with {#label"1" = x984}
                in
                rec211 st627 currRep51 modelParams81 x983 x984
              else match s226 with ""
              in
              (st624, p_pure 0.)
            with
              (st628, x985)
            in
            p_apply st628 x977 x985
  in
  let getTotalRate1 =
    lam st609.
      lam currRep5.
        lam modelParams8.
          lam nhosts6.
            let s223 = create11 (addi (subi nhosts6 1) 1) in
            match
              match s223 with [ _ ] ++ _
              then
                let x948 = get s223 0 in
                match
                  p_bind
                    st609
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st610.
                       lam x949.
                         match eqi (get x949 (subi x948 1)) 2 with true
                         then
                           (st610, p_pure 0.)
                         else match getGainRate st610 x949 x948 modelParams8 with (st611, x950)
                         in
                         p_map
                           st611
                           (lam x952.
                              addf 0. x952)
                           x950)
                    currRep5
                with
                  (st612, x953)
                in
                match splitAt s223 1 with {#label"1" = x954}
                in
                rec210 st612 currRep5 modelParams8 x953 x954
              else match s223 with ""
              in
              (st609, p_pure 0.)
            with
              (st613, x955)
            in
            match
              p_map
                st613
                (lam x956.
                   lam x957.
                     addf x956 x957)
                x955
            with
              (st614, x958)
            in
            let s224 = create12 (addi (subi nhosts6 1) 1) in
            match
              match s224 with [ _ ] ++ _
              then
                let x959 = get s224 0 in
                match
                  p_bind
                    st614
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st615.
                       lam x960.
                         match eqi (get x960 (subi x959 1)) 0 with true
                         then
                           (st615, p_pure 0.)
                         else match getLossRate st615 x960 x959 modelParams8 with (st616, x962)
                         in
                         p_map
                           st616
                           (lam x963.
                              addf 0. x963)
                           x962)
                    currRep5
                with
                  (st617, x964)
                in
                match splitAt s224 1 with {#label"1" = x965}
                in
                rec212 st617 currRep5 modelParams8 x964 x965
              else match s224 with ""
              in
              (st614, p_pure 0.)
            with
              (st618, x966)
            in
            p_apply st618 x958 x966
  in
  recursive
    let fullModelWeight =
      lam st106.
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
                                st106
                                (lam x129.
                                   lam x130.
                                     mulf (negf (subf x129 finalAge)) x130)
                                currAge
                            with
                              (st107, x131)
                            in
                            match
                              getTotalRate1 st107 currRep3 modelParams nhosts5
                            with
                              (st108, x132)
                            in
                            p_apply st108 x131 x132
                          else match
                            p_map
                              st106
                              (lam x133.
                                 get x133 (subi nextIndex 1))
                              eventSeq3
                          with
                            (st109, nextEvent)
                          in
                          match
                            p_map
                              st109
                              (lam x134.
                                 match x134 with Event1 x311
                                 then
                                   x311.eventTime
                                 else
                                   let #var"218" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 25:17-25:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st110, newAge)
                          in
                          match
                            getTotalRate1 st110 currRep3 modelParams nhosts5
                          with
                            (st111, totalLeavingRate1)
                          in
                          match
                            p_map
                              st111
                              (lam x135.
                                 match x135 with Event1 x143
                                 then
                                   x143.host
                                 else
                                   let #var"219" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st112, hostIndex1)
                          in
                          match
                            p_map
                              st112
                              (lam x136.
                                 lam x137.
                                   lam st113.
                                     match
                                       gti
                                         (match x136 with Event1 x141
                                          then
                                            x141.fromState
                                          else
                                            let #var"220" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x137
                                     with
                                       true
                                     then
                                       getLossRate3 st113 currRep3 hostIndex1 modelParams
                                     else
                                       getGainRate3 st113 currRep3 hostIndex1 modelParams)
                              nextEvent
                          with
                            (st114, x138)
                          in
                          match
                            p_map
                              st114
                              (lam x139.
                                 match x139 with Event1 x142
                                 then
                                   x142.toState
                                 else
                                   let #var"221" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st115, x140)
                          in
                          match
                            p_subApply st115 hrmStoreSubmodel (hrmInit {}) x138 x140
                          with
                            (st116, x144)
                          in
                          match p_join st116 x144 with (st117, x145)
                          in
                          match
                            p_map
                              st117
                              (lam x146.
                                 lam x147.
                                   divf x146 x147)
                              x145
                          with
                            (st118, x148)
                          in
                          match p_apply st118 x148 totalLeavingRate1 with (st119, x149)
                          in
                          match log11 st119 x149 with (st120, x150)
                          in
                          match
                            p_map
                              st120
                              (lam x151.
                                 lam x152.
                                   lam x153.
                                     addf (subf x151 x152) x153)
                              x150
                          with
                            (st121, x154)
                          in
                          match
                            p_map
                              st121
                              (lam x155.
                                 lam x158.
                                   lam x159.
                                     mulf (subf x155 x158) x159)
                              currAge
                          with
                            (st122, x160)
                          in
                          match p_apply st122 x160 newAge with (st123, x161)
                          in
                          match p_apply st123 x161 totalLeavingRate1 with (st124, x162)
                          in
                          match p_apply st124 x154 x162 with (st125, x163)
                          in
                          match
                            updateRepertoire1 st125 currRep3 nextEvent nhosts5
                          with
                            (st126, x164)
                          in
                          match
                            fullModelWeight
                              st126
                              (addi nextIndex 1)
                              x164
                              finalRep
                              newAge
                              finalAge
                              eventSeq3
                              nEvents3
                              nhosts5
                              modelParams
                          with
                            (st127, x165)
                          in
                          p_apply st127 x163 x165
    let fullModelWeight1 =
      lam st128.
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
                                st128
                                (lam x166.
                                   lam x167.
                                     mulf (negf (subf x166 finalAge1)) x167)
                                currAge1
                            with
                              (st129, x168)
                            in
                            match
                              getTotalRate1 st129 currRep31 modelParams1 nhosts51
                            with
                              (st130, x169)
                            in
                            p_apply st130 x168 x169
                          else match
                            p_map
                              st128
                              (lam x170.
                                 get x170 (subi nextIndex1 1))
                              eventSeq31
                          with
                            (st131, nextEvent1)
                          in
                          match
                            p_map
                              st131
                              (lam x171.
                                 match x171 with Event1 x312
                                 then
                                   x312.eventTime
                                 else
                                   let #var"222" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 25:17-25:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st132, newAge1)
                          in
                          match
                            getTotalRate1 st132 currRep31 modelParams1 nhosts51
                          with
                            (st133, totalLeavingRate11)
                          in
                          match
                            p_map
                              st133
                              (lam x172.
                                 match x172 with Event1 x1431
                                 then
                                   x1431.host
                                 else
                                   let #var"223" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st134, hostIndex11)
                          in
                          match
                            p_map
                              st134
                              (lam x173.
                                 lam x174.
                                   lam st135.
                                     match
                                       gti
                                         (match x173 with Event1 x1411
                                          then
                                            x1411.fromState
                                          else
                                            let #var"224" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x174
                                     with
                                       true
                                     then
                                       getLossRate3 st135 currRep31 hostIndex11 modelParams1
                                     else
                                       getGainRate3 st135 currRep31 hostIndex11 modelParams1)
                              nextEvent1
                          with
                            (st136, x175)
                          in
                          match
                            p_map
                              st136
                              (lam x176.
                                 match x176 with Event1 x1421
                                 then
                                   x1421.toState
                                 else
                                   let #var"225" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st137, x177)
                          in
                          match
                            p_subApply st137 hrmStoreSubmodel (hrmInit {}) x175 x177
                          with
                            (st138, x178)
                          in
                          match p_join st138 x178 with (st139, x179)
                          in
                          match
                            p_map
                              st139
                              (lam x180.
                                 lam x181.
                                   divf x180 x181)
                              x179
                          with
                            (st140, x182)
                          in
                          match p_apply st140 x182 totalLeavingRate11 with (st141, x183)
                          in
                          match log11 st141 x183 with (st142, x184)
                          in
                          match
                            p_map
                              st142
                              (lam x185.
                                 lam x186.
                                   lam x187.
                                     addf (subf x185 x186) x187)
                              x184
                          with
                            (st143, x188)
                          in
                          match
                            p_map
                              st143
                              (lam x189.
                                 lam x190.
                                   lam x191.
                                     mulf (subf x189 x190) x191)
                              currAge1
                          with
                            (st144, x192)
                          in
                          match p_apply st144 x192 newAge1 with (st145, x193)
                          in
                          match p_apply st145 x193 totalLeavingRate11 with (st146, x194)
                          in
                          match p_apply st146 x188 x194 with (st147, x195)
                          in
                          match
                            updateRepertoire1 st147 currRep31 nextEvent1 nhosts51
                          with
                            (st148, x196)
                          in
                          match
                            fullModelWeight1
                              st148
                              (addi nextIndex1 1)
                              x196
                              finalRep1
                              newAge1
                              finalAge1
                              eventSeq31
                              nEvents31
                              nhosts51
                              modelParams1
                          with
                            (st149, x197)
                          in
                          p_apply st149 x195 x197
  in
  recursive
    let hostIndepLikelihood =
      lam st150.
        lam nextIndex11.
          lam currState.
            lam finalState.
              lam currAge11.
                lam finalAge11.
                  lam eventSeq4.
                    lam embeddedQMatrix.
                      match length13 st150 eventSeq4 with (st151, x198)
                      in
                      p_bind
                        st151
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st152.
                           lam x199.
                             match gti nextIndex11 x199 with true
                             then
                               match
                                 p_traverseSeq
                                   st152
                                   (lam st153.
                                      lam x200.
                                        (st153, x200))
                                   (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x321
                                    then
                                      x321.totalRates
                                    else
                                      let #var"226" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x201.
                                           p_pure x201)
                                        (exit 1))
                               with
                                 (st154, x202)
                               in
                               match
                                 p_map
                                   st154
                                   (lam x203.
                                      lam x204.
                                        mulf (negf (subf currAge11 finalAge11)) (get x203 x204))
                                   x202
                               with
                                 (st155, x205)
                               in
                               match
                                 p_map
                                   st155
                                   (lam x206.
                                      subi (addi x206 1) 1)
                                   currState
                               with
                                 (st156, x207)
                               in
                               p_apply st156 x205 x207
                             else match
                               p_map
                                 st152
                                 (lam x208.
                                    get x208 (subi nextIndex11 1))
                                 eventSeq4
                             with
                               (st157, nextEvent11)
                             in
                             match
                               p_map
                                 st157
                                 (lam x209.
                                    match x209 with Event1 x361
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
                               (st158, nextState)
                             in
                             match
                               p_map
                                 st158
                                 (lam x210.
                                    match x210 with Event1 x351
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
                               (st159, nextAge)
                             in
                             match
                               p_traverseSeq
                                 st159
                                 (lam st160.
                                    lam x211.
                                      p_traverseSeq
                                        st160
                                        (lam st161.
                                           lam x212.
                                             (st161, x212))
                                        x211)
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x331
                                  then
                                    x331.transitionProbs
                                  else
                                    let #var"229" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x213.
                                         map
                                           (lam x214.
                                              p_pure x214)
                                           x213)
                                      (exit 1))
                             with
                               (st162, x215)
                             in
                             match
                               p_map
                                 st162
                                 (lam x216.
                                    lam x217.
                                      get (get x216 x217))
                                 x215
                             with
                               (st163, x218)
                             in
                             match
                               p_map
                                 st163
                                 (lam x219.
                                    subi (addi x219 1) 1)
                                 currState
                             with
                               (st164, x220)
                             in
                             match p_apply st164 x218 x220 with (st165, x222)
                             in
                             match
                               p_map
                                 st165
                                 (lam x223.
                                    subi (addi x223 1) 1)
                                 nextState
                             with
                               (st166, x224)
                             in
                             match p_apply st166 x222 x224 with (st167, x225)
                             in
                             match log11 st167 x225 with (st168, x226)
                             in
                             match
                               p_map
                                 st168
                                 (lam x227.
                                    lam x228.
                                      lam x229.
                                        addf (subf x227 x228) x229)
                                 x226
                             with
                               (st169, x230)
                             in
                             match
                               p_map
                                 st169
                                 (lam x232.
                                    lam x233.
                                      mulf (subf currAge11 x232) x233)
                                 nextAge
                             with
                               (st170, x234)
                             in
                             match
                               p_traverseSeq
                                 st170
                                 (lam st171.
                                    lam x235.
                                      (st171, x235))
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x341
                                  then
                                    x341.totalRates
                                  else
                                    let #var"230" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x236.
                                         p_pure x236)
                                      (exit 1))
                             with
                               (st172, x237)
                             in
                             match p_map st172 get x237 with (st173, x238)
                             in
                             match
                               p_map
                                 st173
                                 (lam x239.
                                    subi (addi x239 1) 1)
                                 currState
                             with
                               (st174, x240)
                             in
                             match p_apply st174 x238 x240 with (st175, x241)
                             in
                             match p_apply st175 x234 x241 with (st176, x242)
                             in
                             match p_apply st176 x230 x242 with (st177, x243)
                             in
                             match
                               hostIndepLikelihood1
                                 st177
                                 (addi nextIndex11 1)
                                 nextState
                                 finalState
                                 nextAge
                                 finalAge11
                                 eventSeq4
                                 embeddedQMatrix
                             with
                               (st178, x244)
                             in
                             p_apply st178 x243 x244)
                        x198
    let hostIndepLikelihood1 =
      lam st179.
        lam nextIndex12.
          lam currState1.
            lam finalState1.
              lam currAge12.
                lam finalAge12.
                  lam eventSeq41.
                    lam embeddedQMatrix1.
                      match length13 st179 eventSeq41 with (st180, x245)
                      in
                      p_bind
                        st180
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st181.
                           lam x246.
                             match gti nextIndex12 x246 with true
                             then
                               match
                                 p_map
                                   st181
                                   (lam x247.
                                      lam x248.
                                        mulf (negf (subf x247 finalAge12)) x248)
                                   currAge12
                               with
                                 (st182, x249)
                               in
                               match
                                 p_traverseSeq
                                   st182
                                   (lam st183.
                                      lam x250.
                                        (st183, x250))
                                   (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x322
                                    then
                                      x322.totalRates
                                    else
                                      let #var"231" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x251.
                                           p_pure x251)
                                        (exit 1))
                               with
                                 (st184, x252)
                               in
                               match p_map st184 get x252 with (st185, x253)
                               in
                               match
                                 p_map
                                   st185
                                   (lam x254.
                                      subi (addi x254 1) 1)
                                   currState1
                               with
                                 (st186, x255)
                               in
                               match p_apply st186 x253 x255 with (st187, x256)
                               in
                               p_apply st187 x249 x256
                             else match
                               p_map
                                 st181
                                 (lam x257.
                                    get x257 (subi nextIndex12 1))
                                 eventSeq41
                             with
                               (st188, nextEvent12)
                             in
                             match
                               p_map
                                 st188
                                 (lam x258.
                                    match x258 with Event1 x362
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
                               (st189, nextState1)
                             in
                             match
                               p_map
                                 st189
                                 (lam x259.
                                    match x259 with Event1 x352
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
                               (st190, nextAge1)
                             in
                             match
                               p_traverseSeq
                                 st190
                                 (lam st191.
                                    lam x260.
                                      p_traverseSeq
                                        st191
                                        (lam st192.
                                           lam x261.
                                             (st192, x261))
                                        x260)
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x332
                                  then
                                    x332.transitionProbs
                                  else
                                    let #var"234" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x262.
                                         map
                                           (lam x263.
                                              p_pure x263)
                                           x262)
                                      (exit 1))
                             with
                               (st193, x264)
                             in
                             match
                               p_map
                                 st193
                                 (lam x265.
                                    lam x266.
                                      get (get x265 x266))
                                 x264
                             with
                               (st194, x267)
                             in
                             match
                               p_map
                                 st194
                                 (lam x268.
                                    subi (addi x268 1) 1)
                                 currState1
                             with
                               (st195, x269)
                             in
                             match p_apply st195 x267 x269 with (st196, x270)
                             in
                             match
                               p_map
                                 st196
                                 (lam x271.
                                    subi (addi x271 1) 1)
                                 nextState1
                             with
                               (st197, x272)
                             in
                             match p_apply st197 x270 x272 with (st198, x273)
                             in
                             match log11 st198 x273 with (st199, x274)
                             in
                             match
                               p_map
                                 st199
                                 (lam x275.
                                    lam x276.
                                      lam x277.
                                        addf (subf x275 x276) x277)
                                 x274
                             with
                               (st200, x278)
                             in
                             match
                               p_map
                                 st200
                                 (lam x279.
                                    lam x280.
                                      lam x281.
                                        mulf (subf x279 x280) x281)
                                 currAge12
                             with
                               (st201, x282)
                             in
                             match p_apply st201 x282 nextAge1 with (st202, x283)
                             in
                             match
                               p_traverseSeq
                                 st202
                                 (lam st203.
                                    lam x284.
                                      (st203, x284))
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x342
                                  then
                                    x342.totalRates
                                  else
                                    let #var"235" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x285.
                                         p_pure x285)
                                      (exit 1))
                             with
                               (st204, x286)
                             in
                             match p_map st204 get x286 with (st205, x287)
                             in
                             match
                               p_map
                                 st205
                                 (lam x288.
                                    subi (addi x288 1) 1)
                                 currState1
                             with
                               (st206, x289)
                             in
                             match p_apply st206 x287 x289 with (st207, x290)
                             in
                             match p_apply st207 x283 x290 with (st208, x291)
                             in
                             match p_apply st208 x278 x291 with (st209, x292)
                             in
                             match
                               hostIndepLikelihood1
                                 st209
                                 (addi nextIndex12 1)
                                 nextState1
                                 finalState1
                                 nextAge1
                                 finalAge12
                                 eventSeq41
                                 embeddedQMatrix1
                             with
                               (st210, x293)
                             in
                             p_apply st210 x292 x293)
                        x245
    let hostIndepLikelihood2 =
      lam st211.
        lam nextIndex13.
          lam currState2.
            lam finalState2.
              lam currAge13.
                lam finalAge13.
                  lam eventSeq42.
                    lam embeddedQMatrix2.
                      match length13 st211 eventSeq42 with (st212, x294)
                      in
                      p_bind
                        st212
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st213.
                           lam x295.
                             match gti nextIndex13 x295 with true
                             then
                               match
                                 p_traverseSeq
                                   st213
                                   (lam st214.
                                      lam x296.
                                        (st214, x296))
                                   (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x323
                                    then
                                      x323.totalRates
                                    else
                                      let #var"236" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x297.
                                           p_pure x297)
                                        (exit 1))
                               with
                                 (st215, x298)
                               in
                               match
                                 p_map
                                   st215
                                   (lam x299.
                                      lam x300.
                                        mulf (negf (subf currAge13 finalAge13)) (get x299 x300))
                                   x298
                               with
                                 (st216, x303)
                               in
                               match
                                 p_map
                                   st216
                                   (lam x304.
                                      subi (addi x304 1) 1)
                                   currState2
                               with
                                 (st217, x305)
                               in
                               p_apply st217 x303 x305
                             else match
                               p_map
                                 st213
                                 (lam x306.
                                    get x306 (subi nextIndex13 1))
                                 eventSeq42
                             with
                               (st218, nextEvent13)
                             in
                             match
                               p_map
                                 st218
                                 (lam x307.
                                    match x307 with Event1 x363
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
                               (st219, nextState2)
                             in
                             match
                               p_map
                                 st219
                                 (lam x308.
                                    match x308 with Event1 x353
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
                               (st220, nextAge2)
                             in
                             match
                               p_traverseSeq
                                 st220
                                 (lam st221.
                                    lam x309.
                                      p_traverseSeq
                                        st221
                                        (lam st222.
                                           lam x310.
                                             (st222, x310))
                                        x309)
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x333
                                  then
                                    x333.transitionProbs
                                  else
                                    let #var"239" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x313.
                                         map
                                           (lam x314.
                                              p_pure x314)
                                           x313)
                                      (exit 1))
                             with
                               (st223, x315)
                             in
                             match
                               p_map
                                 st223
                                 (lam x316.
                                    lam x317.
                                      get (get x316 x317))
                                 x315
                             with
                               (st224, x318)
                             in
                             match
                               p_map
                                 st224
                                 (lam x319.
                                    subi (addi x319 1) 1)
                                 currState2
                             with
                               (st225, x320)
                             in
                             match p_apply st225 x318 x320 with (st226, x324)
                             in
                             match
                               p_map
                                 st226
                                 (lam x325.
                                    subi (addi x325 1) 1)
                                 nextState2
                             with
                               (st227, x326)
                             in
                             match p_apply st227 x324 x326 with (st228, x327)
                             in
                             match log11 st228 x327 with (st229, x328)
                             in
                             match
                               p_map
                                 st229
                                 (lam x329.
                                    lam x330.
                                      lam x334.
                                        addf (subf x329 x330) x334)
                                 x328
                             with
                               (st230, x335)
                             in
                             match
                               p_map
                                 st230
                                 (lam x336.
                                    lam x337.
                                      mulf (subf currAge13 x336) x337)
                                 nextAge2
                             with
                               (st231, x338)
                             in
                             match
                               p_traverseSeq
                                 st231
                                 (lam st232.
                                    lam x339.
                                      (st232, x339))
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x343
                                  then
                                    x343.totalRates
                                  else
                                    let #var"240" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x340.
                                         p_pure x340)
                                      (exit 1))
                             with
                               (st233, x344)
                             in
                             match p_map st233 get x344 with (st234, x345)
                             in
                             match
                               p_map
                                 st234
                                 (lam x346.
                                    subi (addi x346 1) 1)
                                 currState2
                             with
                               (st235, x347)
                             in
                             match p_apply st235 x345 x347 with (st236, x348)
                             in
                             match p_apply st236 x338 x348 with (st237, x349)
                             in
                             match p_apply st237 x335 x349 with (st238, x350)
                             in
                             match
                               hostIndepLikelihood3
                                 st238
                                 (addi nextIndex13 1)
                                 nextState2
                                 finalState2
                                 nextAge2
                                 finalAge13
                                 eventSeq42
                                 embeddedQMatrix2
                             with
                               (st239, x354)
                             in
                             p_apply st239 x350 x354)
                        x294
    let hostIndepLikelihood3 =
      lam st240.
        lam nextIndex14.
          lam currState3.
            lam finalState3.
              lam currAge14.
                lam finalAge14.
                  lam eventSeq43.
                    lam embeddedQMatrix3.
                      match length13 st240 eventSeq43 with (st241, x355)
                      in
                      p_bind
                        st241
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st242.
                           lam x356.
                             match gti nextIndex14 x356 with true
                             then
                               match
                                 p_map
                                   st242
                                   (lam x357.
                                      lam x358.
                                        mulf (negf (subf x357 finalAge14)) x358)
                                   currAge14
                               with
                                 (st243, x359)
                               in
                               match
                                 p_traverseSeq
                                   st243
                                   (lam st244.
                                      lam x360.
                                        (st244, x360))
                                   (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3210
                                    then
                                      x3210.totalRates
                                    else
                                      let #var"241" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x364.
                                           p_pure x364)
                                        (exit 1))
                               with
                                 (st245, x365)
                               in
                               match p_map st245 get x365 with (st246, x366)
                               in
                               match
                                 p_map
                                   st246
                                   (lam x367.
                                      subi (addi x367 1) 1)
                                   currState3
                               with
                                 (st247, x368)
                               in
                               match p_apply st247 x366 x368 with (st248, x369)
                               in
                               p_apply st248 x359 x369
                             else match
                               p_map
                                 st242
                                 (lam x370.
                                    get x370 (subi nextIndex14 1))
                                 eventSeq43
                             with
                               (st249, nextEvent14)
                             in
                             match
                               p_map
                                 st249
                                 (lam x371.
                                    match x371 with Event1 x3610
                                    then
                                      x3610.toState
                                    else
                                      let #var"242" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent14
                             with
                               (st250, nextState3)
                             in
                             match
                               p_map
                                 st250
                                 (lam x372.
                                    match x372 with Event1 x3510
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
                               (st251, nextAge3)
                             in
                             match
                               p_traverseSeq
                                 st251
                                 (lam st252.
                                    lam x373.
                                      p_traverseSeq
                                        st252
                                        (lam st253.
                                           lam x374.
                                             (st253, x374))
                                        x373)
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3310
                                  then
                                    x3310.transitionProbs
                                  else
                                    let #var"244" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x375.
                                         map
                                           (lam x376.
                                              p_pure x376)
                                           x375)
                                      (exit 1))
                             with
                               (st254, x377)
                             in
                             match
                               p_map
                                 st254
                                 (lam x378.
                                    lam x379.
                                      get (get x378 x379))
                                 x377
                             with
                               (st255, x380)
                             in
                             match
                               p_map
                                 st255
                                 (lam x381.
                                    subi (addi x381 1) 1)
                                 currState3
                             with
                               (st256, x382)
                             in
                             match p_apply st256 x380 x382 with (st257, x383)
                             in
                             match
                               p_map
                                 st257
                                 (lam x384.
                                    subi (addi x384 1) 1)
                                 nextState3
                             with
                               (st258, x385)
                             in
                             match p_apply st258 x383 x385 with (st259, x386)
                             in
                             match log11 st259 x386 with (st260, x387)
                             in
                             match
                               p_map
                                 st260
                                 (lam x388.
                                    lam x389.
                                      lam x390.
                                        addf (subf x388 x389) x390)
                                 x387
                             with
                               (st261, x391)
                             in
                             match
                               p_map
                                 st261
                                 (lam x392.
                                    lam x393.
                                      lam x394.
                                        mulf (subf x392 x393) x394)
                                 currAge14
                             with
                               (st262, x395)
                             in
                             match p_apply st262 x395 nextAge3 with (st263, x396)
                             in
                             match
                               p_traverseSeq
                                 st263
                                 (lam st264.
                                    lam x397.
                                      (st264, x397))
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3410
                                  then
                                    x3410.totalRates
                                  else
                                    let #var"245" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x398.
                                         p_pure x398)
                                      (exit 1))
                             with
                               (st265, x399)
                             in
                             match p_map st265 get x399 with (st266, x400)
                             in
                             match
                               p_map
                                 st266
                                 (lam x401.
                                    subi (addi x401 1) 1)
                                 currState3
                             with
                               (st267, x402)
                             in
                             match p_apply st267 x400 x402 with (st268, x403)
                             in
                             match p_apply st268 x396 x403 with (st269, x404)
                             in
                             match p_apply st269 x391 x404 with (st270, x405)
                             in
                             match
                               hostIndepLikelihood3
                                 st270
                                 (addi nextIndex14 1)
                                 nextState3
                                 finalState3
                                 nextAge3
                                 finalAge14
                                 eventSeq43
                                 embeddedQMatrix3
                             with
                               (st271, x406)
                             in
                             p_apply st271 x405 x406)
                        x355
  in
  let anon22 = lam x947.
      addi x947 1 in
  recursive
    let rec36 =
      lam i16.
        lam acc19.
          match geqi i16 0 with true
          then
            rec36 (subi i16 1) (cons (anon22 i16) acc19)
          else
            acc19
  in
  let anon23 =
    lam st604.
      lam msg1.
        lam nodeLabel51.
          lam x941.
            match
              hostMsgToProb st604 msg1 (addi x941 (muli nodeLabel51 0))
            with
              (st605, x942)
            in
            match
              p_traverseSeq
                st605
                (lam st606.
                   lam x943.
                     (st606, x943))
                x942
            with
              (st607, x944)
            in
            match
              p_map st607 (lam x945.
                   mkCategorical x945) x944
            with
              (st608, x946)
            in
            p_assume st608 hrmStoreAssume x946
  in
  recursive
    let rec15 =
      lam st272.
        lam c33.
          lam c34.
            lam s14.
              match s14 with [ _,
                  _ ] ++ _
              then
                match anon23 st272 c33 c34 (get s14 0) with (st273, x407)
                in
                match splitAt s14 1 with {#label"1" = x408}
                in
                match rec15 st273 c33 c34 x408 with (st274, x409)
                in
                (st274, cons x407 x409)
              else match s14 with [ e14 ]
              then
                match splitAt s14 1 with {#label"1" = x410}
                in
                let slice13 = x410 in
                match anon23 st272 c33 c34 e14 with (st275, x411)
                in
                (st275, [ x411 ])
              else match s14 with ""
              in
              (st272, "")
  in
  let suggestNodeRep =
    lam st603.
      lam msg.
        lam nHosts5.
          lam nodeLabel5.
            let i111 = subi (addi (subi nHosts5 1) 1) 1 in
            rec15
              st603
              msg
              nodeLabel5
              (match geqi i111 0 with true
               then
                 rec36 (subi i111 1) (cons (anon22 i111) "")
               else
                 "")
  in
  recursive
    let any =
      lam st276.
        lam seq.
          match null seq with true
          then
            (st276, p_pure false)
          else match
            p_map st276 (lam x412.
                 eqi x412 2) (head seq)
          with
            (st277, x413)
          in
          p_bind
            st277
            hrmStoreSubmodel
            (hrmInit {})
            (lam st278.
               lam x414.
                 match x414 with true
                 then
                   (st278, p_pure true)
                 else
                   any st278 (tail seq))
            x413
  in
  let any1 = lam st602.
      lam l21.
        any st602 l21 in
  recursive
    let sampleHostHistoryRec =
      lam st279.
        lam currentState.
          lam finalState11.
            lam currentAge.
              lam finalAge2.
                lam host.
                  lam nodeLabel.
                    lam embeddedQMatrix11.
                      p_bind
                        st279
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st280.
                           lam x415.
                             match
                               match ltf x415 finalAge2 with true
                               then
                                 match
                                   p_map
                                     st280
                                     (lam x416.
                                        eqi x416 finalState11)
                                     currentState
                                 with
                                   (st281, x417)
                                 in
                                 match
                                   p_traverseSeq
                                     st281
                                     (lam st282.
                                        lam x418.
                                          (st282, x418))
                                     ""
                                 with
                                   (st283, x419)
                                 in
                                 (st283, Bridge1
                                   { success = x417, events = x419 })
                               else match
                                 p_traverseSeq
                                   st280
                                   (lam st284.
                                      lam x420.
                                        p_traverseSeq
                                          st284
                                          (lam st285.
                                             lam x421.
                                               (st285, x421))
                                          x420)
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x4010
                                    then
                                      x4010.transitionProbs
                                    else
                                      let #var"246" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 377:16-377:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x422.
                                           map
                                             (lam x423.
                                                p_pure x423)
                                             x422)
                                        (exit 1))
                               with
                                 (st286, x424)
                               in
                               match
                                 p_map
                                   st286
                                   (lam x425.
                                      lam x426.
                                        mkCategorical (get x425 x426))
                                   x424
                               with
                                 (st287, x427)
                               in
                               match
                                 p_map
                                   st287
                                   (lam x428.
                                      subi (addi x428 1) 1)
                                   currentState
                               with
                                 (st288, x429)
                               in
                               match p_apply st288 x427 x429 with (st289, x430)
                               in
                               match p_assume st289 hrmStoreAssume x430 with (st290, nextState11)
                               in
                               match
                                 p_traverseSeq
                                   st290
                                   (lam st291.
                                      lam x431.
                                        (st291, x431))
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x3910
                                    then
                                      x3910.totalRates
                                    else
                                      let #var"247" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 381:20-381:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x432.
                                           p_pure x432)
                                        (exit 1))
                               with
                                 (st292, x433)
                               in
                               match
                                 p_map
                                   st292
                                   (lam x434.
                                      lam x435.
                                        mkExponential
                                          (addf
                                             (addf (get x434 x435) (mulf (int2float host) 0.))
                                             (mulf (int2float nodeLabel) 0.)))
                                   x433
                               with
                                 (st293, x436)
                               in
                               match
                                 p_map
                                   st293
                                   (lam x437.
                                      subi (addi x437 1) 1)
                                   nextState11
                               with
                                 (st294, x438)
                               in
                               match p_apply st294 x436 x438 with (st295, x439)
                               in
                               match p_assume st295 hrmStoreAssume x439 with (st296, x440)
                               in
                               match
                                 p_map
                                   st296
                                   (lam x441.
                                      subf x415 x441)
                                   x440
                               with
                                 (st297, x442)
                               in
                               match
                                 sampleHostHistoryRec
                                   st297
                                   nextState11
                                   finalState11
                                   x442
                                   finalAge2
                                   host
                                   nodeLabel
                                   embeddedQMatrix11
                               with
                                 (st298, restOfHistory)
                               in
                               match
                                 p_map
                                   st298
                                   (lam x443.
                                      match x443 with Bridge1 x3710
                                      then
                                        x3710.success
                                      else
                                        let #var"248" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 399:18-399:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st299, x444)
                               in
                               match
                                 p_map
                                   st299
                                   (lam x445.
                                      lam x446.
                                        cons
                                          (Event1
                                             { host = host, toState = x445, eventTime = x415, fromState = x446 }))
                                   nextState11
                               with
                                 (st300, x447)
                               in
                               match p_apply st300 x447 currentState with (st301, x448)
                               in
                               match
                                 p_map
                                   st301
                                   (lam x449.
                                      match x449 with Bridge1 x3810
                                      then
                                        x3810.events
                                      else
                                        let #var"249" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 397:10-397:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st302, x450)
                               in
                               match p_apply st302 x448 x450 with (st303, x451)
                               in
                               (st303, Bridge1
                                 { success = x444, events = x451 })
                             with
                               (st304, x452)
                             in
                             match x452 with Bridge1 x453
                             in
                             match x453 with {success = x454}
                             in
                             match
                               p_map
                                 st304
                                 (lam x455.
                                    lam x456.
                                      Bridge1
                                        { success = x455, events = x456 })
                                 x454
                             with
                               (st305, x457)
                             in
                             match x453 with {events = x458}
                             in
                             p_apply st305 x457 x458)
                        currentAge
    let sampleHostHistoryRec1 =
      lam st306.
        lam currentState1.
          lam finalState12.
            lam currentAge1.
              lam finalAge21.
                lam host1.
                  lam nodeLabel1.
                    lam embeddedQMatrix12.
                      p_bind
                        st306
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st307.
                           lam x459.
                             match
                               match ltf x459 finalAge21 with true
                               then
                                 match
                                   p_map
                                     st307
                                     (lam x460.
                                        lam x461.
                                          eqi x460 x461)
                                     currentState1
                                 with
                                   (st308, x462)
                                 in
                                 match p_apply st308 x462 finalState12 with (st309, x463)
                                 in
                                 match
                                   p_traverseSeq
                                     st309
                                     (lam st310.
                                        lam x464.
                                          (st310, x464))
                                     ""
                                 with
                                   (st311, x465)
                                 in
                                 (st311, Bridge1
                                   { success = x463, events = x465 })
                               else match
                                 p_traverseSeq
                                   st307
                                   (lam st312.
                                      lam x466.
                                        p_traverseSeq
                                          st312
                                          (lam st313.
                                             lam x467.
                                               (st313, x467))
                                          x466)
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x4011
                                    then
                                      x4011.transitionProbs
                                    else
                                      let #var"250" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 377:16-377:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x468.
                                           map
                                             (lam x469.
                                                p_pure x469)
                                             x468)
                                        (exit 1))
                               with
                                 (st314, x470)
                               in
                               match
                                 p_map
                                   st314
                                   (lam x471.
                                      lam x472.
                                        mkCategorical (get x471 x472))
                                   x470
                               with
                                 (st315, x473)
                               in
                               match
                                 p_map
                                   st315
                                   (lam x474.
                                      subi (addi x474 1) 1)
                                   currentState1
                               with
                                 (st316, x475)
                               in
                               match p_apply st316 x473 x475 with (st317, x476)
                               in
                               match p_assume st317 hrmStoreAssume x476 with (st318, nextState12)
                               in
                               match
                                 p_traverseSeq
                                   st318
                                   (lam st319.
                                      lam x477.
                                        (st319, x477))
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x3911
                                    then
                                      x3911.totalRates
                                    else
                                      let #var"251" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 381:20-381:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x478.
                                           p_pure x478)
                                        (exit 1))
                               with
                                 (st320, x479)
                               in
                               match
                                 p_map
                                   st320
                                   (lam x480.
                                      lam x481.
                                        mkExponential
                                          (addf
                                             (addf (get x480 x481) (mulf (int2float host1) 0.))
                                             (mulf (int2float nodeLabel1) 0.)))
                                   x479
                               with
                                 (st321, x482)
                               in
                               match
                                 p_map
                                   st321
                                   (lam x483.
                                      subi (addi x483 1) 1)
                                   nextState12
                               with
                                 (st322, x484)
                               in
                               match p_apply st322 x482 x484 with (st323, x485)
                               in
                               match p_assume st323 hrmStoreAssume x485 with (st324, x486)
                               in
                               match
                                 p_map
                                   st324
                                   (lam x487.
                                      subf x459 x487)
                                   x486
                               with
                                 (st325, x488)
                               in
                               match
                                 sampleHostHistoryRec1
                                   st325
                                   nextState12
                                   finalState12
                                   x488
                                   finalAge21
                                   host1
                                   nodeLabel1
                                   embeddedQMatrix12
                               with
                                 (st326, restOfHistory1)
                               in
                               match
                                 p_map
                                   st326
                                   (lam x489.
                                      match x489 with Bridge1 x3711
                                      then
                                        x3711.success
                                      else
                                        let #var"252" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 399:18-399:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st327, x490)
                               in
                               match
                                 p_map
                                   st327
                                   (lam x491.
                                      lam x492.
                                        cons
                                          (Event1
                                             { host = host1, toState = x491, eventTime = x459, fromState = x492 }))
                                   nextState12
                               with
                                 (st328, x493)
                               in
                               match p_apply st328 x493 currentState1 with (st329, x494)
                               in
                               match
                                 p_map
                                   st329
                                   (lam x495.
                                      match x495 with Bridge1 x3811
                                      then
                                        x3811.events
                                      else
                                        let #var"253" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 397:10-397:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st330, x496)
                               in
                               match p_apply st330 x494 x496 with (st331, x497)
                               in
                               (st331, Bridge1
                                 { success = x490, events = x497 })
                             with
                               (st332, x498)
                             in
                             match x498 with Bridge1 x499
                             in
                             match x499 with {success = x500}
                             in
                             match
                               p_map
                                 st332
                                 (lam x501.
                                    lam x502.
                                      Bridge1
                                        { success = x501, events = x502 })
                                 x500
                             with
                               (st333, x503)
                             in
                             match x499 with {events = x504}
                             in
                             p_apply st333 x503 x504)
                        currentAge1
  in
  let anon24 = lam x940.
      addi x940 1 in
  recursive
    let rec37 =
      lam i17.
        lam acc110.
          match geqi i17 0 with true
          then
            rec37 (subi i17 1) (cons (anon24 i17) acc110)
          else
            acc110
  in
  let create13 =
    lam l61.
      let i110 = subi l61 1 in
      match geqi i110 0 with true
      then
        rec37 (subi i110 1) (cons (anon24 i110) "")
      else
        ""
  in
  let anon25 =
    lam st590.
      lam startRep2.
        lam finalRep13.
          lam startAge2.
            lam finalAge33.
              lam nodeLabel13.
                lam modelParams32.
                  lam x922.
                    let startState1 = get startRep2 (subi x922 1) in
                    let embeddedQMatrix51 =
                      match modelParams32 with ModelParams1 x1142
                      then
                        x1142.embeddedQMatrix
                      else
                        let #var"2127" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 255:4-255:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st590
                        (lam st591.
                           lam x923.
                             (st591, x923))
                        (match embeddedQMatrix51 with EmbeddedMarkovChainMatrix1 x1182
                         then
                           x1182.totalRates
                         else
                           let #var"2124" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 346:18-346:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x924.
                                p_pure x924)
                             (exit 1))
                    with
                      (st592, x925)
                    in
                    match
                      p_map
                        st592
                        (lam x926.
                           lam x927.
                             mkExponential
                               (addf
                                  (addf (get x926 x927) (mulf (int2float x922) 0.))
                                  (mulf (int2float nodeLabel13) 0.)))
                        x925
                    with
                      (st593, x928)
                    in
                    match
                      p_map
                        st593
                        (lam x929.
                           subi (addi x929 1) 1)
                        startState1
                    with
                      (st594, x930)
                    in
                    match p_apply st594 x928 x930 with (st595, x931)
                    in
                    match p_assume st595 hrmStoreAssume x931 with (st596, x932)
                    in
                    match
                      p_map
                        st596
                        (lam x933.
                           subf startAge2 x933)
                        x932
                    with
                      (st597, x934)
                    in
                    match
                      sampleHostHistoryRec
                        st597
                        startState1
                        (get finalRep13 (subi x922 1))
                        x934
                        finalAge33
                        x922
                        nodeLabel13
                        embeddedQMatrix51
                    with
                      (st598, bridge1)
                    in
                    match
                      p_map
                        st598
                        (lam x935.
                           match x935 with Bridge1 x1172
                           then
                             x1172.success
                           else
                             let #var"2125" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 358:19-358:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge1
                    with
                      (st599, x936)
                    in
                    match bool2real st599 x936 with (st600, x937)
                    in
                    let st601 =
                      p_weight
                        st600
                        hrmStoreWeight
                        (lam x939.
                           externalLog
                             (addf
                                (addf x939 (mulf (int2float x922) 0.))
                                (mulf (int2float nodeLabel13) 0.)))
                        x937
                    in
                    let foo51 = {} in
                    p_map
                      st601
                      (lam x938.
                         match x938 with Bridge1 x1162
                         then
                           x1162.events
                         else
                           let #var"2126" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 359:9-359:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge1
  in
  let anon26 =
    lam st578.
      lam startRep1.
        lam finalRep12.
          lam startAge1.
            lam finalAge32.
              lam nodeLabel12.
                lam modelParams31.
                  lam x902.
                    let startState = get startRep1 (subi x902 1) in
                    let embeddedQMatrix5 =
                      match modelParams31 with ModelParams1 x1141
                      then
                        x1141.embeddedQMatrix
                      else
                        let #var"2123" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 255:4-255:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st578
                        (lam st579.
                           lam x903.
                             (st579, x903))
                        (match embeddedQMatrix5 with EmbeddedMarkovChainMatrix1 x1181
                         then
                           x1181.totalRates
                         else
                           let #var"2120" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 346:18-346:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x904.
                                p_pure x904)
                             (exit 1))
                    with
                      (st580, x905)
                    in
                    match
                      p_map
                        st580
                        (lam x906.
                           lam x907.
                             mkExponential
                               (addf
                                  (addf (get x906 x907) (mulf (int2float x902) 0.))
                                  (mulf (int2float nodeLabel12) 0.)))
                        x905
                    with
                      (st581, x908)
                    in
                    match
                      p_map
                        st581
                        (lam x909.
                           subi (addi x909 1) 1)
                        startState
                    with
                      (st582, x910)
                    in
                    match p_apply st582 x908 x910 with (st583, x912)
                    in
                    match p_assume st583 hrmStoreAssume x912 with (st584, x913)
                    in
                    match
                      p_map
                        st584
                        (lam x914.
                           subf startAge1 x914)
                        x913
                    with
                      (st585, x915)
                    in
                    match
                      sampleHostHistoryRec1
                        st585
                        startState
                        (get finalRep12 (subi x902 1))
                        x915
                        finalAge32
                        x902
                        nodeLabel12
                        embeddedQMatrix5
                    with
                      (st586, bridge)
                    in
                    match
                      p_map
                        st586
                        (lam x916.
                           match x916 with Bridge1 x1171
                           then
                             x1171.success
                           else
                             let #var"2121" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 358:19-358:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge
                    with
                      (st587, x917)
                    in
                    match bool2real st587 x917 with (st588, x918)
                    in
                    let st589 =
                      p_weight
                        st588
                        hrmStoreWeight
                        (lam x920.
                           externalLog
                             (addf
                                (addf x920 (mulf (int2float x902) 0.))
                                (mulf (int2float nodeLabel12) 0.)))
                        x918
                    in
                    let foo5 = {} in
                    p_map
                      st589
                      (lam x919.
                         match x919 with Bridge1 x1161
                         then
                           x1161.events
                         else
                           let #var"2122" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 359:9-359:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge
  in
  recursive
    let rec16 =
      lam st334.
        lam c35.
          lam c36.
            lam c37.
              lam c38.
                lam c39.
                  lam c40.
                    lam s15.
                      match s15 with [ _,
                          _ ] ++ _
                      then
                        match
                          anon25 st334 c35 c36 c37 c38 c39 c40 (get s15 0)
                        with
                          (st335, x505)
                        in
                        match splitAt s15 1 with {#label"1" = x506}
                        in
                        match rec16 st335 c35 c36 c37 c38 c39 c40 x506 with (st336, x507)
                        in
                        (st336, cons x505 x507)
                      else match s15 with [ e15 ]
                      then
                        match splitAt s15 1 with {#label"1" = x508}
                        in
                        let slice14 = x508 in
                        match anon25 st334 c35 c36 c37 c38 c39 c40 e15 with (st337, x509)
                        in
                        (st337, [ x509 ])
                      else match s15 with ""
                      in
                      (st334, "")
    let rec17 =
      lam st338.
        lam c41.
          lam c42.
            lam c43.
              lam c44.
                lam c45.
                  lam c46.
                    lam s16.
                      match s16 with [ _,
                          _ ] ++ _
                      then
                        match
                          anon26 st338 c41 c42 c43 c44 c45 c46 (get s16 0)
                        with
                          (st339, x510)
                        in
                        match splitAt s16 1 with {#label"1" = x511}
                        in
                        match rec17 st339 c41 c42 c43 c44 c45 c46 x511 with (st340, x512)
                        in
                        (st340, cons x510 x512)
                      else match s16 with [ e16 ]
                      then
                        match splitAt s16 1 with {#label"1" = x513}
                        in
                        let slice15 = x513 in
                        match anon26 st338 c41 c42 c43 c44 c45 c46 e16 with (st341, x514)
                        in
                        (st341, [ x514 ])
                      else match s16 with ""
                      in
                      (st338, "")
  in
  let anon27 =
    lam h2.
      lam x900.
        lti
          (match
             isNaN1
               (match h2 with Event1 x1191
                then
                  x1191.eventTime
                else
                  let #var"2116" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 295:12-295:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             negi 1
           else match
             isNaN1
               (match x900 with Event1 x1241
                then
                  x1241.eventTime
                else
                  let #var"2117" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 298:12-298:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             1
           else match
             geqf
               (match h2 with Event1 x1251
                then
                  x1251.eventTime
                else
                  let #var"2118" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 301:6-301:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
                  in
                  exit 1)
               (match x900 with Event1 x1261
                then
                  x1261.eventTime
                else
                  let #var"2119" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 301:25-301:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
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
      lam c47.
        lam l.
          lam r.
            lam seq1.
              match seq1 with [ _ ] ++ _
              then
                let s41 = get seq1 0 in
                match splitAt seq1 1 with {#label"1" = x515}
                in
                let seq2 = x515 in
                match anon27 c47 s41 with true
                then
                  work11 c47 (cons s41 l) r seq2
                else
                  work11 c47 l (cons s41 r) seq2
              else match seq1 with ""
              in
              (l, r)
    let work12 =
      lam c48.
        lam l1.
          lam r1.
            lam seq11.
              match seq11 with [ _ ] ++ _
              then
                let s42 = get seq11 0 in
                match splitAt seq11 1 with {#label"1" = x516}
                in
                let seq21 = x516 in
                match anon27 c48 s42 with true
                then
                  work12 c48 (cons s42 l1) r1 seq21
                else
                  work11 c48 l1 (cons s42 r1) seq21
              else match seq11 with ""
              in
              (l1, r1)
    let work13 =
      lam c49.
        lam l2.
          lam r2.
            lam seq12.
              match seq12 with [ _ ] ++ _
              then
                let s43 = get seq12 0 in
                match splitAt seq12 1 with {#label"1" = x517}
                in
                let seq22 = x517 in
                match anon27 c49 s43 with true
                then
                  work11 c49 (cons s43 l2) r2 seq22
                else
                  work13 c49 l2 (cons s43 r2) seq22
              else match seq12 with ""
              in
              (l2, r2)
    let work14 =
      lam c50.
        lam l3.
          lam r3.
            lam seq13.
              match seq13 with [ _ ] ++ _
              then
                let s44 = get seq13 0 in
                match splitAt seq13 1 with {#label"1" = x518}
                in
                let seq23 = x518 in
                match anon27 c50 s44 with true
                then
                  work12 c50 (cons s44 l3) r3 seq23
                else
                  work13 c50 l3 (cons s44 r3) seq23
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
      lam st342.
        lam seq31.
          p_map
            st342
            (lam x519.
               match null x519 with true
               then
                 x519
               else
                 let h1 = head x519 in
                 let lr1 = work14 h1 "" "" (reverse (tail x519)) in
                 match lr1 with (#var"X6",)
                 in
                 match lr1 with {#label"1" = #var"X7"}
                 in
                 concat (quickSort #var"X6") (cons h1 (quickSort #var"X7")))
            seq31
  in
  recursive
    let rec213 =
      lam st343.
        lam c51.
          lam c52.
            lam c53.
              lam c54.
                lam c55.
                  lam c56.
                    lam acc20.
                      lam s214.
                        match s214 with [ _ ] ++ _
                        then
                          let x520 = get s214 0 in
                          match
                            p_map
                              st343
                              (lam x521.
                                 lam x522.
                                   addf x521 x522)
                              acc20
                          with
                            (st344, x523)
                          in
                          match
                            hostIndepLikelihood
                              st344
                              1
                              (get c51 (subi x520 1))
                              (get c52 (subi x520 1))
                              c53
                              c54
                              (get c56 (subi x520 1))
                              (match c55 with ModelParams1 x1401
                               then
                                 x1401.embeddedQMatrix
                               else
                                 let #var"254" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st345, x524)
                          in
                          match p_apply st345 x523 x524 with (st346, x525)
                          in
                          match splitAt s214 1 with {#label"1" = x526}
                          in
                          rec213 st346 c51 c52 c53 c54 c55 c56 x525 x526
                        else match s214 with ""
                        in
                        (st343, acc20)
    let rec214 =
      lam st347.
        lam c57.
          lam c58.
            lam c59.
              lam c60.
                lam c61.
                  lam c62.
                    lam acc23.
                      lam s215.
                        match s215 with [ _ ] ++ _
                        then
                          let x527 = get s215 0 in
                          match
                            p_map
                              st347
                              (lam x528.
                                 lam x529.
                                   addf x528 x529)
                              acc23
                          with
                            (st348, x530)
                          in
                          match
                            hostIndepLikelihood2
                              st348
                              1
                              (get c57 (subi x527 1))
                              (get c58 (subi x527 1))
                              c59
                              c60
                              (get c62 (subi x527 1))
                              (match c61 with ModelParams1 x1402
                               then
                                 x1402.embeddedQMatrix
                               else
                                 let #var"255" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st349, x531)
                          in
                          match p_apply st349 x530 x531 with (st350, x532)
                          in
                          match splitAt s215 1 with {#label"1" = x533}
                          in
                          rec214 st350 c57 c58 c59 c60 c61 c62 x532 x533
                        else match s215 with ""
                        in
                        (st347, acc23)
  in
  let anon28 = lam x899.
      addi x899 1 in
  recursive
    let rec38 =
      lam i18.
        lam acc111.
          match geqi i18 0 with true
          then
            rec38 (subi i18 1) (cons (anon28 i18) acc111)
          else
            acc111
  in
  let create14 =
    lam l6.
      let i19 = subi l6 1 in
      match geqi i19 0 with true
      then
        rec38 (subi i19 1) (cons (anon28 i19) "")
      else
        ""
  in
  recursive
    let rec215 =
      lam st351.
        lam acc24.
          lam s216.
            match s216 with [ _ ] ++ _
            then
              match
                p_map
                  st351
                  (lam x534.
                     lam x535.
                       addf x534 x535)
                  acc24
              with
                (st352, x536)
              in
              match p_apply st352 x536 (get s216 0) with (st353, x537)
              in
              match splitAt s216 1 with {#label"1" = x538}
              in
              rec215 st353 x537 x538
            else match s216 with ""
            in
            (st351, acc24)
  in
  let fold =
    lam st576.
      lam init1.
        lam seq5.
          match seq5 with [ _ ] ++ _
          then
            match
              p_map
                st576
                (lam x896.
                   addf init1 x896)
                (get seq5 0)
            with
              (st577, x897)
            in
            match splitAt seq5 1 with {#label"1" = x898}
            in
            rec215 st577 x897 x898
          else match seq5 with ""
          in
          (st576, p_pure init1)
  in
  recursive
    let rec216 =
      lam st354.
        lam c63.
          lam acc25.
            lam s217.
              match s217 with [ _ ] ++ _
              then
                match acc25 with (field, field1)
                in
                match
                  match field1 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st354
                        (lam x539.
                           addi x539 1)
                        (get field1 0)
                    with
                      (st355, x540)
                    in
                    match mtxGet1 st355 x540 (addi (get s217 0) 1) c63 with (st356, x541)
                    in
                    match log11 st356 x541 with (st357, x542)
                    in
                    match splitAt field1 1 with {#label"1" = x543}
                    in
                    (st357, (snoc field x542, x543))
                  else
                    let x544 = error "foldl2: Cannot happen!" in
                    match x544 with (x545,)
                    in
                    match x544 with {#label"1" = x546}
                    in
                    (st354, (map (lam x547.
                         p_pure x547) x545, map (lam x548.
                         p_pure x548) x546))
                with
                  (st358, x549)
                in
                match splitAt s217 1 with {#label"1" = x550}
                in
                rec216 st358 c63 x549 x550
              else match s217 with ""
              in
              (st354, acc25)
    let rec217 =
      lam st359.
        lam c64.
          lam acc26.
            lam s218.
              match s218 with [ _ ] ++ _
              then
                match acc26 with (field2, field3)
                in
                match
                  match field3 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st359
                        (lam x551.
                           addi x551 1)
                        (get field3 0)
                    with
                      (st360, x552)
                    in
                    match
                      p_map
                        st360
                        (lam x553.
                           addi x553 1)
                        (get s218 0)
                    with
                      (st361, x554)
                    in
                    match mtxGet2 st361 x552 x554 c64 with (st362, x555)
                    in
                    match log11 st362 x555 with (st363, x556)
                    in
                    match splitAt field3 1 with {#label"1" = x557}
                    in
                    (st363, (snoc field2 x556, x557))
                  else
                    let x558 = error "foldl2: Cannot happen!" in
                    match x558 with (x559,)
                    in
                    match x558 with {#label"1" = x560}
                    in
                    (st359, (map (lam x561.
                         p_pure x561) x559, map (lam x562.
                         p_pure x562) x560))
                with
                  (st364, x563)
                in
                match splitAt s218 1 with {#label"1" = x564}
                in
                rec217 st364 c64 x563 x564
              else match s218 with ""
              in
              (st359, acc26)
  in
  recursive
    let rec218 =
      lam st365.
        lam c65.
          lam acc27.
            lam s219.
              match s219 with [ _ ] ++ _
              then
                match acc27 with (field4, field5)
                in
                match
                  match field5 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st365
                        (lam x565.
                           addi x565 1)
                        (get s219 0)
                    with
                      (st366, x566)
                    in
                    match mtxGet1 st366 x566 (addi (get field5 0) 1) c65 with (st367, x567)
                    in
                    match log11 st367 x567 with (st368, x568)
                    in
                    match splitAt field5 1 with {#label"1" = x569}
                    in
                    (st368, (snoc field4 x568, x569))
                  else
                    let x570 = error "foldl2: Cannot happen!" in
                    match x570 with (x571,)
                    in
                    match x570 with {#label"1" = x572}
                    in
                    (st365, (map (lam x573.
                         p_pure x573) x571, x572))
                with
                  (st369, x574)
                in
                match splitAt s219 1 with {#label"1" = x575}
                in
                rec218 st369 c65 x574 x575
              else match s219 with ""
              in
              (st365, acc27)
    let rec219 =
      lam st370.
        lam c66.
          lam acc28.
            lam s220.
              match s220 with [ _ ] ++ _
              then
                match acc28 with (field6, field7)
                in
                match
                  match field7 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st370
                        (lam x576.
                           addi x576 1)
                        (get s220 0)
                    with
                      (st371, x577)
                    in
                    match
                      p_map
                        st371
                        (lam x578.
                           addi x578 1)
                        (get field7 0)
                    with
                      (st372, x579)
                    in
                    match mtxGet2 st372 x577 x579 c66 with (st373, x580)
                    in
                    match log11 st373 x580 with (st374, x581)
                    in
                    match splitAt field7 1 with {#label"1" = x582}
                    in
                    (st374, (snoc field6 x581, x582))
                  else
                    let x583 = error "foldl2: Cannot happen!" in
                    match x583 with (x584,)
                    in
                    match x583 with {#label"1" = x585}
                    in
                    (st370, (map (lam x586.
                         p_pure x586) x584, map (lam x587.
                         p_pure x587) x585))
                with
                  (st375, x588)
                in
                match splitAt s220 1 with {#label"1" = x589}
                in
                rec219 st375 c66 x588 x589
              else match s220 with ""
              in
              (st370, acc28)
  in
  let sampleBranch =
    lam st526.
      lam startRep.
        lam finalRep11.
          lam startAge.
            lam finalAge31.
              lam nHosts2.
                lam nodeLabel11.
                  lam modelParams3.
                    lam branchKernel1.
                      match
                        rec17
                          st526
                          startRep
                          finalRep11
                          startAge
                          finalAge31
                          nodeLabel11
                          modelParams3
                          (create13 (addi (subi nHosts2 1) 1))
                      with
                        (st527, unorderedBranch1)
                      in
                      match paste01 st527 unorderedBranch1 with (st528, x808)
                      in
                      match quickSort1 st528 x808 with (st529, orderedEvents1)
                      in
                      match length13 st529 orderedEvents1 with (st530, nEvents41)
                      in
                      match
                        allTimesValidBranch st530 startRep orderedEvents1 1 nEvents41 nHosts2
                      with
                        (st531, x809)
                      in
                      p_bind
                        st531
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st532.
                           lam x810.
                             match
                               match x810 with true
                               then
                                 let s222 = create14 (addi (subi (length12 unorderedBranch1) 1) 1)
                                 in
                                 match
                                   match s222 with [ _ ] ++ _
                                   then
                                     let x811 = get s222 0 in
                                     match
                                       hostIndepLikelihood2
                                         st532
                                         1
                                         (get startRep (subi x811 1))
                                         (get finalRep11 (subi x811 1))
                                         startAge
                                         finalAge31
                                         (get unorderedBranch1 (subi x811 1))
                                         (match modelParams3 with ModelParams1 x1404
                                          then
                                            x1404.embeddedQMatrix
                                          else
                                            let #var"2111" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                            in
                                            exit 1)
                                     with
                                       (st533, x812)
                                     in
                                     match
                                       p_map
                                         st533
                                         (lam x813.
                                            addf 0. x813)
                                         x812
                                     with
                                       (st534, x814)
                                     in
                                     match splitAt s222 1 with {#label"1" = x815}
                                     in
                                     rec214
                                       st534
                                       startRep
                                       finalRep11
                                       startAge
                                       finalAge31
                                       modelParams3
                                       unorderedBranch1
                                       x814
                                       x815
                                   else match s222 with ""
                                   in
                                   (st532, p_pure 0.)
                                 with
                                   (st535, x816)
                                 in
                                 match
                                   p_map
                                     st535
                                     (lam x817.
                                        lam x818.
                                          subf x817 x818)
                                     x816
                                 with
                                   (st536, x819)
                                 in
                                 match
                                   match geqi (length startRep) (length finalRep11) with true
                                   then
                                     let acc33 = ("", startRep) in
                                     match
                                       match finalRep11 with [ _ ] ++ _
                                       then
                                         match acc33 with (field16, field17)
                                         in
                                         match
                                           match field17 with [ _ ] ++ _
                                           then
                                             match
                                               p_map
                                                 st536
                                                 (lam x820.
                                                    addi x820 1)
                                                 (get field17 0)
                                             with
                                               (st537, x821)
                                             in
                                             match
                                               p_map
                                                 st537
                                                 (lam x822.
                                                    addi x822 1)
                                                 (get finalRep11 0)
                                             with
                                               (st538, x823)
                                             in
                                             match mtxGet2 st538 x821 x823 branchKernel1 with (st539, x824)
                                             in
                                             match log11 st539 x824 with (st540, x825)
                                             in
                                             match splitAt field17 1 with {#label"1" = x826}
                                             in
                                             (st540, (snoc field16 x825, x826))
                                           else
                                             let x827 = error "foldl2: Cannot happen!" in
                                             match x827 with (x828,)
                                             in
                                             match x827 with {#label"1" = x829}
                                             in
                                             (st536, (map
                                               (lam x830.
                                                  p_pure x830)
                                               x828, map
                                               (lam x831.
                                                  p_pure x831)
                                               x829))
                                         with
                                           (st541, x832)
                                         in
                                         match splitAt finalRep11 1 with {#label"1" = x833}
                                         in
                                         rec217 st541 branchKernel1 x832 x833
                                       else match finalRep11 with ""
                                       in
                                       (st536, acc33)
                                     with
                                       (st542, x834)
                                     in
                                     match x834 with (field18, field19)
                                     in
                                     (st542, field18)
                                   else
                                     let acc34 = ("", finalRep11) in
                                     match
                                       match startRep with [ _ ] ++ _
                                       then
                                         match acc34 with (field20, field21)
                                         in
                                         match
                                           match field21 with [ _ ] ++ _
                                           then
                                             match
                                               p_map
                                                 st536
                                                 (lam x835.
                                                    addi x835 1)
                                                 (get startRep 0)
                                             with
                                               (st543, x836)
                                             in
                                             match
                                               p_map
                                                 st543
                                                 (lam x837.
                                                    addi x837 1)
                                                 (get field21 0)
                                             with
                                               (st544, x838)
                                             in
                                             match mtxGet2 st544 x836 x838 branchKernel1 with (st545, x839)
                                             in
                                             match log11 st545 x839 with (st546, x840)
                                             in
                                             match splitAt field21 1 with {#label"1" = x841}
                                             in
                                             (st546, (snoc field20 x840, x841))
                                           else
                                             let x842 = error "foldl2: Cannot happen!" in
                                             match x842 with (x843,)
                                             in
                                             match x842 with {#label"1" = x844}
                                             in
                                             (st536, (map
                                               (lam x845.
                                                  p_pure x845)
                                               x843, map
                                               (lam x846.
                                                  p_pure x846)
                                               x844))
                                         with
                                           (st547, x847)
                                         in
                                         match splitAt startRep 1 with {#label"1" = x848}
                                         in
                                         rec219 st547 branchKernel1 x847 x848
                                       else match startRep with ""
                                       in
                                       (st536, acc34)
                                     with
                                       (st548, x849)
                                     in
                                     match x849 with (field22, field23)
                                     in
                                     (st548, field22)
                                 with
                                   (st549, x850)
                                 in
                                 match fold st549 0. x850 with (st550, x851)
                                 in
                                 match p_apply st550 x819 x851 with (st551, x852)
                                 in
                                 match
                                   p_bind
                                     st551
                                     hrmStoreSubmodel
                                     (hrmInit {})
                                     (lam st552.
                                        lam x853.
                                          match gti 1 x853 with true
                                          then
                                            match
                                              getTotalRate st552 startRep modelParams3 nHosts2
                                            with
                                              (st553, x854)
                                            in
                                            p_map
                                              st553
                                              (lam x855.
                                                 mulf (negf (subf startAge finalAge31)) x855)
                                              x854
                                          else match
                                            p_map
                                              st552
                                              (lam x856.
                                                 get x856 (subi 1 1))
                                              orderedEvents1
                                          with
                                            (st554, nextEvent3)
                                          in
                                          match
                                            p_map
                                              st554
                                              (lam x857.
                                                 match x857 with Event1 x3111
                                                 then
                                                   x3111.eventTime
                                                 else
                                                   let #var"2112" =
                                                     print
                                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 25:17-25:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                   in
                                                   exit 1)
                                              nextEvent3
                                          with
                                            (st555, newAge3)
                                          in
                                          match
                                            getTotalRate st555 startRep modelParams3 nHosts2
                                          with
                                            (st556, totalLeavingRate13)
                                          in
                                          match
                                            p_map
                                              st556
                                              (lam x858.
                                                 match x858 with Event1 x1433
                                                 then
                                                   x1433.host
                                                 else
                                                   let #var"2113" =
                                                     print
                                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                   in
                                                   exit 1)
                                              nextEvent3
                                          with
                                            (st557, hostIndex13)
                                          in
                                          match
                                            p_map
                                              st557
                                              (lam x859.
                                                 lam x860.
                                                   lam st558.
                                                     match
                                                       gti
                                                         (match x859 with Event1 x1413
                                                          then
                                                            x1413.fromState
                                                          else
                                                            let #var"2114" =
                                                              print
                                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                            in
                                                            exit 1)
                                                         x860
                                                     with
                                                       true
                                                     then
                                                       getLossRate2 st558 startRep hostIndex13 modelParams3
                                                     else
                                                       getGainRate2 st558 startRep hostIndex13 modelParams3)
                                              nextEvent3
                                          with
                                            (st559, x861)
                                          in
                                          match
                                            p_map
                                              st559
                                              (lam x862.
                                                 match x862 with Event1 x1423
                                                 then
                                                   x1423.toState
                                                 else
                                                   let #var"2115" =
                                                     print
                                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                   in
                                                   exit 1)
                                              nextEvent3
                                          with
                                            (st560, x863)
                                          in
                                          match
                                            p_subApply st560 hrmStoreSubmodel (hrmInit {}) x861 x863
                                          with
                                            (st561, x864)
                                          in
                                          match p_join st561 x864 with (st562, x865)
                                          in
                                          match
                                            p_map
                                              st562
                                              (lam x866.
                                                 lam x867.
                                                   divf x866 x867)
                                              x865
                                          with
                                            (st563, x868)
                                          in
                                          match p_apply st563 x868 totalLeavingRate13 with (st564, x869)
                                          in
                                          match log11 st564 x869 with (st565, x870)
                                          in
                                          match
                                            p_map
                                              st565
                                              (lam x871.
                                                 lam x872.
                                                   lam x873.
                                                     addf (subf x871 x872) x873)
                                              x870
                                          with
                                            (st566, x874)
                                          in
                                          match
                                            p_map
                                              st566
                                              (lam x875.
                                                 lam x876.
                                                   mulf (subf startAge x875) x876)
                                              newAge3
                                          with
                                            (st567, x877)
                                          in
                                          match p_apply st567 x877 totalLeavingRate13 with (st568, x878)
                                          in
                                          match p_apply st568 x874 x878 with (st569, x879)
                                          in
                                          match
                                            updateRepertoire st569 startRep nextEvent3 nHosts2
                                          with
                                            (st570, x880)
                                          in
                                          match
                                            fullModelWeight1
                                              st570
                                              (addi 1 1)
                                              x880
                                              finalRep11
                                              newAge3
                                              finalAge31
                                              orderedEvents1
                                              x853
                                              nHosts2
                                              modelParams3
                                          with
                                            (st571, x882)
                                          in
                                          p_apply st571 x879 x882)
                                     nEvents41
                                 with
                                   (st572, x883)
                                 in
                                 (st572, CorrectedBranchSample1
                                   { history = orderedEvents1,
                                     logSamplingDensity = x852,
                                     logModelDensity = x883,
                                     success = true })
                               else
                                 (st532, CorrectedBranchSample1
                                   { history = orderedEvents1,
                                     logSamplingDensity = p_pure (log1 0.),
                                     logModelDensity = p_pure (log1 0.),
                                     success = false })
                             with
                               (st573, x884)
                             in
                             match x884 with CorrectedBranchSample1 x885
                             in
                             match x885 with {history = x886}
                             in
                             match
                               p_map
                                 st573
                                 (lam x887.
                                    lam x888.
                                      lam x889.
                                        match x885 with {success = x890}
                                        in
                                        CorrectedBranchSample1
                                          { history = x887,
                                            logSamplingDensity = x888,
                                            logModelDensity = x889,
                                            success = x890 })
                                 x886
                             with
                               (st574, x892)
                             in
                             match x885 with {logSamplingDensity = x893}
                             in
                             match p_apply st574 x892 x893 with (st575, x894)
                             in
                             match x885 with {logModelDensity = x895}
                             in
                             p_apply st575 x894 x895)
                        x809
  in
  recursive
    let sampleTreeHistory =
      lam st376.
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 169:14-169:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
                            in
                            exit 1
                        in
                        let finalAge3 =
                          match tree2 with MsgLeaf carried30
                          then
                            carried30.age
                          else match tree2 with MsgNode carried31
                          then
                            carried31.age
                          else
                            let #var"268" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 175:6-175:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                            in
                            exit 1
                        in
                        match
                          rec16
                            st376
                            parentRep
                            rep1
                            parentAge
                            finalAge3
                            (match tree2 with MsgLeaf carried22
                             then
                               carried22.label
                             else match tree2 with MsgNode carried23
                             then
                               carried23.label
                             else
                               let #var"256" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 177:6-177:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create13 (addi (subi nHosts 1) 1))
                        with
                          (st377, unorderedBranch)
                        in
                        match paste01 st377 unorderedBranch with (st378, x590)
                        in
                        match quickSort1 st378 x590 with (st379, orderedEvents)
                        in
                        match length13 st379 orderedEvents with (st380, nEvents4)
                        in
                        match
                          allTimesValidBranch st380 parentRep orderedEvents 1 nEvents4 nHosts
                        with
                          (st381, x591)
                        in
                        match
                          p_bind
                            st381
                            hrmStoreSubmodel
                            (hrmInit {})
                            (lam st382.
                               lam x592.
                                 match
                                   match x592 with true
                                   then
                                     let s221 = create14 (addi (subi (length12 unorderedBranch) 1) 1)
                                     in
                                     match
                                       match s221 with [ _ ] ++ _
                                       then
                                         let x593 = get s221 0 in
                                         match
                                           hostIndepLikelihood
                                             st382
                                             1
                                             (get parentRep (subi x593 1))
                                             (get rep1 (subi x593 1))
                                             parentAge
                                             finalAge3
                                             (get unorderedBranch (subi x593 1))
                                             (match modelParams11 with ModelParams1 x1403
                                              then
                                                x1403.embeddedQMatrix
                                              else
                                                let #var"257" =
                                                  print
                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                                in
                                                exit 1)
                                         with
                                           (st383, x594)
                                         in
                                         match
                                           p_map
                                             st383
                                             (lam x595.
                                                addf 0. x595)
                                             x594
                                         with
                                           (st384, x596)
                                         in
                                         match splitAt s221 1 with {#label"1" = x597}
                                         in
                                         rec213
                                           st384
                                           parentRep
                                           rep1
                                           parentAge
                                           finalAge3
                                           modelParams11
                                           unorderedBranch
                                           x596
                                           x597
                                       else match s221 with ""
                                       in
                                       (st382, p_pure 0.)
                                     with
                                       (st385, x598)
                                     in
                                     match
                                       p_map
                                         st385
                                         (lam x599.
                                            lam x600.
                                              subf x599 x600)
                                         x598
                                     with
                                       (st386, x601)
                                     in
                                     match
                                       match geqi (length parentRep) (length rep1) with true
                                       then
                                         let acc29 = ("", parentRep) in
                                         match
                                           match rep1 with [ _ ] ++ _
                                           then
                                             match acc29 with (field8, field9)
                                             in
                                             match
                                               match field9 with [ _ ] ++ _
                                               then
                                                 match
                                                   p_map
                                                     st386
                                                     (lam x602.
                                                        addi x602 1)
                                                     (get field9 0)
                                                 with
                                                   (st387, x603)
                                                 in
                                                 match
                                                   mtxGet1 st387 x603 (addi (get rep1 0) 1) branchKernel
                                                 with
                                                   (st388, x604)
                                                 in
                                                 match log11 st388 x604 with (st389, x605)
                                                 in
                                                 match splitAt field9 1 with {#label"1" = x606}
                                                 in
                                                 (st389, (snoc field8 x605, x606))
                                               else
                                                 let x607 = error "foldl2: Cannot happen!" in
                                                 match x607 with (x608,)
                                                 in
                                                 match x607 with {#label"1" = x609}
                                                 in
                                                 (st386, (map
                                                   (lam x610.
                                                      p_pure x610)
                                                   x608, map
                                                   (lam x611.
                                                      p_pure x611)
                                                   x609))
                                             with
                                               (st390, x612)
                                             in
                                             match splitAt rep1 1 with {#label"1" = x613}
                                             in
                                             rec216 st390 branchKernel x612 x613
                                           else match rep1 with ""
                                           in
                                           (st386, acc29)
                                         with
                                           (st391, x614)
                                         in
                                         match x614 with (field10, field11)
                                         in
                                         (st391, field10)
                                       else
                                         let acc30 = ("", rep1) in
                                         match
                                           match parentRep with [ _ ] ++ _
                                           then
                                             match acc30 with (field12, field13)
                                             in
                                             match
                                               match field13 with [ _ ] ++ _
                                               then
                                                 match
                                                   p_map
                                                     st386
                                                     (lam x615.
                                                        addi x615 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st392, x616)
                                                 in
                                                 match
                                                   mtxGet1 st392 x616 (addi (get field13 0) 1) branchKernel
                                                 with
                                                   (st393, x617)
                                                 in
                                                 match log11 st393 x617 with (st394, x618)
                                                 in
                                                 match splitAt field13 1 with {#label"1" = x619}
                                                 in
                                                 (st394, (snoc field12 x618, x619))
                                               else
                                                 let x620 = error "foldl2: Cannot happen!" in
                                                 match x620 with (x621,)
                                                 in
                                                 match x620 with {#label"1" = x622}
                                                 in
                                                 (st386, (map
                                                   (lam x623.
                                                      p_pure x623)
                                                   x621, x622))
                                             with
                                               (st395, x624)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x625}
                                             in
                                             rec218 st395 branchKernel x624 x625
                                           else match parentRep with ""
                                           in
                                           (st386, acc30)
                                         with
                                           (st396, x626)
                                         in
                                         match x626 with (field14, field15)
                                         in
                                         (st396, field14)
                                     with
                                       (st397, x627)
                                     in
                                     match fold st397 0. x627 with (st398, x628)
                                     in
                                     match p_apply st398 x601 x628 with (st399, x629)
                                     in
                                     match
                                       p_bind
                                         st399
                                         hrmStoreSubmodel
                                         (hrmInit {})
                                         (lam st400.
                                            lam x630.
                                              match gti 1 x630 with true
                                              then
                                                match
                                                  getTotalRate st400 parentRep modelParams11 nHosts
                                                with
                                                  (st401, x631)
                                                in
                                                p_map
                                                  st401
                                                  (lam x632.
                                                     mulf (negf (subf parentAge finalAge3)) x632)
                                                  x631
                                              else match
                                                p_map
                                                  st400
                                                  (lam x633.
                                                     get x633 (subi 1 1))
                                                  orderedEvents
                                              with
                                                (st402, nextEvent2)
                                              in
                                              match
                                                p_map
                                                  st402
                                                  (lam x634.
                                                     match x634 with Event1 x3110
                                                     then
                                                       x3110.eventTime
                                                     else
                                                       let #var"258" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 25:17-25:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st403, newAge2)
                                              in
                                              match
                                                getTotalRate st403 parentRep modelParams11 nHosts
                                              with
                                                (st404, totalLeavingRate12)
                                              in
                                              match
                                                p_map
                                                  st404
                                                  (lam x635.
                                                     match x635 with Event1 x1432
                                                     then
                                                       x1432.host
                                                     else
                                                       let #var"259" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st405, hostIndex12)
                                              in
                                              match
                                                p_map
                                                  st405
                                                  (lam x636.
                                                     lam x637.
                                                       lam st406.
                                                         match
                                                           gti
                                                             (match x636 with Event1 x1412
                                                              then
                                                                x1412.fromState
                                                              else
                                                                let #var"260" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x637
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st406 parentRep hostIndex12 modelParams11
                                                         else
                                                           getGainRate2 st406 parentRep hostIndex12 modelParams11)
                                                  nextEvent2
                                              with
                                                (st407, x638)
                                              in
                                              match
                                                p_map
                                                  st407
                                                  (lam x639.
                                                     match x639 with Event1 x1422
                                                     then
                                                       x1422.toState
                                                     else
                                                       let #var"261" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st408, x640)
                                              in
                                              match
                                                p_subApply st408 hrmStoreSubmodel (hrmInit {}) x638 x640
                                              with
                                                (st409, x641)
                                              in
                                              match p_join st409 x641 with (st410, x642)
                                              in
                                              match
                                                p_map
                                                  st410
                                                  (lam x643.
                                                     lam x644.
                                                       divf x643 x644)
                                                  x642
                                              with
                                                (st411, x645)
                                              in
                                              match p_apply st411 x645 totalLeavingRate12 with (st412, x646)
                                              in
                                              match log11 st412 x646 with (st413, x647)
                                              in
                                              match
                                                p_map
                                                  st413
                                                  (lam x648.
                                                     lam x649.
                                                       lam x650.
                                                         addf (subf x648 x649) x650)
                                                  x647
                                              with
                                                (st414, x651)
                                              in
                                              match
                                                p_map
                                                  st414
                                                  (lam x652.
                                                     lam x653.
                                                       mulf (subf parentAge x652) x653)
                                                  newAge2
                                              with
                                                (st415, x654)
                                              in
                                              match p_apply st415 x654 totalLeavingRate12 with (st416, x655)
                                              in
                                              match p_apply st416 x651 x655 with (st417, x656)
                                              in
                                              match
                                                updateRepertoire st417 parentRep nextEvent2 nHosts
                                              with
                                                (st418, x657)
                                              in
                                              match
                                                fullModelWeight
                                                  st418
                                                  (addi 1 1)
                                                  x657
                                                  rep1
                                                  newAge2
                                                  finalAge3
                                                  orderedEvents
                                                  x630
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st419, x658)
                                              in
                                              p_apply st419 x656 x658)
                                         nEvents4
                                     with
                                       (st420, x659)
                                     in
                                     (st420, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = x629,
                                         logModelDensity = x659,
                                         success = true })
                                   else
                                     (st382, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = p_pure (log1 0.),
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st421, x660)
                                 in
                                 match x660 with CorrectedBranchSample1 x661
                                 in
                                 match x661 with {history = x662}
                                 in
                                 match
                                   p_map
                                     st421
                                     (lam x663.
                                        lam x664.
                                          lam x665.
                                            match x661 with {success = x666}
                                            in
                                            CorrectedBranchSample1
                                              { history = x663,
                                                logSamplingDensity = x664,
                                                logModelDensity = x665,
                                                success = x666 })
                                     x662
                                 with
                                   (st422, x667)
                                 in
                                 match x661 with {logSamplingDensity = x668}
                                 in
                                 match p_apply st422 x667 x668 with (st423, x669)
                                 in
                                 match x661 with {logModelDensity = x670}
                                 in
                                 p_apply st423 x669 x670)
                            x591
                        with
                          (st424, branchSample)
                        in
                        match
                          p_map
                            st424
                            (lam x671.
                               lam x672.
                                 mulf
                                   (subf
                                      (match x671 with CorrectedBranchSample1 x4610
                                       then
                                         x4610.logModelDensity
                                       else
                                         let #var"262" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 183:15-183:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x672)
                                   (exp1
                                      (mulf
                                         (int2float
                                            (match tree2 with MsgLeaf carried24
                                             then
                                               carried24.label
                                             else match tree2 with MsgNode carried25
                                             then
                                               carried25.label
                                             else
                                               let #var"263" =
                                                 print
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 183:90-183:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1))
                                         0.)))
                            branchSample
                        with
                          (st425, x673)
                        in
                        match
                          p_map
                            st425
                            (lam x674.
                               match x674 with CorrectedBranchSample1 x4710
                               then
                                 x4710.logSamplingDensity
                               else
                                 let #var"264" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 183:46-183:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st426, x675)
                        in
                        match p_apply st426 x673 x675 with (st427, x676)
                        in
                        let st428 =
                          p_weight
                            st427
                            hrmStoreWeight
                            (/-temp-/lam x679.
                               x679)
                            x676
                        in
                        let foo = {} in
                        match
                          p_map
                            st428
                            (lam x677.
                               match x677 with CorrectedBranchSample1 x4510
                               then
                                 x4510.history
                               else
                                 let #var"265" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 189:16-189:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st429, x678)
                        in
                        (st429, HistoryLeaf
                          { age =
                              match tree2 with MsgLeaf carried26
                              then
                                carried26.age
                              else match tree2 with MsgNode carried27
                              then
                                carried27.age
                              else
                                let #var"266" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 186:12-186:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
                                in
                                exit 1,
                            label =
                              match tree2 with MsgLeaf carried28
                              then
                                carried28.label
                              else match tree2 with MsgNode carried29
                              then
                                carried29.label
                              else
                                let #var"267" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 187:14-187:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            history = x678,
                            repertoire = rep1 })
                      else match
                        mtxElemMul
                          st376
                          (match tree2 with MsgLeaf carried32
                           then
                             match carried32 with {outMsg = #var"X8"}
                             in
                             p_pure #var"X8"
                           else match tree2 with MsgNode carried33
                           then
                             carried33.outMsg
                           else
                             let #var"270" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 192:34-192:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                             in
                             p_pure (exit 1))
                          preorderMsg
                      with
                        (st430, samplingProb)
                      in
                      match
                        suggestNodeRep
                          st430
                          samplingProb
                          nHosts
                          (match tree2 with MsgLeaf carried34
                           then
                             carried34.label
                           else match tree2 with MsgNode carried35
                           then
                             carried35.label
                           else
                             let #var"271" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 193:51-193:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                             in
                             exit 1)
                      with
                        (st431, rep2)
                      in
                      match any1 st431 rep2 with (st432, x680)
                      in
                      match bool2real st432 x680 with (st433, x681)
                      in
                      let st434 =
                        p_weight
                          st433
                          hrmStoreWeight
                          (lam x702.
                             externalLog
                               (addf
                                  x702
                                  (mulf
                                     (int2float
                                        (match tree2 with MsgLeaf carried50
                                         then
                                           carried50.label
                                         else match tree2 with MsgNode carried51
                                         then
                                           carried51.label
                                         else
                                           let #var"288" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 195:43-195:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1))
                                     0.)))
                          x681
                      in
                      let foo1 = {} in
                      match
                        sampleBranch
                          st434
                          parentRep
                          rep2
                          parentAge
                          (match tree2 with MsgLeaf carried36
                           then
                             carried36.age
                           else match tree2 with MsgNode carried37
                           then
                             carried37.age
                           else
                             let #var"272" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 203:6-203:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                             in
                             exit 1)
                          nHosts
                          (match tree2 with MsgLeaf carried38
                           then
                             carried38.label
                           else match tree2 with MsgNode carried39
                           then
                             carried39.label
                           else
                             let #var"273" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 205:6-205:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                             in
                             exit 1)
                          modelParams11
                          branchKernel
                      with
                        (st435, branchSample1)
                      in
                      match
                        p_map
                          st435
                          (lam x682.
                             lam x683.
                               lam x684.
                                 subf
                                   (subf
                                      (match x682 with CorrectedBranchSample1 x701
                                       then
                                         x701.logModelDensity
                                       else
                                         let #var"274" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 211:14-211:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x683)
                                   x684)
                          branchSample1
                      with
                        (st436, x685)
                      in
                      match
                        p_map
                          st436
                          (lam x686.
                             match x686 with CorrectedBranchSample1 x711
                             then
                               x711.logSamplingDensity
                             else
                               let #var"275" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 211:45-211:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st437, x687)
                      in
                      match p_apply st437 x685 x687 with (st438, x688)
                      in
                      match
                        getRepertoireSamplingDensity st438 rep2 samplingProb
                      with
                        (st439, x689)
                      in
                      match
                        p_map
                          st439
                          (lam x690.
                             mulf
                               x690
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
                                           let #var"276" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 211:113-211:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1))
                                     0.)))
                          x689
                      with
                        (st440, x691)
                      in
                      match p_apply st440 x688 x691 with (st441, x692)
                      in
                      let st442 =
                        p_weight
                          st441
                          hrmStoreWeight
                          (/-temp-/lam x700.
                             x700)
                          x692
                      in
                      let foo2 = {} in
                      match observationMessage1 st442 rep2 with (st443, newMsg)
                      in
                      match
                        mtxMul
                          st443
                          newMsg
                          (match tree2 with MsgNode x693
                           then
                             x693.leftKernel
                           else
                             let #var"277" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 215:33-215:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st444, x694)
                      in
                      match
                        sampleTreeHistory
                          st444
                          (match tree2 with MsgNode x6410
                           then
                             x6410.left
                           else
                             let #var"278" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 220:6-220:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          nHosts
                          x694
                          rep2
                          (match tree2 with MsgLeaf carried42
                           then
                             carried42.age
                           else match tree2 with MsgNode carried43
                           then
                             carried43.age
                           else
                             let #var"279" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 220:39-220:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6710
                           then
                             x6710.leftKernel
                           else
                             let #var"280" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 220:62-220:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st445, x695)
                      in
                      match
                        mtxMul
                          st445
                          newMsg
                          (match tree2 with MsgNode x6810
                           then
                             x6810.rightKernel
                           else
                             let #var"281" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 216:34-216:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st446, x696)
                      in
                      match
                        sampleTreeHistory
                          st446
                          (match tree2 with MsgNode x6010
                           then
                             x6010.right
                           else
                             let #var"282" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 223:6-223:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          nHosts
                          x696
                          rep2
                          (match tree2 with MsgLeaf carried44
                           then
                             carried44.age
                           else match tree2 with MsgNode carried45
                           then
                             carried45.age
                           else
                             let #var"283" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 223:41-223:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6310
                           then
                             x6310.rightKernel
                           else
                             let #var"284" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 223:64-223:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st447, x697)
                      in
                      match
                        p_map
                          st447
                          (lam x698.
                             match x698 with CorrectedBranchSample1 x5910
                             then
                               x5910.history
                             else
                               let #var"285" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 230:16-230:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st448, x699)
                      in
                      (st448, HistoryNode
                        { age =
                            match tree2 with MsgLeaf carried46
                            then
                              carried46.age
                            else match tree2 with MsgNode carried47
                            then
                              carried47.age
                            else
                              let #var"286" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 227:12-227:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                              let #var"287" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 228:14-228:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                              in
                              exit 1,
                          left = x695,
                          right = x697,
                          history = x699,
                          repertoire = rep2 })
  in
  let anon29 =
    lam n22.
      lam hostDistances2.
        lam x807.
          divf
            x807
            (divf
               (rec25 0. (paste0 hostDistances2))
               (int2float (muli n22 (subi n22 1))))
  in
  recursive
    let rec18 =
      lam c67.
        lam c68.
          lam s17.
            match s17 with [ _,
                _ ] ++ _
            then
              match splitAt s17 1 with {#label"1" = x703}
              in
              cons (anon29 c67 c68 (get s17 0)) (rec18 c67 c68 x703)
            else match s17 with [ e17 ]
            then
              match splitAt s17 1 with {#label"1" = x704}
              in
              let slice16 = x704 in
              [ anon29 c67 c68 e17 ]
            else match s17 with ""
            in
            ""
  in
  let anon30 =
    lam n21.
      lam hostDistances1.
        lam x806.
          rec18 n21 hostDistances1 x806
  in
  recursive
    let rec19 =
      lam c69.
        lam c70.
          lam s18.
            match s18 with [ _,
                _ ] ++ _
            then
              match splitAt s18 1 with {#label"1" = x705}
              in
              cons (anon30 c69 c70 (get s18 0)) (rec19 c69 c70 x705)
            else match s18 with [ e18 ]
            then
              match splitAt s18 1 with {#label"1" = x706}
              in
              let slice17 = x706 in
              [ anon30 c69 c70 e18 ]
            else match s18 with ""
            in
            ""
  in
  let input1 =
    { interactions =
        [ [ 0, 0, 2, 0, 2 ],
          [ 0, 0, 2, 0, 1 ],
          [ 0, 0, 2, 0, 1 ],
          [ 0, 0, 2, 0, 2 ],
          [ 0, 0, 2, 0, 1 ] ],
      subrootLabel = (negi 1),
      symbiontTree =
        Node
          { age = 6.839526974,
            label = 9,
            left = Leaf
                { age = 0., label = 1 },
            right =
              Node
                { age = 4.842443202,
                  label = 8,
                  left = Leaf
                      { age = 0., label = 2 },
                  right =
                    Node
                      { age = 3.501720109,
                        label = 7,
                        left =
                          Leaf
                            { age = 0., label = 3 },
                        right =
                          Node
                            { age = 3.127609164,
                              label = 6,
                              left =
                                Leaf
                                  { age = 0., label = 4 },
                              right =
                                Leaf
                                  { age = 0., label = 5 } } } } },
      hostDistances =
        [ [ 0., 1., 2., 2., 1. ],
          [ 1., 0., 2., 2., 1. ],
          [ 2., 2., 0., 1., 1. ],
          [ 2., 2., 1., 0., 1. ],
          [ 1., 1., 1., 1., 0. ] ],
      subrootLength = 6.84 }
  in
  match input1 with {symbiontTree = #var"X9"}
  in
  let symbiontTree = #var"X9" in
  match input1 with {hostDistances = #var"X10"}
  in
  let hostDistances = #var"X10" in
  match input1 with {subrootLength = #var"X11"}
  in
  let subrootLength = #var"X11" in
  let nHosts1 = length11 hostDistances in
  match
    p_assume
      st hrmStoreAssume (p_pure (mkDirichlet [ 1., 1., 1., 1. ]))
  with
    (st449, lambda)
  in
  match
    p_assume st449 hrmStoreAssume (p_pure (mkExponential 10.))
  with
    (st450, mu)
  in
  match
    p_assume st450 hrmStoreAssume (p_pure (mkExponential 1.))
  with
    (st451, beta)
  in
  match
    p_map
      st451
      (lam x707.
         subf 0. (get x707 (subi 1 1)))
      lambda
  with
    (st452, x708)
  in
  match
    p_map st452 (lam x709.
         get x709 (subi 1 1)) lambda
  with
    (st453, x710)
  in
  match
    p_map st453 (lam x712.
         get x712 (subi 2 1)) lambda
  with
    (st454, x713)
  in
  match
    p_map
      st454
      (lam x714.
         lam x715.
           subf 0. (addf (get x714 (subi 2 1)) x715))
      lambda
  with
    (st455, x716)
  in
  match
    p_map st455 (lam x717.
         get x717 (subi 3 1)) lambda
  with
    (st456, x718)
  in
  match p_apply st456 x716 x718 with (st457, x719)
  in
  match
    p_map st457 (lam x720.
         get x720 (subi 3 1)) lambda
  with
    (st458, x721)
  in
  match
    p_map st458 (lam x722.
         get x722 (subi 4 1)) lambda
  with
    (st459, x723)
  in
  match
    p_map
      st459
      (lam x724.
         subf 0. (get x724 (subi 4 1)))
      lambda
  with
    (st460, x725)
  in
  match
    p_traverseSeq
      st460
      (lam st461.
         lam x726.
           (st461, x726))
      [ x708,
        x710,
        p_pure 0.,
        x713,
        x719,
        x721,
        p_pure 0.,
        x723,
        x725 ]
  with
    (st462, x727)
  in
  match
    p_map
      st462
      (lam x728.
         tmOpaque (let len = length x728 in
          let a71 = externalExtArrMakeUninit extArrKindFloat64 len in
          recursive
            let work3 =
              lam i22.
                match eqi i22 len with true
                then
                  {}
                else
                  let #var"2110" = externalExtArrSet a71 i22 (get x728 i22) in
                  work3 (addi i22 1)
          in
          let #var"2210" = work3 0 in
          a71))
      x727
  with
    (st463, x729)
  in
  match matFromArrExn st463 3 3 x729 with (st464, mtx6)
  in
  match p_map st464 (lam x730.
         x730.m) mtx6 with (st465, m2)
  in
  match p_map st465 (lam x731.
         x731.n) mtx6 with (st466, n4)
  in
  match
    p_map
      st466
      (lam x732.
         lam x733.
           lam x734.
             lam x735.
               lam x736.
                 tmOpaque (let b14 = matMakeUninit (externalExtArrKind x736.arr) x732 x733
                  in
                  let #var"14" = externalCblasCopy x734 x736.arr 1 b14.arr 1 in
                  let #var"15" = externalCblasScal x734 x735 b14.arr 1 in
                  b14))
      m2
  with
    (st467, x737)
  in
  match p_apply st467 x737 n4 with (st468, x738)
  in
  match
    p_map
      st468
      (lam x739.
         lam x740.
           muli x739 x740)
      m2
  with
    (st469, x741)
  in
  match p_apply st469 x741 n4 with (st470, x742)
  in
  match p_apply st470 x738 x742 with (st471, x743)
  in
  match p_apply st471 x743 mu with (st472, x744)
  in
  match p_apply st472 x744 mtx6 with (st473, qMatrix2)
  in
  let ns = rec19 (length11 hostDistances) hostDistances hostDistances
  in
  match mtxGet st473 2 2 qMatrix2 with (st474, x745)
  in
  match p_map st474 (lam x746.
         negf x746) x745 with (st475, q2)
  in
  match mtxGet st475 1 1 qMatrix2 with (st476, x747)
  in
  match p_map st476 (lam x748.
         negf x748) x747 with (st477, x749)
  in
  match mtxGet st477 3 3 qMatrix2 with (st478, x750)
  in
  match p_map st478 (lam x751.
         negf x751) x750 with (st479, x752)
  in
  match mtxGet st479 2 1 qMatrix2 with (st480, x753)
  in
  match
    p_map
      st480
      (lam x754.
         lam x755.
           divf x754 x755)
      x753
  with
    (st481, x756)
  in
  match p_apply st481 x756 q2 with (st482, x757)
  in
  match mtxGet st482 2 3 qMatrix2 with (st483, x758)
  in
  match
    p_map
      st483
      (lam x759.
         lam x760.
           divf x759 x760)
      x758
  with
    (st484, x761)
  in
  match p_apply st484 x761 q2 with (st485, x762)
  in
  let modelParams2 =
    ModelParams1
      { beta = beta,
        hostMetric =
          mtxCreate (length11 ns) (length1 (get ns (subi 1 1))) (paste0 ns),
        embeddedQMatrix =
          EmbeddedMarkovChainMatrix1
            { totalRates =
                [ x749,
                  q2,
                  x752 ],
              transitionProbs =
                [ [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ],
                  [ x757,
                    p_pure 0.,
                    x762 ],
                  [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ] ],
              mat = qMatrix2 } }
  in
  match input1 with {interactions = #var"X12"}
  in
  match
    postorderTraverse st485 symbiontTree qMatrix2 #var"X12" nHosts1
  with
    (st486, postorderTree)
  in
  match input1 with {subrootLabel = #var"X13"}
  in
  let subrootLabel1 = #var"X13" in
  match mtxSclrMul st486 subrootLength qMatrix2 with (st487, x763)
  in
  match matExpExn st487 x763 with (st488, subrootKernel)
  in
  match mtxTrans st488 subrootKernel with (st489, x764)
  in
  match
    mtxMul
      st489
      (match postorderTree with MsgLeaf carried52
       then
         match carried52 with {outMsg = #var"X14"}
         in
         p_pure #var"X14"
       else match postorderTree with MsgNode carried53
       then
         carried53.outMsg
       else
         let #var"289" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 84:32-84:52>:\nField \'outMsg\' not found\n[0m  let subrootInfo = subrootNode([31mpostorderTree.outMsg[0m[0m, subrootLength, subrootLabel, qMatrix, nHosts);\n"
         in
         p_pure (exit 1))
      x764
  with
    (st490, a32)
  in
  let b4 = mtxCreate nHosts1 3 (rep (muli 3 nHosts1) 1.) in
  match
    p_map
      st490
      (lam x765.
         match x765 with {m = #var"X15"}
         in
         match b4 with {m = #var"X16"}
         in
         eqi #var"X15" #var"X16")
      a32
  with
    (st491, x766)
  in
  match
    p_map
      st491
      (lam x767.
         match x767 with {n = #var"X17"}
         in
         match b4 with {n = #var"X18"}
         in
         eqi #var"X17" #var"X18")
      a32
  with
    (st492, x768)
  in
  match and1 st492 x766 x768 with (st493, x769)
  in
  match
    p_bind
      st493
      hrmStoreSubmodel
      (hrmInit {})
      (lam st494.
         lam x770.
           match
             match x770 with true
             then
               match
                 p_map
                   st494
                   (lam x771.
                      tmOpaque (let c210 = matMakeUninit (externalExtArrKind x771.arr) x771.m x771.n
                       in
                       let #var"16" = matElemMulNoAlloc x771 b4 c210 in
                       c210))
                   a32
               with
                 (st495, x772)
               in
               (st495, Right
                 x772)
             else
               (st494, Left
                 (DimensionMismatch
                    {}))
           with
             (st496, n3)
           in
           match n3 with Right x773
           then
             p_map
               st496
               (lam x774.
                  Right
                    x774)
               x773
           else match n3 with Left x775
           in
           (st496, p_pure (Left
                x775)))
      x769
  with
    (st497, x776)
  in
  match eitherEither st497 x776 with (st498, subrootSamplingProb)
  in
  match
    suggestNodeRep st498 subrootSamplingProb nHosts1 (negi 1)
  with
    (st499, subrootRep)
  in
  match any1 st499 subrootRep with (st500, x777)
  in
  match bool2real st500 x777 with (st501, x778)
  in
  let st502 =
    p_weight
      st501
      hrmStoreWeight
      (lam x805.
         externalLog (addf x805 (mulf (int2float subrootLabel1) 0.)))
      x778
  in
  let foo6 = {} in
  match
    getRepertoireSamplingDensity st502 subrootRep subrootSamplingProb
  with
    (st503, x779)
  in
  let st504 =
    p_weight
      st503
      hrmStoreWeight
      (lam x804.
         addf
           (subf
              (negf
                 (log1
                    (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1)))))
              x804)
           (mulf (int2float subrootLabel1) 0.))
      x779
  in
  let foo7 = {} in
  match observationMessage1 st504 subrootRep with (st505, x780)
  in
  match mtxMul st505 x780 subrootKernel with (st506, x781)
  in
  let subrootInfo =
    SubrootInfo1
      { kernel = subrootKernel, rep = subrootRep, msg = x781 }
  in
  match
    mtxElemMul
      st506
      (match subrootInfo with SubrootInfo1 x1091
       then
         x1091.msg
       else
         let #var"290" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 86:36-86:51>:\nField \'msg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31msubrootInfo.msg[0m[0m, postorderTree.outMsg);\n"
         in
         p_pure (exit 1))
      (match postorderTree with MsgLeaf carried54
       then
         match carried54 with {outMsg = #var"X19"}
         in
         p_pure #var"X19"
       else match postorderTree with MsgNode carried55
       then
         carried55.outMsg
       else
         let #var"291" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 86:53-86:73>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul(subrootInfo.msg, [31mpostorderTree.outMsg[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st507, rootSamplingProb)
  in
  match
    suggestNodeRep
      st507
      rootSamplingProb
      nHosts1
      (match postorderTree with MsgLeaf carried56
       then
         carried56.label
       else match postorderTree with MsgNode carried57
       then
         carried57.label
       else
         let #var"292" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 87:57-87:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
         in
         exit 1)
  with
    (st508, rootRep)
  in
  match any1 st508 rootRep with (st509, x782)
  in
  match bool2real st509 x782 with (st510, x783)
  in
  let st511 =
    p_weight
      st510
      hrmStoreWeight
      (lam x803.
         externalLog
           (addf
              x803
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried68
                     then
                       carried68.label
                     else match postorderTree with MsgNode carried69
                     then
                       carried69.label
                     else
                       let #var"2109" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 88:45-88:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1))
                 0.)))
      x783
  in
  let foo3 = {} in
  let rootAge =
    match postorderTree with MsgLeaf carried66
    then
      carried66.age
    else match postorderTree with MsgNode carried67
    then
      carried67.age
    else
      let #var"2108" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 91:16-91:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    sampleBranch
      st511
      (match subrootInfo with SubrootInfo1 x1011
       then
         x1011.rep
       else
         let #var"293" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 93:4-93:19>:\nField \'rep\' not found\n[0m    [31msubrootInfo.rep[0m[0m,\n"
         in
         map (lam x784.
              p_pure x784) (exit 1))
      rootRep
      (addf rootAge subrootLength)
      rootAge
      nHosts1
      (negi 1)
      modelParams2
      (match subrootInfo with SubrootInfo1 x1021
       then
         x1021.kernel
       else
         let #var"294" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 100:4-100:22>:\nField \'kernel\' not found\n[0m    [31msubrootInfo.kernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st512, subrootBranchSample)
  in
  match
    p_map
      st512
      (lam x785.
         lam x786.
           lam x787.
             subf
               (subf
                  (match x785 with CorrectedBranchSample1 x971
                   then
                     x971.logModelDensity
                   else
                     let #var"295" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 108:4-108:39>:\nField \'logModelDensity\' not found\n[0m    [31msubrootBranchSample.logModelDensity[0m\n"
                     in
                     exit 1)
                  x786)
               x787)
      subrootBranchSample
  with
    (st513, x788)
  in
  match
    p_map
      st513
      (lam x789.
         match x789 with CorrectedBranchSample1 x981
         then
           x981.logSamplingDensity
         else
           let #var"296" =
             print
               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 109:6-109:44>:\nField \'logSamplingDensity\' not found\n[0m    - [31msubrootBranchSample.logSamplingDensity[0m\n"
           in
           exit 1)
      subrootBranchSample
  with
    (st514, x790)
  in
  match p_apply st514 x788 x790 with (st515, x791)
  in
  match
    getRepertoireSamplingDensity st515 rootRep rootSamplingProb
  with
    (st516, x792)
  in
  match
    p_map
      st516
      (lam x793.
         mulf
           x793
           (exp1
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried58
                     then
                       carried58.label
                     else match postorderTree with MsgNode carried59
                     then
                       carried59.label
                     else
                       let #var"297" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 110:40-110:59>:\nField \'label\' not found\n[0m    - rootLogSamplingDensity * exp(Real([31mpostorderTree.label[0m[0m) * 0.)\n"
                       in
                       exit 1))
                 0.)))
      x792
  with
    (st517, x794)
  in
  match p_apply st517 x791 x794 with (st518, x795)
  in
  let st519 =
    p_weight
      st518 hrmStoreWeight (/-temp-/lam x802.
         x802) x795
  in
  let foo4 = {} in
  match observationMessage1 st519 rootRep with (st520, newMsg1)
  in
  let rootAge1 =
    match postorderTree with MsgLeaf carried64
    then
      carried64.age
    else match postorderTree with MsgNode carried65
    then
      carried65.age
    else
      let #var"2107" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 119:16-119:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    mtxMul
      st520
      newMsg1
      (match postorderTree with MsgNode x961
       then
         x961.leftKernel
       else
         let #var"298" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 115:31-115:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st521, x796)
  in
  match
    sampleTreeHistory
      st521
      (match postorderTree with MsgNode x911
       then
         x911.left
       else
         let #var"299" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 121:4-121:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
         in
         exit 1)
      nHosts1
      x796
      rootRep
      rootAge1
      modelParams2
      (match postorderTree with MsgNode x921
       then
         x921.leftKernel
       else
         let #var"2100" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 121:72-121:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st522, x797)
  in
  match
    mtxMul
      st522
      newMsg1
      (match postorderTree with MsgNode x951
       then
         x951.rightKernel
       else
         let #var"2101" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 116:32-116:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st523, x798)
  in
  match
    sampleTreeHistory
      st523
      (match postorderTree with MsgNode x891
       then
         x891.right
       else
         let #var"2102" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 125:4-125:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
         in
         exit 1)
      nHosts1
      x798
      rootRep
      rootAge1
      modelParams2
      (match postorderTree with MsgNode x901
       then
         x901.rightKernel
       else
         let #var"2103" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 125:74-125:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st524, x799)
  in
  match
    p_map
      st524
      (lam x800.
         match x800 with CorrectedBranchSample1 x881
         then
           x881.history
         else
           let #var"2104" =
             print
               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 132:36-132:63>:\nField \'history\' not found\n[0m    repertoire = rootRep, history = [31msubrootBranchSample.history[0m\n"
           in
           exit 1)
      subrootBranchSample
  with
    (st525, x801)
  in
  p_export
    st525
    hrmStoreExport
    (p_pure
       (dprint
          (ReturnType1
             { mu = mu,
               beta = beta,
               tree =
                 HistoryNode
                   { age =
                       match symbiontTree with Leaf carried60
                       then
                         carried60.age
                       else match symbiontTree with Node carried61
                       then
                         carried61.age
                       else
                         let #var"2105" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 130:10-130:26>:\nField \'age\' not found\n[0m    age = [31msymbiontTree.age[0m[0m, label = symbiontTree.label,\n"
                         in
                         exit 1,
                     label =
                       match symbiontTree with Leaf carried62
                       then
                         carried62.label
                       else match symbiontTree with Node carried63
                       then
                         carried63.label
                       else
                         let #var"2106" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 130:36-130:54>:\nField \'label\' not found\n[0m    age = symbiontTree.age, label = [31msymbiontTree.label[0m[0m,\n"
                         in
                         exit 1,
                     left = x797,
                     right = x799,
                     history = x801,
                     repertoire = rootRep },
               lambda = lambda })))
