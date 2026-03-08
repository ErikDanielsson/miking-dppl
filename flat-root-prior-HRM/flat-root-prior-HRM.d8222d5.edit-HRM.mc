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
  type Bridge p70 in
  con Bridge1: all p71. p71 -> Bridge p71 in
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
    lam st954.
      lam a92.
        lam b31.
          p_select
            st954
            (lam x1513.
               match x1513 with true
               then
                 b31
               else
                 p_pure false)
            a92
  in
  let pow = lam x1773.
      lam y2.
        externalPow x1773 y2
  in
  let pow1 =
    lam st953.
      lam x1772.
        lam y1.
          p_map
            st953 (lam x1512.
               externalPow x1772 x1512) y1
  in
  let pow2 =
    lam st951.
      lam x1771.
        lam y.
          match
            p_map
              st951
              (lam x1509.
                 lam x1510.
                   externalPow x1509 x1510)
              x1771
          with
            (st952, x1511)
          in
          p_apply st952 x1511 y
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
      lam x1508.
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
    lam st950.
      lam a75.
        lam i24.
          p_map
            st950
            (lam x1507.
               externalExtArrGet x1507 i24)
            a75
  in
  let extArrOfSeq =
    lam st949.
      lam kind11.
        lam seq6.
          p_map
            st949
            (lam x1506.
               tmOpaque (let len2 = length x1506 in
                let a712 = externalExtArrMakeUninit kind11 len2 in
                recursive
                  let work32 =
                    lam i222.
                      match eqi i222 len2 with true
                      then
                        {}
                      else
                        let #var"2157" = externalExtArrSet a712 i222 (get x1506 i222)
                        in
                        work32 (addi i222 1)
                in
                let #var"2212" = work32 0 in
                a712))
            seq6
  in
  let matErrorToString =
    lam err3.
      match err3 with DimensionMismatch carried73
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
    lam st947.
      lam kind.
        lam m4.
          lam n61.
            match
              p_map
                st947
                (lam x1504.
                   externalExtArrMakeUninit kind (muli m4 x1504))
                n61
            with
              (st948, x1505)
            in
            (st948, { arr = x1505, n = n61, m = m4 })
  in
  let matGetExn =
    lam a661.
      lam i212.
        lam j31.
          match a661 with {arr = #var"X69"}
          in
          match a661 with {n = #var"X70"}
          in
          externalExtArrGet #var"X69" (addi (muli i212 #var"X70") j31)
  in
  let matGetExn1 =
    lam st944.
      lam a66.
        lam i211.
          lam j3.
            match
              p_map
                st944
                (lam x1499.
                   lam x1500.
                     match x1499 with {arr = #var"X67"}
                     in
                     externalExtArrGet #var"X67" x1500)
                a66
            with
              (st945, x1501)
            in
            match
              p_map
                st945
                (lam x1502.
                   match x1502 with {n = #var"X68"}
                   in
                   addi (muli i211 #var"X68") j3)
                a66
            with
              (st946, x1503)
            in
            p_apply st946 x1501 x1503
  in
  let matFromArrExn =
    lam st943.
      lam m3.
        lam n51.
          lam a622.
            p_map
              st943
              (lam x1498.
                 match eqi (muli m3 n51) (externalExtArrLength x1498) with true
                 then
                   { arr = x1498, n = n51, m = m3 }
                 else
                   error "matFromArrExn: dimensions mismatch")
              a622
  in
  let matCopy =
    lam st936.
      lam a60.
        match
          p_map
            st936
            (lam x1484.
               lam x1485.
                 { x1484 with arr = x1485 })
            a60
        with
          (st937, x1486)
        in
        match
          p_map
            st937
            (lam x1487.
               lam x1488.
                 tmOpaque (let b23 = extArrMakeUninit (externalExtArrKind x1487.arr) x1488
                  in
                  let #var"20" = externalCblasCopy x1488 x1487.arr 1 b23 1 in
                  b23))
            a60
        with
          (st938, x1489)
        in
        match
          p_map
            st938
            (lam x1490.
               lam x1492.
                 match x1490 with {m = #var"X66"}
                 in
                 muli #var"X66" x1492)
            a60
        with
          (st939, x1493)
        in
        match
          p_map st939 (lam x1494.
               x1494.n) a60
        with
          (st940, x1495)
        in
        match p_apply st940 x1493 x1495 with (st941, x1496)
        in
        match p_apply st941 x1489 x1496 with (st942, x1497)
        in
        p_apply st942 x1486 x1497
  in
  let matHasSameShape2 =
    lam a58.
      lam b21.
        match a58 with {m = #var"X62"}
        in
        match b21 with {m = #var"X63"}
        in
        match a58 with {n = #var"X64"}
        in
        match b21 with {n = #var"X65"}
        in
        and (eqi #var"X62" #var"X63") (eqi #var"X64" #var"X65")
  in
  let matTranposeNoAlloc =
    lam a55.
      lam b19.
        match a55 with {m = #var"X54"}
        in
        match b19 with {n = #var"X55"}
        in
        match a55 with {n = #var"X56"}
        in
        match b19 with {m = #var"X57"}
        in
        match and (eqi #var"X54" #var"X55") (eqi #var"X56" #var"X57") with true
        then
          match a55 with {m = #var"X58"}
          in
          match a55 with {n = #var"X59"}
          in
          match a55 with {arr = #var"X60"}
          in
          match b19 with {arr = #var"X61"}
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
    lam a54.
      lam b18.
        lam c310.
          match
            and (matHasSameShape2 a54 b18) (matHasSameShape2 b18 c310)
          with
            true
          then
            match a54 with {m = #var"X49"}
            in
            match a54 with {n = #var"X50"}
            in
            match a54 with {arr = #var"X51"}
            in
            match b18 with {arr = #var"X52"}
            in
            match c310 with {arr = #var"X53"}
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
    lam st922.
      lam a48.
        lam b12.
          match
            p_map st922 (lam x1455.
                 x1455.n) a48
          with
            (st923, x1456)
          in
          match
            p_map
              st923
              (lam x1457.
                 lam x1458.
                   lam st924.
                     match
                       match eqi x1457 x1458 with true
                       then
                         match
                           p_map
                             st924
                             (lam x1459.
                                x1459.m)
                             a48
                         with
                           (st925, x1460)
                         in
                         match
                           p_map
                             st925
                             (lam x1463.
                                lam x1464.
                                  lam x1465.
                                    lam x1466.
                                      tmOpaque (let c110 = matMakeUninit (externalExtArrKind x1466.arr) x1463 x1464
                                       in
                                       let #var"13" =
                                         externalCblasGemm
                                           cblasRowMajor
                                           cblasNoTrans
                                           cblasNoTrans
                                           x1463
                                           x1464
                                           x1457
                                           1.
                                           x1465.arr
                                           x1457
                                           x1466.arr
                                           x1464
                                           0.
                                           c110.arr
                                           x1464
                                       in
                                       c110))
                             x1460
                         with
                           (st926, x1467)
                         in
                         match
                           p_map
                             st926
                             (lam x1468.
                                x1468.n)
                             b12
                         with
                           (st927, x1469)
                         in
                         match p_apply st927 x1467 x1469 with (st928, x1470)
                         in
                         match p_apply st928 x1470 a48 with (st929, x1473)
                         in
                         match p_apply st929 x1473 b12 with (st930, x1474)
                         in
                         (st930, Right
                           x1474)
                       else
                         (st924, Left
                           (DimensionMismatch
                              {}))
                     with
                       (st931, n6)
                     in
                     match n6 with Right x1475
                     then
                       p_map
                         st931
                         (lam x1476.
                            Right
                              x1476)
                         x1475
                     else match n6 with Left x1477
                     in
                     (st931, p_pure (Left
                          x1477)))
              x1456
          with
            (st932, x1478)
          in
          match
            p_map st932 (lam x1479.
                 x1479.m) b12
          with
            (st933, x1480)
          in
          match
            p_subApply st933 hrmStoreSubmodel (hrmInit {}) x1478 x1480
          with
            (st934, x1481)
          in
          match p_join st934 x1481 with (st935, x1482)
          in
          p_map
            st935
            (lam x1483.
               match x1483 with Left carried71
               then
                 error (matErrorToString carried71)
               else match x1483 with Right carried72
               in
               carried72)
            x1482
  in
  let exp1 = lam x1621.
      externalExp x1621 in
  let log1 = lam x1612.
      externalLog x1612 in
  let log11 =
    lam st921.
      lam x1611.
        p_map st921 (lam x1454.
             externalLog x1454) x1611
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
        match splitAt l52 1 with {#label"1" = x1453}
        in
        rec2 (concat "" (get l52 0)) x1453
      else match l52 with ""
      in
      ""
  in
  let paste01 =
    lam st915.
      lam l51.
        match l51 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st915
              (lam st916.
                 lam x1447.
                   (st916, x1447))
              ""
          with
            (st917, x1448)
          in
          match p_map st917 concat x1448 with (st918, x1449)
          in
          match p_apply st918 x1449 (get l51 0) with (st919, x1450)
          in
          match splitAt l51 1 with {#label"1" = x1451}
          in
          rec22 st919 x1450 x1451
        else match l51 with ""
        in
        p_traverseSeq
          st915
          (lam st920.
             lam x1452.
               (st920, x1452))
          ""
  in
  let paste02 =
    lam st909.
      lam l5.
        match l5 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st909
              (lam st910.
                 lam x1441.
                   (st910, x1441))
              ""
          with
            (st911, x1442)
          in
          match p_map st911 concat x1442 with (st912, x1443)
          in
          match p_apply st912 x1443 (get l5 0) with (st913, x1444)
          in
          match splitAt l5 1 with {#label"1" = x1445}
          in
          rec24 st913 x1444 x1445
        else match l5 with ""
        in
        p_traverseSeq
          st909
          (lam st914.
             lam x1446.
               (st914, x1446))
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
  let length13 = lam st908.
      lam l31.
        p_map st908 length l31
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
    lam st906.
      lam s81.
        match s81 with [ _ ] ++ _
        then
          match
            p_map
              st906 (lam x1438.
                 addf 0. x1438) (get s81 0)
          with
            (st907, x1439)
          in
          match splitAt s81 1 with {#label"1" = x1440}
          in
          rec26 st907 x1439 x1440
        else match s81 with ""
        in
        (st906, p_pure 0.)
  in
  let anon1 =
    lam x1435.
      lam x1436.
        lam x1437.
          match x1437 with true
          then
            snoc x1435 (addi x1436 1)
          else
            x1435
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
    lam st903.
      lam s62.
        match s62 with [ e24 ] ++ rest3
        then
          match
            p_map
              st903
              (lam x1428.
                 match x1428 with true
                 then
                   snoc "" (addi 0 1)
                 else
                   "")
              e24
          with
            (st904, x1429)
          in
          work1 st904 x1429 (addi 0 1) rest3
        else
          p_traverseSeq
            st903
            (lam st905.
               lam x1430.
                 (st905, x1430))
            ""
  in
  let whichTrue2 =
    lam st902.
      lam s61.
        p_map
          st902
          (lam x1427.
             match x1427 with [ e23 ] ++ rest2
             then
               work (anon1 "" 0 e23) (addi 0 1) rest2
             else
               "")
          s61
  in
  let bool2real =
    lam st901.
      lam v.
        p_map
          st901
          (lam x1426.
             match x1426 with true
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
                     let #var"2156" = externalExtArrSet a711 i221 (get data i221) in
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
    lam st900.
      lam row13.
        lam col2.
          lam mtx72.
            matGetExn1 st900 mtx72 (subi row13 1) (subi col2 1)
  in
  let mtxGet1 =
    lam st894.
      lam row12.
        lam col1.
          lam mtx71.
            match
              p_map
                st894
                (lam x1407.
                   lam x1408.
                     match x1407 with {arr = #var"X48"}
                     in
                     externalExtArrGet #var"X48" x1408)
                mtx71
            with
              (st895, x1409)
            in
            match
              p_map st895 (lam x1410.
                   subi x1410 1) row12
            with
              (st896, x1415)
            in
            match
              p_map
                st896
                (lam x1416.
                   lam x1417.
                     addi (muli x1416 x1417) (subi col1 1))
                x1415
            with
              (st897, x1418)
            in
            match
              p_map st897 (lam x1419.
                   x1419.n) mtx71
            with
              (st898, x1420)
            in
            match p_apply st898 x1418 x1420 with (st899, x1425)
            in
            p_apply st899 x1409 x1425
  in
  let mtxGet2 =
    lam st886.
      lam row11.
        lam col.
          lam mtx7.
            match
              p_map
                st886
                (lam x1380.
                   lam x1385.
                     match x1380 with {arr = #var"X47"}
                     in
                     externalExtArrGet #var"X47" x1385)
                mtx7
            with
              (st887, x1386)
            in
            match
              p_map st887 (lam x1387.
                   subi x1387 1) row11
            with
              (st888, x1388)
            in
            match
              p_map
                st888
                (lam x1389.
                   lam x1390.
                     lam x1395.
                       addi (muli x1389 x1390) x1395)
                x1388
            with
              (st889, x1396)
            in
            match
              p_map st889 (lam x1397.
                   x1397.n) mtx7
            with
              (st890, x1398)
            in
            match p_apply st890 x1396 x1398 with (st891, x1399)
            in
            match
              p_map st891 (lam x1400.
                   subi x1400 1) col
            with
              (st892, x1405)
            in
            match p_apply st892 x1399 x1405 with (st893, x1406)
            in
            p_apply st893 x1386 x1406
  in
  let anon2 =
    lam new5.
      lam mtx65.
        lam row5.
          lam x1378.
            lam x1379.
              match new5 with {arr = #var"X45"}
              in
              match new5 with {n = #var"X46"}
              in
              externalExtArrSet
                #var"X45"
                (addi (muli 0 #var"X46") x1378)
                (matGetExn mtx65 (subi row5 1) (subi x1379 1))
  in
  let anon3 =
    lam st883.
      lam new4.
        lam mtx64.
          lam row4.
            lam x1371.
              lam x1372.
                match new4 with {arr = #var"X43"}
                in
                match
                  p_map
                    st883
                    (lam x1373.
                       lam x1374.
                         externalExtArrSet x1373 x1374 (matGetExn mtx64 (subi row4 1) (subi x1372 1)))
                    #var"X43"
                with
                  (st884, x1375)
                in
                match new4 with {n = #var"X44"}
                in
                match
                  p_map
                    st884
                    (lam x1376.
                       addi (muli 0 x1376) x1371)
                    #var"X44"
                with
                  (st885, x1377)
                in
                p_apply st885 x1375 x1377
  in
  let anon4 =
    lam st877.
      lam new3.
        lam mtx63.
          lam row3.
            lam x1350.
              lam x1355.
                match new3 with {arr = #var"X39"}
                in
                match
                  p_map
                    st877
                    (lam x1356.
                       lam x1357.
                         lam x1358.
                           externalExtArrSet x1356 x1357 x1358)
                    #var"X39"
                with
                  (st878, x1359)
                in
                match new3 with {n = #var"X40"}
                in
                match
                  p_map
                    st878
                    (lam x1360.
                       addi (muli 0 x1360) x1350)
                    #var"X40"
                with
                  (st879, x1365)
                in
                match p_apply st879 x1359 x1365 with (st880, x1366)
                in
                match
                  p_map st880 (lam x1367.
                       subi x1367 1) row3
                with
                  (st881, x1368)
                in
                match
                  p_map
                    st881
                    (lam x1369.
                       match mtx63 with {arr = #var"X41"}
                       in
                       match mtx63 with {n = #var"X42"}
                       in
                       externalExtArrGet #var"X41" (addi (muli x1369 #var"X42") (subi x1355 1)))
                    x1368
                with
                  (st882, x1370)
                in
                p_apply st882 x1366 x1370
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
    lam mtx62.
      lam row2.
        lam cols2.
          match mtx62 with {arr = #var"X38"}
          in
          let new2 =
            matMakeUninit (externalExtArrKind #var"X38") 1 (length cols2)
          in
          let #var"2412" = rec1 new2 mtx62 row2 0 cols2 in
          let #var"102" = {} in
          new2
  in
  let mtxRowCols1 =
    lam st867.
      lam mtx61.
        lam row1.
          lam cols1.
            match mtx61 with {arr = #var"X37"}
            in
            match p_map st867 length cols1 with (st868, x1341)
            in
            match
              matMakeUninit1 st868 (externalExtArrKind #var"X37") 1 x1341
            with
              (st869, new1)
            in
            match
              p_bind
                st869
                hrmStoreSubmodel
                (hrmInit {})
                (lam st870.
                   lam x1342.
                     match
                       match x1342 with [ _,
                           _ ] ++ _
                       then
                         match anon3 st870 new1 mtx61 row1 0 (get x1342 0) with (st871, x1343)
                         in
                         match splitAt x1342 1 with {#label"1" = x1344}
                         in
                         match rec11 st871 new1 mtx61 row1 (addi 0 1) x1344 with (st872, x1345)
                         in
                         (st872, cons x1343 x1345)
                       else match x1342 with [ e22 ]
                       then
                         match splitAt x1342 1 with {#label"1" = x1346}
                         in
                         let slice21 = x1346 in
                         match anon3 st870 new1 mtx61 row1 0 e22 with (st873, x1347)
                         in
                         (st873, [ x1347 ])
                       else match x1342 with ""
                       in
                       (st870, "")
                     with
                       (st874, x1348)
                     in
                     p_traverseSeq
                       st874
                       (lam st875.
                          lam x1349.
                            (st875, x1349))
                       x1348)
                cols1
            with
              (st876, #var"2411")
            in
            let #var"101" = {} in
            (st876, new1)
  in
  let mtxRowCols2 =
    lam st857.
      lam mtx6.
        lam row.
          lam cols.
            match mtx6 with {arr = #var"X36"}
            in
            match p_map st857 length cols with (st858, x1328)
            in
            match
              matMakeUninit1 st858 (externalExtArrKind #var"X36") 1 x1328
            with
              (st859, new)
            in
            match
              p_bind
                st859
                hrmStoreSubmodel
                (hrmInit {})
                (lam st860.
                   lam x1329.
                     match
                       match x1329 with [ _,
                           _ ] ++ _
                       then
                         match anon4 st860 new mtx6 row 0 (get x1329 0) with (st861, x1330)
                         in
                         match splitAt x1329 1 with {#label"1" = x1335}
                         in
                         match rec12 st861 new mtx6 row (addi 0 1) x1335 with (st862, x1336)
                         in
                         (st862, cons x1330 x1336)
                       else match x1329 with [ e21 ]
                       then
                         match splitAt x1329 1 with {#label"1" = x1337}
                         in
                         let slice20 = x1337 in
                         match anon4 st860 new mtx6 row 0 e21 with (st863, x1338)
                         in
                         (st863, [ x1338 ])
                       else match x1329 with ""
                       in
                       (st860, "")
                     with
                       (st864, x1339)
                     in
                     p_traverseSeq
                       st864
                       (lam st865.
                          lam x1340.
                            (st865, x1340))
                       x1339)
                cols
            with
              (st866, #var"2410")
            in
            let #var"10" = {} in
            (st866, new)
  in
  let mtxSclrMul =
    lam st849.
      lam scalar.
        lam mtx51.
          match
            p_map st849 (lam x1307.
                 x1307.m) mtx51
          with
            (st850, m21)
          in
          match
            p_map st850 (lam x1308.
                 x1308.n) mtx51
          with
            (st851, n41)
          in
          match
            p_map
              st851
              (lam x1309.
                 lam x1310.
                   lam x1315.
                     lam x1316.
                       tmOpaque (let b141 = matMakeUninit (externalExtArrKind x1316.arr) x1309 x1310
                        in
                        let #var"141" = externalCblasCopy x1315 x1316.arr 1 b141.arr 1
                        in
                        let #var"151" = externalCblasScal x1315 scalar b141.arr 1 in
                        b141))
              m21
          with
            (st852, x1317)
          in
          match p_apply st852 x1317 n41 with (st853, x1318)
          in
          match
            p_map
              st853
              (lam x1319.
                 lam x1320.
                   muli x1319 x1320)
              m21
          with
            (st854, x1325)
          in
          match p_apply st854 x1325 n41 with (st855, x1326)
          in
          match p_apply st855 x1318 x1326 with (st856, x1327)
          in
          p_apply st856 x1327 mtx51
  in
  let mtxTrans =
    lam st848.
      lam mtx4.
        p_map
          st848
          (lam x1306.
             tmOpaque (let b17 = matMakeUninit (externalExtArrKind x1306.arr) x1306.n x1306.m
              in
              let #var"17" = matTranposeNoAlloc x1306 b17 in
              b17))
          mtx4
  in
  let anon5 =
    lam st843.
      lam mtx121.
        lam mtx241.
          lam x1293.
            match
              p_map
                st843
                (lam x1294.
                   lam x1295.
                     match x1294 with {arr = #var"X35"}
                     in
                     externalExtArrSet #var"X35" x1293 x1295)
                mtx241
            with
              (st844, x1296)
            in
            match
              p_map st844 (lam x1297.
                   x1297.arr) mtx121
            with
              (st845, x1298)
            in
            match extArrGetExn st845 x1298 x1293 with (st846, x1299)
            in
            match
              p_map
                st846
                (lam x1300.
                   match gtf x1300 0. with true
                   then
                     x1300
                   else
                     0.)
                x1299
            with
              (st847, x1305)
            in
            p_apply st847 x1296 x1305
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
    lam st816.
      lam mtx92.
        lam mtx213.
          lam x1241.
            lam x1242.
              match
                p_map
                  st816
                  (lam x1243.
                     lam x1244.
                       lam x1245.
                         match x1243 with {arr = #var"X33"}
                         in
                         externalExtArrSet #var"X33" x1244 x1245)
                  mtx213
              with
                (st817, x1246)
              in
              match
                p_map
                  st817
                  (lam x1247.
                     match x1247 with {n = #var"X34"}
                     in
                     addi (muli x1241 #var"X34") x1242)
                  mtx213
              with
                (st818, x1248)
              in
              match p_apply st818 x1246 x1248 with (st819, x1249)
              in
              match matGetExn1 st819 mtx92 x1241 x1242 with (st820, x1250)
              in
              match
                p_map
                  st820
                  (lam x1251.
                     lam x1252.
                       divf x1251 x1252)
                  x1250
              with
                (st821, x1253)
              in
              match
                p_map st821 (lam x1254.
                     x1254.m) mtx92
              with
                (st822, x1255)
              in
              match
                p_map st822 (lam x1256.
                     subi x1256 1) x1255
              with
                (st823, x1257)
              in
              match
                p_map
                  st823
                  (lam x1258.
                     match geqi x1258 0 with true
                     then
                       rec3 1. (subi x1258 1) (cons (anon 1. x1258) "")
                     else
                       "")
                  x1257
              with
                (st824, x1259)
              in
              match extArrOfSeq st824 extArrKindFloat64 x1259 with (st825, a62)
              in
              match
                p_map st825 (lam x1260.
                     x1260.m) mtx92
              with
                (st826, x1261)
              in
              match
                p_map
                  st826
                  (lam x1262.
                     lam x1263.
                       lam st827.
                         let x1264 =
                           match eqi (muli x1262 1) x1263 with true
                           then
                             { arr = a62, n = 1, m = x1262 }
                           else
                             let x1269 = error "matFromArrExn: dimensions mismatch" in
                             match x1269 with {arr = x1270}
                             in
                             match x1269 with {n = x1271}
                             in
                             match x1269 with {m = x1272}
                             in
                             { arr = p_pure x1270, n = x1271, m = x1272 }
                         in
                         match x1264 with {arr = x1265}
                         in
                         p_map
                           st827
                           (lam x1266.
                              match x1264 with {n = x1267}
                              in
                              match x1264 with {m = x1268}
                              in
                              { arr = x1266, n = x1267, m = x1268 })
                           x1265)
                  x1261
              with
                (st828, x1273)
              in
              match
                p_map
                  st828
                  (lam x1274.
                     externalExtArrLength x1274)
                  a62
              with
                (st829, x1275)
              in
              match
                p_subApply st829 hrmStoreSubmodel (hrmInit {}) x1273 x1275
              with
                (st830, x1276)
              in
              match p_join st830 x1276 with (st831, x1277)
              in
              match matMulExn st831 mtx92 x1277 with (st832, x1278)
              in
              match
                p_map
                  st832
                  (lam x1279.
                     match x1279 with {arr = field24, n = field25, m = field26}
                     in
                     field24)
                  x1278
              with
                (st833, a69)
              in
              match
                p_map
                  st833
                  (lam x1280.
                     externalExtArrLength x1280)
                  a69
              with
                (st834, x1281)
              in
              match
                p_map st834 (lam x1282.
                     subi x1282 1) x1281
              with
                (st835, x1283)
              in
              match
                p_bind
                  st835
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st836.
                     lam x1284.
                       match
                         match geqi x1284 0 with true
                         then
                           match
                             p_map
                               st836
                               (lam x1285.
                                  externalExtArrGet x1285 x1284)
                               a69
                           with
                             (st837, x1286)
                           in
                           rec31 st837 a69 (subi x1284 1) (cons x1286 "")
                         else
                           (st836, "")
                       with
                         (st838, x1287)
                       in
                       p_traverseSeq
                         st838
                         (lam st839.
                            lam x1288.
                              (st839, x1288))
                         x1287)
                  x1283
              with
                (st840, x1289)
              in
              match
                p_map
                  st840 (lam x1290.
                     get x1290 x1241) x1289
              with
                (st841, x1291)
              in
              match p_apply st841 x1253 x1291 with (st842, x1292)
              in
              p_apply st842 x1249 x1292
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
    lam st812.
      lam mtx91.
        lam mtx212.
          lam x1237.
            match
              p_map st812 (lam x1238.
                   x1238.n) mtx91
            with
              (st813, x1239)
            in
            p_subMap
              st813
              hrmStoreSubmodel
              (hrmInit {})
              (lam x1240.
                 lam st814.
                   match geqi 0 x1240 with true
                   then
                     (st814, {})
                   else match anon6 st814 mtx91 mtx212 #frozen"x1237" 0 with (st815, #var"6")
                   in
                   rec41 st815 mtx91 mtx212 #frozen"x1237" x1240 (addi 0 1))
              x1239
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
    lam st795.
      lam mtx3.
        match
          p_map
            st795
            (lam x1220.
               lam x1221.
                 match x1220 with {m = #var"X28"}
                 in
                 match eqi #var"X28" x1221 with true
                 then
                   match x1220 with {m = #var"X29"}
                   in
                   match x1220 with {n = #var"X30"}
                   in
                   match x1220 with {arr = #var"X31"}
                   in
                   Right
                     { x1220 with arr = externalMatExp #var"X29" #var"X30" #var"X31" }
                 else
                   Left
                     (NotSquare
                        {}))
            mtx3
        with
          (st796, x1222)
        in
        match
          p_map st796 (lam x1223.
               x1223.n) mtx3
        with
          (st797, x1224)
        in
        match p_apply st797 x1222 x1224 with (st798, x1225)
        in
        match
          p_map
            st798
            (lam x1226.
               match x1226 with Left carried68
               then
                 match carried68 with NotSquare carried69
                 in
                 error "Not square"
               else match x1226 with Right carried70
               in
               carried70)
            x1225
        with
          (st799, mtx12)
        in
        match matCopy st799 mtx12 with (st800, mtx24)
        in
        match
          p_map
            st800
            (lam x1227.
               lam x1228.
                 match x1227 with {m = #var"X32"}
                 in
                 muli #var"X32" x1228)
            mtx12
        with
          (st801, x1229)
        in
        match
          p_map st801 (lam x1230.
               x1230.n) mtx12
        with
          (st802, x1231)
        in
        match p_apply st802 x1229 x1231 with (st803, x1232)
        in
        match
          p_subMap
            st803
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1233.
               lam st804.
                 match geqi 0 x1233 with true
                 then
                   (st804, {})
                 else match anon5 st804 mtx12 mtx24 0 with (st805, #var"4")
                 in
                 rec4 st805 mtx12 mtx24 x1233 (addi 0 1))
            x1232
        with
          (st806, #var"12")
        in
        let mtx9 = mtx24 in
        match matCopy st806 mtx9 with (st807, mtx211)
        in
        match
          p_map st807 (lam x1234.
               x1234.m) mtx9
        with
          (st808, x1235)
        in
        match
          p_subMap
            st808
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1236.
               lam st809.
                 match geqi 0 x1236 with true
                 then
                   (st809, {})
                 else match anon7 st809 mtx9 mtx211 0 with (st810, #var"5")
                 in
                 rec42 st810 mtx9 mtx211 x1236 (addi 0 1))
            x1235
        with
          (st811, #var"11")
        in
        (st811, mtx211)
  in
  let mtxMul =
    lam st794.
      lam a33.
        lam b5.
          matMulExn st794 a33 b5
  in
  let eitherEither =
    lam st793.
      lam e31.
        p_map
          st793
          (lam x1219.
             match x1219 with Left carried66
             then
               error (matErrorToString carried66)
             else match x1219 with Right carried67
             in
             carried67)
          e31
  in
  let mtxElemMul =
    lam st780.
      lam a321.
        lam b41.
          match
            p_map
              st780
              (lam x1197.
                 lam x1198.
                   match x1197 with {m = #var"X26"}
                   in
                   eqi #var"X26" x1198)
              a321
          with
            (st781, x1199)
          in
          match
            p_map st781 (lam x1200.
                 x1200.m) b41
          with
            (st782, x1201)
          in
          match p_apply st782 x1199 x1201 with (st783, x1202)
          in
          match
            p_map
              st783
              (lam x1203.
                 lam x1204.
                   match x1203 with {n = #var"X27"}
                   in
                   eqi #var"X27" x1204)
              a321
          with
            (st784, x1205)
          in
          match
            p_map st784 (lam x1206.
                 x1206.n) b41
          with
            (st785, x1207)
          in
          match p_apply st785 x1205 x1207 with (st786, x1208)
          in
          match and1 st786 x1202 x1208 with (st787, x1209)
          in
          match
            p_bind
              st787
              hrmStoreSubmodel
              (hrmInit {})
              (lam st788.
                 lam x1210.
                   match
                     match x1210 with true
                     then
                       match
                         p_map
                           st788
                           (lam x1211.
                              lam x1212.
                                tmOpaque (let c211 = matMakeUninit (externalExtArrKind x1211.arr) x1211.m x1211.n
                                 in
                                 let #var"161" = matElemMulNoAlloc x1211 x1212 c211 in
                                 c211))
                           a321
                       with
                         (st789, x1213)
                       in
                       match p_apply st789 x1213 b41 with (st790, x1214)
                       in
                       (st790, Right
                         x1214)
                     else
                       (st788, Left
                         (DimensionMismatch
                            {}))
                   with
                     (st791, n5)
                   in
                   match n5 with Right x1215
                   then
                     p_map
                       st791
                       (lam x1216.
                          Right
                            x1216)
                       x1215
                   else match n5 with Left x1217
                   in
                   (st791, p_pure (Left
                        x1217)))
              x1209
          with
            (st792, x1218)
          in
          eitherEither st792 x1218
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
      match mtx21 with {m = #var"X22"}
      in
      match mtx21 with {n = #var"X23"}
      in
      match mtx21 with {m = #var"X24"}
      in
      match mtx21 with {n = #var"X25"}
      in
      divf
        (work2 (muli #var"X22" #var"X23") mtx21 0 0.)
        (int2float (muli #var"X24" #var"X25"))
  in
  let mtxMean1 =
    lam st772.
      lam mtx2.
        match mtx2 with {n = #var"X17"}
        in
        match
          p_map
            st772
            (lam x1185.
               match mtx2 with {m = #var"X18"}
               in
               muli #var"X18" x1185)
            #var"X17"
        with
          (st773, x1186)
        in
        match
          p_bind
            st773
            hrmStoreSubmodel
            (hrmInit {})
            (lam st774.
               lam x1187.
                 match lti 0 x1187 with true
                 then
                   match mtx2 with {arr = #var"X19"}
                   in
                   match extArrGetExn st774 #var"X19" 0 with (st775, x1188)
                   in
                   match
                     p_map
                       st775
                       (lam x1189.
                          addf 0. x1189)
                       x1188
                   with
                     (st776, x1190)
                   in
                   work21 st776 x1187 mtx2 (addi 0 1) x1190
                 else
                   (st774, p_pure 0.))
            x1186
        with
          (st777, x1191)
        in
        match
          p_map
            st777
            (lam x1192.
               lam x1193.
                 divf x1192 x1193)
            x1191
        with
          (st778, x1194)
        in
        match mtx2 with {n = #var"X20"}
        in
        match
          p_map
            st778
            (lam x1195.
               match mtx2 with {m = #var"X21"}
               in
               int2float (muli #var"X21" x1195))
            #var"X20"
        with
          (st779, x1196)
        in
        p_apply st779 x1194 x1196
  in
  let anon8 =
    lam x1183.
      lam x1184.
        match eqi (addi x1183 1) (addi x1184 1) with true
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
    lam x1182.
      match
        match geqi x1182 0 with true
        then
          leqi x1182 2
        else
          false
      with
        true
      then
        create1 3 #frozen"x1182"
      else
        rep 3 1.
  in
  let anon10 =
    lam st771.
      lam x1180.
        p_map
          st771
          (lam x1181.
             match
               match geqi x1181 0 with true
               then
                 leqi x1181 2
               else
                 false
             with
               true
             then
               create1 3 x1181
             else
               rep 3 1.)
          x1180
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
    lam st762.
      lam obsRepertoire.
        match rec5 st762 obsRepertoire with (st763, s227)
        in
        match
          match s227 with [ _ ] ++ _
          then
            match
              p_traverseSeq
                st763
                (lam st764.
                   lam x1172.
                     (st764, x1172))
                ""
            with
              (st765, x1173)
            in
            match p_map st765 concat x1173 with (st766, x1174)
            in
            match p_apply st766 x1174 (get s227 0) with (st767, x1175)
            in
            match splitAt s227 1 with {#label"1" = x1176}
            in
            rec23 st767 x1175 x1176
          else match s227 with ""
          in
          p_traverseSeq
            st763
            (lam st768.
               lam x1177.
                 (st768, x1177))
            ""
        with
          (st769, x1178)
        in
        match extArrOfSeq st769 extArrKindFloat64 x1178 with (st770, x1179)
        in
        matFromArrExn st770 (length obsRepertoire) 3 x1179
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
                  -- Export leaf messages (interactions)
                  let ll = (match tree1 with Leaf carried2
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
                            exit 1) in
                  let leafMsg = observationMessage leafInts in
                  let st40 = p_export st40 (hrmStoreNodeMsg ll) (p_pure leafMsg) in
                  -- Done 
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
                -- Export transition kernels
                let getLabel = lam n.
                  match n with MsgLeaf l then l.label
                  else match n with MsgNode n in n.label
                in
                let leftLabel = getLabel left in
                let rightLabel = getLabel right in
                let st51 = p_export st51 (hrmStoreTransKernel rightLabel) rightKernel in 
                let st51 = p_export st51 (hrmStoreTransKernel leftLabel) leftKernel
                -- Done
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
  let anon11 = lam x1171.
      addi x1171 1 in
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
    lam st761.
      lam mtx1.
        lam i101.
          lam x1170.
            mtxGet st761 i101 x1170 mtx1
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
    lam st758.
      lam s72.
        lam x1165.
          match
            p_map
              st758
              (lam x1166.
                 lam x1167.
                   divf x1166 x1167)
              x1165
          with
            (st759, x1168)
          in
          match seqSumReal st759 s72 with (st760, x1169)
          in
          p_apply st760 x1168 x1169
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
    lam st756.
      lam mtx.
        lam i10.
          let i114 = subi (addi (subi 3 1) 1) 1 in
          match
            rec6
              st756
              mtx
              i10
              (match geqi i114 0 with true
               then
                 rec33 (subi i114 1) (cons (anon11 i114) "")
               else
                 "")
          with
            (st757, s71)
          in
          rec7 st757 s71 s71
  in
  let anon14 =
    lam st753.
      lam samplingProb11.
        lam x1162.
          lam x1163.
            match
              hostMsgToProb st753 samplingProb11 (addi x1162 1)
            with
              (st754, param6)
            in
            p_bind
              st754
              hrmStoreSubmodel
              (hrmInit {})
              (lam st755.
                 lam x1164.
                   match
                     match leqi 0 x1164 with true
                     then
                       lti x1164 (length param6)
                     else
                       false
                   with
                     true
                   then
                     log11 st755 (get param6 (subi (addi x1164 1) 1))
                   else
                     (st755, p_pure (log1 0.)))
              x1163
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
    lam st751.
      lam x1491.
        lam samplingProb1.
          match rec13 st751 samplingProb1 0 x1491 with (st752, x1160)
          in
          seqSumReal st752 x1160
  in
  let anon15 =
    lam x1158.
      lam x1159.
        match eqi x1159 2 with true
        then
          addi x1158 1
        else
          x1158
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
    lam st749.
      lam repertoire21.
        match repertoire21 with [ _ ] ++ _
        then
          match
            p_map
              st749
              (lam x1155.
                 match eqi x1155 2 with true
                 then
                   addi 0 1
                 else
                   0)
              (get repertoire21 0)
          with
            (st750, x1156)
          in
          match splitAt repertoire21 1 with {#label"1" = x1157}
          in
          rec28 st750 x1156 x1157
        else match repertoire21 with ""
        in
        (st749, p_pure 0)
  in
  let updateRepertoire =
    lam st731.
      lam currRep81.
        lam event31.
          lam nhosts71.
            match
              p_map
                st731
                (lam x1131.
                   match x1131 with Event1 x1472
                   then
                     x1472.host
                   else
                     let #var"2154" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event31
            with
              (st732, hostIndex42)
            in
            match
              p_traverseSeq
                st732
                (lam st733.
                   lam x1132.
                     (st733, x1132))
                currRep81
            with
              (st734, x1133)
            in
            match
              p_map
                st734
                (lam x1134.
                   subsequence x1134 (subi 1 1))
                x1133
            with
              (st735, x1135)
            in
            match
              p_map
                st735
                (lam x1136.
                   subi x1136 1)
                hostIndex42
            with
              (st736, x1137)
            in
            match p_apply st736 x1135 x1137 with (st737, x1138)
            in
            match
              p_map
                st737
                (lam x1139.
                   match x1139 with Event1 x1462
                   then
                     x1462.toState
                   else
                     let #var"2155" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event31
            with
              (st738, x1140)
            in
            match
              p_traverseSeq
                st738
                (lam st739.
                   lam x1142.
                     (st739, x1142))
                [ x1140 ]
            with
              (st740, x1143)
            in
            match
              p_map
                st740
                (lam x1144.
                   addi x1144 1)
                hostIndex42
            with
              (st741, first1)
            in
            match
              p_traverseSeq
                st741
                (lam st742.
                   lam x1145.
                     (st742, x1145))
                currRep81
            with
              (st743, x1146)
            in
            match p_map st743 subsequence x1146 with (st744, x1147)
            in
            match
              p_map st744 (lam x1148.
                   subi x1148 1) first1
            with
              (st745, x1149)
            in
            match p_apply st745 x1147 x1149 with (st746, x1150)
            in
            match
              p_map
                st746
                (lam x1152.
                   subi (addi nhosts71 1) x1152)
                first1
            with
              (st747, x1153)
            in
            match p_apply st747 x1150 x1153 with (st748, x1154)
            in
            paste02
              st748
              [ x1138,
                x1143,
                x1154 ]
  in
  let updateRepertoire1 =
    lam st717.
      lam currRep8.
        lam event3.
          lam nhosts7.
            match
              p_map
                st717
                (lam x1113.
                   match x1113 with Event1 x1471
                   then
                     x1471.host
                   else
                     let #var"2152" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event3
            with
              (st718, hostIndex41)
            in
            match
              p_map
                st718
                (lam x1114.
                   subsequence x1114 (subi 1 1))
                currRep8
            with
              (st719, x1115)
            in
            match
              p_map
                st719
                (lam x1116.
                   subi x1116 1)
                hostIndex41
            with
              (st720, x1117)
            in
            match p_apply st720 x1115 x1117 with (st721, x1118)
            in
            match
              p_map
                st721
                (lam x1119.
                   match x1119 with Event1 x1461
                   then
                     x1461.toState
                   else
                     let #var"2153" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event3
            with
              (st722, x1120)
            in
            match
              p_traverseSeq
                st722
                (lam st723.
                   lam x1121.
                     (st723, x1121))
                [ x1120 ]
            with
              (st724, x1122)
            in
            match
              p_map
                st724
                (lam x1123.
                   addi x1123 1)
                hostIndex41
            with
              (st725, first)
            in
            match p_map st725 subsequence currRep8 with (st726, x1124)
            in
            match
              p_map st726 (lam x1125.
                   subi x1125 1) first
            with
              (st727, x1126)
            in
            match p_apply st727 x1124 x1126 with (st728, x1127)
            in
            match
              p_map
                st728
                (lam x1128.
                   subi (addi nhosts7 1) x1128)
                first
            with
              (st729, x1129)
            in
            match p_apply st729 x1127 x1129 with (st730, x1130)
            in
            paste02
              st730
              [ x1118,
                x1122,
                x1130 ]
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
                        match event with Event1 x147
                        then
                          x147.host
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
                              (match event with Event1 x146
                               then
                                 x146.toState
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
    lam x1112.
      match eqi x1112 2 with true
      then
        true
      else
        eqi x1112 1
  in
  let anon17 =
    lam st716.
      lam x1110.
        p_map
          st716
          (lam x1111.
             match eqi x1111 2 with true
             then
               true
             else
               eqi x1111 1)
          x1110
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
  let sapply = lam st715.
      lam s102.
        rec9 st715 s102
  in
  let anon18 = lam x1109.
      eqi x1109 2 in
  let anon19 =
    lam st714.
      lam x1107.
        p_map st714 (lam x1108.
             eqi x1108 2) x1107
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
  let sapply1 = lam st713.
      lam s101.
        rec14 st713 s101
  in
  let getGainRate =
    lam st705.
      lam repertoire14.
        lam hostIndex33.
          lam modelParams123.
            let fromState53 = get repertoire14 (subi hostIndex33 1) in
            match
              mtxGet
                st705
                (addi fromState53 1)
                (addi (addi fromState53 1) 1)
                (match
                   match modelParams123 with ModelParams1 x1434
                   then
                     x1434.embeddedQMatrix
                   else
                     let #var"2146" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1424
                 then
                   x1424.mat
                 else
                   let #var"2147" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st706, baseRate13)
            in
            match eqi fromState53 0 with true
            then
              match
                p_map
                  st706
                  (lam x1094.
                     lam x1095.
                       mulf x1094 x1095)
                  baseRate13
              with
                (st707, x1096)
              in
              match
                p_map
                  st707
                  (lam x1097.
                     negf x1097)
                  (match modelParams123 with ModelParams1 x1384
                   then
                     x1384.beta
                   else
                     let #var"2148" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                     in
                     p_pure (exit 1))
              with
                (st708, x1098)
              in
              match
                pow1
                  st708
                  (mtxMean
                     (mtxRowCols
                        (match modelParams123 with ModelParams1 x1394
                         then
                           x1394.hostMetric
                         else
                           let #var"2149" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                           in
                           exit 1)
                        hostIndex33
                        (whichTrue (rec8 repertoire14))))
                  x1098
              with
                (st709, x1099)
              in
              p_apply st709 x1096 x1099
            else match
              p_map
                st706
                (lam x1100.
                   lam x1102.
                     mulf x1100 x1102)
                baseRate13
            with
              (st710, x1103)
            in
            match
              p_map
                st710
                (lam x1104.
                   negf x1104)
                (match modelParams123 with ModelParams1 x1404
                 then
                   x1404.beta
                 else
                   let #var"2150" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                   in
                   p_pure (exit 1))
            with
              (st711, x1105)
            in
            match
              pow1
                st711
                (mtxMean
                   (mtxRowCols
                      (match modelParams123 with ModelParams1 x1414
                       then
                         x1414.hostMetric
                       else
                         let #var"2151" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                         in
                         exit 1)
                      hostIndex33
                      (whichTrue (rec10 repertoire14))))
                x1105
            with
              (st712, x1106)
            in
            p_apply st712 x1103 x1106
  in
  let getGainRate1 =
    lam st686.
      lam repertoire13.
        lam hostIndex32.
          lam modelParams122.
            let fromState52 = get repertoire13 (subi hostIndex32 1) in
            match
              p_map
                st686
                (lam x1063.
                   addi x1063 1)
                fromState52
            with
              (st687, x1064)
            in
            match
              p_map
                st687
                (lam x1065.
                   addi (addi x1065 1) 1)
                fromState52
            with
              (st688, x1066)
            in
            match
              mtxGet2
                st688
                x1064
                x1066
                (match
                   match modelParams122 with ModelParams1 x1433
                   then
                     x1433.embeddedQMatrix
                   else
                     let #var"2140" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1423
                 then
                   x1423.mat
                 else
                   let #var"2141" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st689, baseRate12)
            in
            p_bind
              st689
              hrmStoreSubmodel
              (hrmInit {})
              (lam st690.
                 lam x1067.
                   match eqi x1067 0 with true
                   then
                     match
                       p_map
                         st690
                         (lam x1068.
                            lam x1069.
                              mulf x1068 x1069)
                         baseRate12
                     with
                       (st691, x1070)
                     in
                     match sapply st691 repertoire13 with (st692, x1073)
                     in
                     match whichTrue1 st692 x1073 with (st693, x1074)
                     in
                     match
                       mtxRowCols1
                         st693
                         (match modelParams122 with ModelParams1 x1393
                          then
                            x1393.hostMetric
                          else
                            let #var"2142" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex32
                         x1074
                     with
                       (st694, x1075)
                     in
                     match mtxMean1 st694 x1075 with (st695, x1076)
                     in
                     match
                       p_map
                         st695
                         (lam x1077.
                            negf x1077)
                         (match modelParams122 with ModelParams1 x1383
                          then
                            x1383.beta
                          else
                            let #var"2143" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st696, x1078)
                     in
                     match pow2 st696 x1076 x1078 with (st697, x1079)
                     in
                     p_apply st697 x1070 x1079
                   else match
                     p_map
                       st690
                       (lam x1080.
                          lam x1083.
                            mulf x1080 x1083)
                       baseRate12
                   with
                     (st698, x1084)
                   in
                   match sapply1 st698 repertoire13 with (st699, x1085)
                   in
                   match whichTrue1 st699 x1085 with (st700, x1086)
                   in
                   match
                     mtxRowCols1
                       st700
                       (match modelParams122 with ModelParams1 x1413
                        then
                          x1413.hostMetric
                        else
                          let #var"2144" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex32
                       x1086
                   with
                     (st701, x1087)
                   in
                   match mtxMean1 st701 x1087 with (st702, x1088)
                   in
                   match
                     p_map
                       st702
                       (lam x1089.
                          negf x1089)
                       (match modelParams122 with ModelParams1 x1403
                        then
                          x1403.beta
                        else
                          let #var"2145" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st703, x1090)
                   in
                   match pow2 st703 x1088 x1090 with (st704, x1093)
                   in
                   p_apply st704 x1084 x1093)
              fromState52
  in
  let getGainRate2 =
    lam st662.
      lam repertoire12.
        lam hostIndex31.
          lam modelParams121.
            match
              p_traverseSeq
                st662
                (lam st663.
                   lam x1031.
                     (st663, x1031))
                repertoire12
            with
              (st664, x1032)
            in
            match p_map st664 get x1032 with (st665, x1033)
            in
            match
              p_map
                st665
                (lam x1034.
                   subi x1034 1)
                hostIndex31
            with
              (st666, x1035)
            in
            match p_apply st666 x1033 x1035 with (st667, fromState51)
            in
            match
              p_map
                st667
                (lam x1036.
                   addi x1036 1)
                fromState51
            with
              (st668, x1037)
            in
            match
              p_map
                st668
                (lam x1038.
                   addi (addi x1038 1) 1)
                fromState51
            with
              (st669, x1039)
            in
            match
              mtxGet2
                st669
                x1037
                x1039
                (match
                   match modelParams121 with ModelParams1 x1432
                   then
                     x1432.embeddedQMatrix
                   else
                     let #var"2134" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1422
                 then
                   x1422.mat
                 else
                   let #var"2135" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st670, baseRate11)
            in
            p_bind
              st670
              hrmStoreSubmodel
              (hrmInit {})
              (lam st671.
                 lam x1040.
                   match eqi x1040 0 with true
                   then
                     match
                       p_map
                         st671
                         (lam x1041.
                            lam x1042.
                              mulf x1041 x1042)
                         baseRate11
                     with
                       (st672, x1043)
                     in
                     match sapply st672 repertoire12 with (st673, x1044)
                     in
                     match whichTrue1 st673 x1044 with (st674, x1045)
                     in
                     match
                       mtxRowCols2
                         st674
                         (match modelParams121 with ModelParams1 x1392
                          then
                            x1392.hostMetric
                          else
                            let #var"2136" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex31
                         x1045
                     with
                       (st675, x1046)
                     in
                     match mtxMean1 st675 x1046 with (st676, x1047)
                     in
                     match
                       p_map
                         st676
                         (lam x1048.
                            negf x1048)
                         (match modelParams121 with ModelParams1 x1382
                          then
                            x1382.beta
                          else
                            let #var"2137" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st677, x1049)
                     in
                     match pow2 st677 x1047 x1049 with (st678, x1050)
                     in
                     p_apply st678 x1043 x1050
                   else match
                     p_map
                       st671
                       (lam x1053.
                          lam x1054.
                            mulf x1053 x1054)
                       baseRate11
                   with
                     (st679, x1055)
                   in
                   match sapply1 st679 repertoire12 with (st680, x1056)
                   in
                   match whichTrue1 st680 x1056 with (st681, x1057)
                   in
                   match
                     mtxRowCols2
                       st681
                       (match modelParams121 with ModelParams1 x1412
                        then
                          x1412.hostMetric
                        else
                          let #var"2138" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex31
                       x1057
                   with
                     (st682, x1058)
                   in
                   match mtxMean1 st682 x1058 with (st683, x1059)
                   in
                   match
                     p_map
                       st683
                       (lam x1060.
                          negf x1060)
                       (match modelParams121 with ModelParams1 x1402
                        then
                          x1402.beta
                        else
                          let #var"2139" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st684, x1061)
                   in
                   match pow2 st684 x1059 x1061 with (st685, x1062)
                   in
                   p_apply st685 x1055 x1062)
              fromState51
  in
  let getGainRate3 =
    lam st640.
      lam repertoire11.
        lam hostIndex3.
          lam modelParams12.
            match p_map st640 get repertoire11 with (st641, x997)
            in
            match
              p_map st641 (lam x998.
                   subi x998 1) hostIndex3
            with
              (st642, x999)
            in
            match p_apply st642 x997 x999 with (st643, fromState5)
            in
            match
              p_map
                st643 (lam x1000.
                   addi x1000 1) fromState5
            with
              (st644, x1001)
            in
            match
              p_map
                st644
                (lam x1002.
                   addi (addi x1002 1) 1)
                fromState5
            with
              (st645, x1003)
            in
            match
              mtxGet2
                st645
                x1001
                x1003
                (match
                   match modelParams12 with ModelParams1 x1431
                   then
                     x1431.embeddedQMatrix
                   else
                     let #var"2128" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1421
                 then
                   x1421.mat
                 else
                   let #var"2129" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st646, baseRate1)
            in
            p_bind
              st646
              hrmStoreSubmodel
              (hrmInit {})
              (lam st647.
                 lam x1004.
                   match eqi x1004 0 with true
                   then
                     match
                       p_map
                         st647
                         (lam x1005.
                            lam x1006.
                              mulf x1005 x1006)
                         baseRate1
                     with
                       (st648, x1007)
                     in
                     match
                       p_map
                         st648
                         (lam x1008.
                            match x1008 with [ _,
                                _ ] ++ _
                            then
                              match splitAt x1008 1 with {#label"1" = x1009}
                              in
                              cons (anon16 (get x1008 0)) (rec8 x1009)
                            else match x1008 with [ e19 ]
                            then
                              match splitAt x1008 1 with {#label"1" = x1010}
                              in
                              let slice18 = x1010 in
                              [ anon16 e19 ]
                            else match x1008 with ""
                            in
                            "")
                         repertoire11
                     with
                       (st649, x1011)
                     in
                     match whichTrue2 st649 x1011 with (st650, x1012)
                     in
                     match
                       mtxRowCols2
                         st650
                         (match modelParams12 with ModelParams1 x1391
                          then
                            x1391.hostMetric
                          else
                            let #var"2130" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex3
                         x1012
                     with
                       (st651, x1013)
                     in
                     match mtxMean1 st651 x1013 with (st652, x1014)
                     in
                     match
                       p_map
                         st652
                         (lam x1015.
                            negf x1015)
                         (match modelParams12 with ModelParams1 x1381
                          then
                            x1381.beta
                          else
                            let #var"2131" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st653, x1016)
                     in
                     match pow2 st653 x1014 x1016 with (st654, x1017)
                     in
                     p_apply st654 x1007 x1017
                   else match
                     p_map
                       st647
                       (lam x1018.
                          lam x1019.
                            mulf x1018 x1019)
                       baseRate1
                   with
                     (st655, x1020)
                   in
                   match
                     p_map
                       st655
                       (lam x1021.
                          match x1021 with [ _,
                              _ ] ++ _
                          then
                            match splitAt x1021 1 with {#label"1" = x1022}
                            in
                            cons (anon18 (get x1021 0)) (rec10 x1022)
                          else match x1021 with [ e20 ]
                          then
                            match splitAt x1021 1 with {#label"1" = x1023}
                            in
                            let slice19 = x1023 in
                            [ anon18 e20 ]
                          else match x1021 with ""
                          in
                          "")
                       repertoire11
                   with
                     (st656, x1024)
                   in
                   match whichTrue2 st656 x1024 with (st657, x1025)
                   in
                   match
                     mtxRowCols2
                       st657
                       (match modelParams12 with ModelParams1 x1411
                        then
                          x1411.hostMetric
                        else
                          let #var"2132" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex3
                       x1025
                   with
                     (st658, x1026)
                   in
                   match mtxMean1 st658 x1026 with (st659, x1027)
                   in
                   match
                     p_map
                       st659
                       (lam x1028.
                          negf x1028)
                       (match modelParams12 with ModelParams1 x1401
                        then
                          x1401.beta
                        else
                          let #var"2133" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st660, x1029)
                   in
                   match pow2 st660 x1027 x1029 with (st661, x1030)
                   in
                   p_apply st661 x1020 x1030)
              fromState5
  in
  let getLossRate =
    lam st639.
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
              (st639, p_pure 0.)
            else
              mtxGet
                st639
                (addi fromState33 1)
                (addi (subi fromState33 1) 1)
                (match
                   match modelParams103 with ModelParams1 x1364
                   then
                     x1364.embeddedQMatrix
                   else
                     let #var"2126" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1354
                 then
                   x1354.mat
                 else
                   let #var"2127" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
  in
  let getLossRate1 =
    lam st632.
      lam repertoire2.
        lam hostIndex22.
          lam modelParams102.
            let fromState32 = get repertoire2 (subi hostIndex22 1) in
            match
              p_bind
                st632
                hrmStoreSubmodel
                (hrmInit {})
                (lam st633.
                   lam x988.
                     match eqi x988 2 with true
                     then
                       match count2s st633 repertoire2 with (st634, x989)
                       in
                       p_map
                         st634 (lam x990.
                            eqi x990 1) x989
                     else
                       (st633, p_pure false))
                fromState32
            with
              (st635, x991)
            in
            p_bind
              st635
              hrmStoreSubmodel
              (hrmInit {})
              (lam st636.
                 lam x992.
                   match x992 with true
                   then
                     (st636, p_pure 0.)
                   else match
                     p_map
                       st636
                       (lam x993.
                          addi x993 1)
                       fromState32
                   with
                     (st637, x994)
                   in
                   match
                     p_map
                       st637
                       (lam x995.
                          addi (subi x995 1) 1)
                       fromState32
                   with
                     (st638, x996)
                   in
                   mtxGet2
                     st638
                     x994
                     x996
                     (match
                        match modelParams102 with ModelParams1 x1363
                        then
                          x1363.embeddedQMatrix
                        else
                          let #var"2124" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1353
                      then
                        x1353.mat
                      else
                        let #var"2125" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x991
  in
  let getLossRate2 =
    lam st620.
      lam repertoire1.
        lam hostIndex21.
          lam modelParams101.
            match
              p_traverseSeq
                st620
                (lam st621.
                   lam x974.
                     (st621, x974))
                repertoire1
            with
              (st622, x975)
            in
            match p_map st622 get x975 with (st623, x976)
            in
            match
              p_map
                st623 (lam x977.
                   subi x977 1) hostIndex21
            with
              (st624, x978)
            in
            match p_apply st624 x976 x978 with (st625, fromState31)
            in
            match
              p_bind
                st625
                hrmStoreSubmodel
                (hrmInit {})
                (lam st626.
                   lam x979.
                     match eqi x979 2 with true
                     then
                       match count2s st626 repertoire1 with (st627, x980)
                       in
                       p_map
                         st627 (lam x981.
                            eqi x981 1) x980
                     else
                       (st626, p_pure false))
                fromState31
            with
              (st628, x982)
            in
            p_bind
              st628
              hrmStoreSubmodel
              (hrmInit {})
              (lam st629.
                 lam x983.
                   match x983 with true
                   then
                     (st629, p_pure 0.)
                   else match
                     p_map
                       st629
                       (lam x984.
                          addi x984 1)
                       fromState31
                   with
                     (st630, x985)
                   in
                   match
                     p_map
                       st630
                       (lam x986.
                          addi (subi x986 1) 1)
                       fromState31
                   with
                     (st631, x987)
                   in
                   mtxGet2
                     st631
                     x985
                     x987
                     (match
                        match modelParams101 with ModelParams1 x1362
                        then
                          x1362.embeddedQMatrix
                        else
                          let #var"2122" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1352
                      then
                        x1352.mat
                      else
                        let #var"2123" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x982
  in
  let getLossRate3 =
    lam st610.
      lam repertoire.
        lam hostIndex2.
          lam modelParams10.
            match p_map st610 get repertoire with (st611, x960)
            in
            match
              p_map st611 (lam x961.
                   subi x961 1) hostIndex2
            with
              (st612, x962)
            in
            match p_apply st612 x960 x962 with (st613, fromState3)
            in
            match
              p_bind
                st613
                hrmStoreSubmodel
                (hrmInit {})
                (lam st614.
                   lam x963.
                     match eqi x963 2 with true
                     then
                       match
                         p_map
                           st614
                           (lam x964.
                              match x964 with [ _ ] ++ _
                              then
                                match splitAt x964 1 with {#label"1" = x965}
                                in
                                rec27 (anon15 0 (get x964 0)) x965
                              else match x964 with ""
                              in
                              0)
                           repertoire
                       with
                         (st615, x966)
                       in
                       p_map
                         st615 (lam x967.
                            eqi x967 1) x966
                     else
                       (st614, p_pure false))
                fromState3
            with
              (st616, x968)
            in
            p_bind
              st616
              hrmStoreSubmodel
              (hrmInit {})
              (lam st617.
                 lam x969.
                   match x969 with true
                   then
                     (st617, p_pure 0.)
                   else match
                     p_map
                       st617
                       (lam x970.
                          addi x970 1)
                       fromState3
                   with
                     (st618, x971)
                   in
                   match
                     p_map
                       st618
                       (lam x972.
                          addi (subi x972 1) 1)
                       fromState3
                   with
                     (st619, x973)
                   in
                   mtxGet2
                     st619
                     x971
                     x973
                     (match
                        match modelParams10 with ModelParams1 x1361
                        then
                          x1361.embeddedQMatrix
                        else
                          let #var"2120" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1351
                      then
                        x1351.mat
                      else
                        let #var"2121" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x968
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
  let anon20 = lam x959.
      addi x959 1 in
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
  let anon21 = lam x958.
      addi x958 1 in
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
    lam st600.
      lam currRep51.
        lam modelParams81.
          lam nhosts61.
            let s225 = create11 (addi (subi nhosts61 1) 1) in
            match
              match s225 with [ _ ] ++ _
              then
                let x939 = get s225 0 in
                match
                  p_bind
                    st600
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st601.
                       lam x940.
                         match eqi x940 2 with true
                         then
                           (st601, p_pure 0.)
                         else match getGainRate1 st601 currRep51 x939 modelParams81 with (st602, x942)
                         in
                         p_map
                           st602
                           (lam x943.
                              addf 0. x943)
                           x942)
                    (get currRep51 (subi x939 1))
                with
                  (st603, x944)
                in
                match splitAt s225 1 with {#label"1" = x945}
                in
                rec29 st603 currRep51 modelParams81 x944 x945
              else match s225 with ""
              in
              (st600, p_pure 0.)
            with
              (st604, x946)
            in
            match
              p_map
                st604
                (lam x947.
                   lam x948.
                     addf x947 x948)
                x946
            with
              (st605, x949)
            in
            let s226 = create12 (addi (subi nhosts61 1) 1) in
            match
              match s226 with [ _ ] ++ _
              then
                let x950 = get s226 0 in
                match
                  p_bind
                    st605
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st606.
                       lam x952.
                         match eqi x952 0 with true
                         then
                           (st606, p_pure 0.)
                         else match getLossRate1 st606 currRep51 x950 modelParams81 with (st607, x953)
                         in
                         p_map
                           st607
                           (lam x954.
                              addf 0. x954)
                           x953)
                    (get currRep51 (subi x950 1))
                with
                  (st608, x955)
                in
                match splitAt s226 1 with {#label"1" = x956}
                in
                rec211 st608 currRep51 modelParams81 x955 x956
              else match s226 with ""
              in
              (st605, p_pure 0.)
            with
              (st609, x957)
            in
            p_apply st609 x949 x957
  in
  let getTotalRate1 =
    lam st590.
      lam currRep5.
        lam modelParams8.
          lam nhosts6.
            let s223 = create11 (addi (subi nhosts6 1) 1) in
            match
              match s223 with [ _ ] ++ _
              then
                let x922 = get s223 0 in
                match
                  p_bind
                    st590
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st591.
                       lam x923.
                         match eqi (get x923 (subi x922 1)) 2 with true
                         then
                           (st591, p_pure 0.)
                         else match getGainRate st591 x923 x922 modelParams8 with (st592, x924)
                         in
                         p_map
                           st592
                           (lam x925.
                              addf 0. x925)
                           x924)
                    currRep5
                with
                  (st593, x926)
                in
                match splitAt s223 1 with {#label"1" = x927}
                in
                rec210 st593 currRep5 modelParams8 x926 x927
              else match s223 with ""
              in
              (st590, p_pure 0.)
            with
              (st594, x928)
            in
            match
              p_map
                st594
                (lam x929.
                   lam x930.
                     addf x929 x930)
                x928
            with
              (st595, x931)
            in
            let s224 = create12 (addi (subi nhosts6 1) 1) in
            match
              match s224 with [ _ ] ++ _
              then
                let x932 = get s224 0 in
                match
                  p_bind
                    st595
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st596.
                       lam x933.
                         match eqi (get x933 (subi x932 1)) 0 with true
                         then
                           (st596, p_pure 0.)
                         else match getLossRate st596 x933 x932 modelParams8 with (st597, x934)
                         in
                         p_map
                           st597
                           (lam x935.
                              addf 0. x935)
                           x934)
                    currRep5
                with
                  (st598, x936)
                in
                match splitAt s224 1 with {#label"1" = x937}
                in
                rec212 st598 currRep5 modelParams8 x936 x937
              else match s224 with ""
              in
              (st595, p_pure 0.)
            with
              (st599, x938)
            in
            p_apply st599 x931 x938
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
                                 match x135 with Event1 x1331
                                 then
                                   x1331.host
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
                                         (match x136 with Event1 x1311
                                          then
                                            x1311.fromState
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
                                 match x139 with Event1 x1321
                                 then
                                   x1321.toState
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
                            (st116, x141)
                          in
                          match p_join st116 x141 with (st117, x142)
                          in
                          match
                            p_map
                              st117
                              (lam x143.
                                 lam x144.
                                   divf x143 x144)
                              x142
                          with
                            (st118, x145)
                          in
                          match p_apply st118 x145 totalLeavingRate1 with (st119, x148)
                          in
                          match log11 st119 x148 with (st120, x149)
                          in
                          match
                            p_map
                              st120
                              (lam x150.
                                 lam x151.
                                   lam x152.
                                     addf (subf x150 x151) x152)
                              x149
                          with
                            (st121, x153)
                          in
                          match
                            p_map
                              st121
                              (lam x154.
                                 lam x155.
                                   lam x156.
                                     mulf (subf x154 x155) x156)
                              currAge
                          with
                            (st122, x157)
                          in
                          match p_apply st122 x157 newAge with (st123, x158)
                          in
                          match p_apply st123 x158 totalLeavingRate1 with (st124, x159)
                          in
                          match p_apply st124 x153 x159 with (st125, x160)
                          in
                          match
                            updateRepertoire1 st125 currRep3 nextEvent nhosts5
                          with
                            (st126, x161)
                          in
                          match
                            fullModelWeight
                              st126
                              (addi nextIndex 1)
                              x161
                              finalRep
                              newAge
                              finalAge
                              eventSeq3
                              nEvents3
                              nhosts5
                              modelParams
                          with
                            (st127, x162)
                          in
                          p_apply st127 x160 x162
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
                                (lam x163.
                                   lam x164.
                                     mulf (negf (subf x163 finalAge1)) x164)
                                currAge1
                            with
                              (st129, x165)
                            in
                            match
                              getTotalRate1 st129 currRep31 modelParams1 nhosts51
                            with
                              (st130, x166)
                            in
                            p_apply st130 x165 x166
                          else match
                            p_map
                              st128
                              (lam x167.
                                 get x167 (subi nextIndex1 1))
                              eventSeq31
                          with
                            (st131, nextEvent1)
                          in
                          match
                            p_map
                              st131
                              (lam x168.
                                 match x168 with Event1 x312
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
                              (lam x169.
                                 match x169 with Event1 x1332
                                 then
                                   x1332.host
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
                              (lam x170.
                                 lam x171.
                                   lam st135.
                                     match
                                       gti
                                         (match x170 with Event1 x1312
                                          then
                                            x1312.fromState
                                          else
                                            let #var"224" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x171
                                     with
                                       true
                                     then
                                       getLossRate3 st135 currRep31 hostIndex11 modelParams1
                                     else
                                       getGainRate3 st135 currRep31 hostIndex11 modelParams1)
                              nextEvent1
                          with
                            (st136, x172)
                          in
                          match
                            p_map
                              st136
                              (lam x173.
                                 match x173 with Event1 x1322
                                 then
                                   x1322.toState
                                 else
                                   let #var"225" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st137, x174)
                          in
                          match
                            p_subApply st137 hrmStoreSubmodel (hrmInit {}) x172 x174
                          with
                            (st138, x175)
                          in
                          match p_join st138 x175 with (st139, x176)
                          in
                          match
                            p_map
                              st139
                              (lam x177.
                                 lam x178.
                                   divf x177 x178)
                              x176
                          with
                            (st140, x179)
                          in
                          match p_apply st140 x179 totalLeavingRate11 with (st141, x180)
                          in
                          match log11 st141 x180 with (st142, x181)
                          in
                          match
                            p_map
                              st142
                              (lam x182.
                                 lam x183.
                                   lam x184.
                                     addf (subf x182 x183) x184)
                              x181
                          with
                            (st143, x185)
                          in
                          match
                            p_map
                              st143
                              (lam x186.
                                 lam x187.
                                   lam x188.
                                     mulf (subf x186 x187) x188)
                              currAge1
                          with
                            (st144, x189)
                          in
                          match p_apply st144 x189 newAge1 with (st145, x190)
                          in
                          match p_apply st145 x190 totalLeavingRate11 with (st146, x191)
                          in
                          match p_apply st146 x185 x191 with (st147, x192)
                          in
                          match
                            updateRepertoire1 st147 currRep31 nextEvent1 nhosts51
                          with
                            (st148, x193)
                          in
                          match
                            fullModelWeight1
                              st148
                              (addi nextIndex1 1)
                              x193
                              finalRep1
                              newAge1
                              finalAge1
                              eventSeq31
                              nEvents31
                              nhosts51
                              modelParams1
                          with
                            (st149, x194)
                          in
                          p_apply st149 x192 x194
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
                      match length13 st150 eventSeq4 with (st151, x195)
                      in
                      p_bind
                        st151
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st152.
                           lam x196.
                             match gti nextIndex11 x196 with true
                             then
                               match
                                 p_traverseSeq
                                   st152
                                   (lam st153.
                                      lam x197.
                                        (st153, x197))
                                   (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x321
                                    then
                                      x321.totalRates
                                    else
                                      let #var"226" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x198.
                                           p_pure x198)
                                        (exit 1))
                               with
                                 (st154, x199)
                               in
                               match
                                 p_map
                                   st154
                                   (lam x200.
                                      lam x201.
                                        mulf (negf (subf currAge11 finalAge11)) (get x200 x201))
                                   x199
                               with
                                 (st155, x202)
                               in
                               match
                                 p_map
                                   st155
                                   (lam x203.
                                      subi (addi x203 1) 1)
                                   currState
                               with
                                 (st156, x204)
                               in
                               p_apply st156 x202 x204
                             else match
                               p_map
                                 st152
                                 (lam x205.
                                    get x205 (subi nextIndex11 1))
                                 eventSeq4
                             with
                               (st157, nextEvent11)
                             in
                             match
                               p_map
                                 st157
                                 (lam x206.
                                    match x206 with Event1 x361
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
                                 (lam x207.
                                    match x207 with Event1 x351
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
                                    lam x208.
                                      p_traverseSeq
                                        st160
                                        (lam st161.
                                           lam x209.
                                             (st161, x209))
                                        x208)
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x331
                                  then
                                    x331.transitionProbs
                                  else
                                    let #var"229" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x210.
                                         map
                                           (lam x211.
                                              p_pure x211)
                                           x210)
                                      (exit 1))
                             with
                               (st162, x212)
                             in
                             match
                               p_map
                                 st162
                                 (lam x213.
                                    lam x214.
                                      get (get x213 x214))
                                 x212
                             with
                               (st163, x215)
                             in
                             match
                               p_map
                                 st163
                                 (lam x216.
                                    subi (addi x216 1) 1)
                                 currState
                             with
                               (st164, x217)
                             in
                             match p_apply st164 x215 x217 with (st165, x218)
                             in
                             match
                               p_map
                                 st165
                                 (lam x219.
                                    subi (addi x219 1) 1)
                                 nextState
                             with
                               (st166, x220)
                             in
                             match p_apply st166 x218 x220 with (st167, x222)
                             in
                             match log11 st167 x222 with (st168, x223)
                             in
                             match
                               p_map
                                 st168
                                 (lam x224.
                                    lam x225.
                                      lam x226.
                                        addf (subf x224 x225) x226)
                                 x223
                             with
                               (st169, x227)
                             in
                             match
                               p_map
                                 st169
                                 (lam x228.
                                    lam x229.
                                      mulf (subf currAge11 x228) x229)
                                 nextAge
                             with
                               (st170, x230)
                             in
                             match
                               p_traverseSeq
                                 st170
                                 (lam st171.
                                    lam x232.
                                      (st171, x232))
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x341
                                  then
                                    x341.totalRates
                                  else
                                    let #var"230" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x233.
                                         p_pure x233)
                                      (exit 1))
                             with
                               (st172, x234)
                             in
                             match p_map st172 get x234 with (st173, x235)
                             in
                             match
                               p_map
                                 st173
                                 (lam x236.
                                    subi (addi x236 1) 1)
                                 currState
                             with
                               (st174, x237)
                             in
                             match p_apply st174 x235 x237 with (st175, x238)
                             in
                             match p_apply st175 x230 x238 with (st176, x239)
                             in
                             match p_apply st176 x227 x239 with (st177, x240)
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
                               (st178, x241)
                             in
                             p_apply st178 x240 x241)
                        x195
    let hostIndepLikelihood1 =
      lam st179.
        lam nextIndex12.
          lam currState1.
            lam finalState1.
              lam currAge12.
                lam finalAge12.
                  lam eventSeq41.
                    lam embeddedQMatrix1.
                      match length13 st179 eventSeq41 with (st180, x242)
                      in
                      p_bind
                        st180
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st181.
                           lam x243.
                             match gti nextIndex12 x243 with true
                             then
                               match
                                 p_map
                                   st181
                                   (lam x244.
                                      lam x245.
                                        mulf (negf (subf x244 finalAge12)) x245)
                                   currAge12
                               with
                                 (st182, x246)
                               in
                               match
                                 p_traverseSeq
                                   st182
                                   (lam st183.
                                      lam x247.
                                        (st183, x247))
                                   (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x322
                                    then
                                      x322.totalRates
                                    else
                                      let #var"231" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x248.
                                           p_pure x248)
                                        (exit 1))
                               with
                                 (st184, x249)
                               in
                               match p_map st184 get x249 with (st185, x250)
                               in
                               match
                                 p_map
                                   st185
                                   (lam x251.
                                      subi (addi x251 1) 1)
                                   currState1
                               with
                                 (st186, x252)
                               in
                               match p_apply st186 x250 x252 with (st187, x253)
                               in
                               p_apply st187 x246 x253
                             else match
                               p_map
                                 st181
                                 (lam x254.
                                    get x254 (subi nextIndex12 1))
                                 eventSeq41
                             with
                               (st188, nextEvent12)
                             in
                             match
                               p_map
                                 st188
                                 (lam x255.
                                    match x255 with Event1 x362
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
                                 (lam x256.
                                    match x256 with Event1 x352
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
                                    lam x257.
                                      p_traverseSeq
                                        st191
                                        (lam st192.
                                           lam x258.
                                             (st192, x258))
                                        x257)
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x332
                                  then
                                    x332.transitionProbs
                                  else
                                    let #var"234" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x259.
                                         map
                                           (lam x260.
                                              p_pure x260)
                                           x259)
                                      (exit 1))
                             with
                               (st193, x261)
                             in
                             match
                               p_map
                                 st193
                                 (lam x262.
                                    lam x263.
                                      get (get x262 x263))
                                 x261
                             with
                               (st194, x264)
                             in
                             match
                               p_map
                                 st194
                                 (lam x265.
                                    subi (addi x265 1) 1)
                                 currState1
                             with
                               (st195, x266)
                             in
                             match p_apply st195 x264 x266 with (st196, x267)
                             in
                             match
                               p_map
                                 st196
                                 (lam x268.
                                    subi (addi x268 1) 1)
                                 nextState1
                             with
                               (st197, x269)
                             in
                             match p_apply st197 x267 x269 with (st198, x270)
                             in
                             match log11 st198 x270 with (st199, x271)
                             in
                             match
                               p_map
                                 st199
                                 (lam x272.
                                    lam x273.
                                      lam x274.
                                        addf (subf x272 x273) x274)
                                 x271
                             with
                               (st200, x275)
                             in
                             match
                               p_map
                                 st200
                                 (lam x276.
                                    lam x277.
                                      lam x278.
                                        mulf (subf x276 x277) x278)
                                 currAge12
                             with
                               (st201, x279)
                             in
                             match p_apply st201 x279 nextAge1 with (st202, x280)
                             in
                             match
                               p_traverseSeq
                                 st202
                                 (lam st203.
                                    lam x281.
                                      (st203, x281))
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x342
                                  then
                                    x342.totalRates
                                  else
                                    let #var"235" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x282.
                                         p_pure x282)
                                      (exit 1))
                             with
                               (st204, x283)
                             in
                             match p_map st204 get x283 with (st205, x284)
                             in
                             match
                               p_map
                                 st205
                                 (lam x285.
                                    subi (addi x285 1) 1)
                                 currState1
                             with
                               (st206, x286)
                             in
                             match p_apply st206 x284 x286 with (st207, x287)
                             in
                             match p_apply st207 x280 x287 with (st208, x288)
                             in
                             match p_apply st208 x275 x288 with (st209, x289)
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
                               (st210, x290)
                             in
                             p_apply st210 x289 x290)
                        x242
    let hostIndepLikelihood2 =
      lam st211.
        lam nextIndex13.
          lam currState2.
            lam finalState2.
              lam currAge13.
                lam finalAge13.
                  lam eventSeq42.
                    lam embeddedQMatrix2.
                      match length13 st211 eventSeq42 with (st212, x291)
                      in
                      p_bind
                        st212
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st213.
                           lam x292.
                             match gti nextIndex13 x292 with true
                             then
                               match
                                 p_traverseSeq
                                   st213
                                   (lam st214.
                                      lam x293.
                                        (st214, x293))
                                   (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x323
                                    then
                                      x323.totalRates
                                    else
                                      let #var"236" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x294.
                                           p_pure x294)
                                        (exit 1))
                               with
                                 (st215, x295)
                               in
                               match
                                 p_map
                                   st215
                                   (lam x296.
                                      lam x297.
                                        mulf (negf (subf currAge13 finalAge13)) (get x296 x297))
                                   x295
                               with
                                 (st216, x298)
                               in
                               match
                                 p_map
                                   st216
                                   (lam x299.
                                      subi (addi x299 1) 1)
                                   currState2
                               with
                                 (st217, x300)
                               in
                               p_apply st217 x298 x300
                             else match
                               p_map
                                 st213
                                 (lam x303.
                                    get x303 (subi nextIndex13 1))
                                 eventSeq42
                             with
                               (st218, nextEvent13)
                             in
                             match
                               p_map
                                 st218
                                 (lam x304.
                                    match x304 with Event1 x363
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
                                 (lam x305.
                                    match x305 with Event1 x353
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
                                    lam x306.
                                      p_traverseSeq
                                        st221
                                        (lam st222.
                                           lam x307.
                                             (st222, x307))
                                        x306)
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x333
                                  then
                                    x333.transitionProbs
                                  else
                                    let #var"239" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x308.
                                         map
                                           (lam x309.
                                              p_pure x309)
                                           x308)
                                      (exit 1))
                             with
                               (st223, x310)
                             in
                             match
                               p_map
                                 st223
                                 (lam x313.
                                    lam x314.
                                      get (get x313 x314))
                                 x310
                             with
                               (st224, x315)
                             in
                             match
                               p_map
                                 st224
                                 (lam x316.
                                    subi (addi x316 1) 1)
                                 currState2
                             with
                               (st225, x317)
                             in
                             match p_apply st225 x315 x317 with (st226, x318)
                             in
                             match
                               p_map
                                 st226
                                 (lam x319.
                                    subi (addi x319 1) 1)
                                 nextState2
                             with
                               (st227, x320)
                             in
                             match p_apply st227 x318 x320 with (st228, x324)
                             in
                             match log11 st228 x324 with (st229, x325)
                             in
                             match
                               p_map
                                 st229
                                 (lam x326.
                                    lam x327.
                                      lam x328.
                                        addf (subf x326 x327) x328)
                                 x325
                             with
                               (st230, x329)
                             in
                             match
                               p_map
                                 st230
                                 (lam x330.
                                    lam x334.
                                      mulf (subf currAge13 x330) x334)
                                 nextAge2
                             with
                               (st231, x335)
                             in
                             match
                               p_traverseSeq
                                 st231
                                 (lam st232.
                                    lam x336.
                                      (st232, x336))
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x343
                                  then
                                    x343.totalRates
                                  else
                                    let #var"240" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x337.
                                         p_pure x337)
                                      (exit 1))
                             with
                               (st233, x338)
                             in
                             match p_map st233 get x338 with (st234, x339)
                             in
                             match
                               p_map
                                 st234
                                 (lam x340.
                                    subi (addi x340 1) 1)
                                 currState2
                             with
                               (st235, x344)
                             in
                             match p_apply st235 x339 x344 with (st236, x345)
                             in
                             match p_apply st236 x335 x345 with (st237, x346)
                             in
                             match p_apply st237 x329 x346 with (st238, x347)
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
                               (st239, x348)
                             in
                             p_apply st239 x347 x348)
                        x291
    let hostIndepLikelihood3 =
      lam st240.
        lam nextIndex14.
          lam currState3.
            lam finalState3.
              lam currAge14.
                lam finalAge14.
                  lam eventSeq43.
                    lam embeddedQMatrix3.
                      match length13 st240 eventSeq43 with (st241, x349)
                      in
                      p_bind
                        st241
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st242.
                           lam x350.
                             match gti nextIndex14 x350 with true
                             then
                               match
                                 p_map
                                   st242
                                   (lam x354.
                                      lam x355.
                                        mulf (negf (subf x354 finalAge14)) x355)
                                   currAge14
                               with
                                 (st243, x356)
                               in
                               match
                                 p_traverseSeq
                                   st243
                                   (lam st244.
                                      lam x357.
                                        (st244, x357))
                                   (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3210
                                    then
                                      x3210.totalRates
                                    else
                                      let #var"241" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x358.
                                           p_pure x358)
                                        (exit 1))
                               with
                                 (st245, x359)
                               in
                               match p_map st245 get x359 with (st246, x360)
                               in
                               match
                                 p_map
                                   st246
                                   (lam x364.
                                      subi (addi x364 1) 1)
                                   currState3
                               with
                                 (st247, x365)
                               in
                               match p_apply st247 x360 x365 with (st248, x366)
                               in
                               p_apply st248 x356 x366
                             else match
                               p_map
                                 st242
                                 (lam x367.
                                    get x367 (subi nextIndex14 1))
                                 eventSeq43
                             with
                               (st249, nextEvent14)
                             in
                             match
                               p_map
                                 st249
                                 (lam x368.
                                    match x368 with Event1 x369
                                    then
                                      x369.toState
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
                                 (lam x370.
                                    match x370 with Event1 x3510
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
                                    lam x371.
                                      p_traverseSeq
                                        st252
                                        (lam st253.
                                           lam x372.
                                             (st253, x372))
                                        x371)
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3310
                                  then
                                    x3310.transitionProbs
                                  else
                                    let #var"244" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x373.
                                         map
                                           (lam x374.
                                              p_pure x374)
                                           x373)
                                      (exit 1))
                             with
                               (st254, x375)
                             in
                             match
                               p_map
                                 st254
                                 (lam x376.
                                    lam x377.
                                      get (get x376 x377))
                                 x375
                             with
                               (st255, x378)
                             in
                             match
                               p_map
                                 st255
                                 (lam x379.
                                    subi (addi x379 1) 1)
                                 currState3
                             with
                               (st256, x380)
                             in
                             match p_apply st256 x378 x380 with (st257, x381)
                             in
                             match
                               p_map
                                 st257
                                 (lam x382.
                                    subi (addi x382 1) 1)
                                 nextState3
                             with
                               (st258, x383)
                             in
                             match p_apply st258 x381 x383 with (st259, x384)
                             in
                             match log11 st259 x384 with (st260, x385)
                             in
                             match
                               p_map
                                 st260
                                 (lam x386.
                                    lam x387.
                                      lam x388.
                                        addf (subf x386 x387) x388)
                                 x385
                             with
                               (st261, x389)
                             in
                             match
                               p_map
                                 st261
                                 (lam x390.
                                    lam x391.
                                      lam x392.
                                        mulf (subf x390 x391) x392)
                                 currAge14
                             with
                               (st262, x393)
                             in
                             match p_apply st262 x393 nextAge3 with (st263, x394)
                             in
                             match
                               p_traverseSeq
                                 st263
                                 (lam st264.
                                    lam x395.
                                      (st264, x395))
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3410
                                  then
                                    x3410.totalRates
                                  else
                                    let #var"245" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x396.
                                         p_pure x396)
                                      (exit 1))
                             with
                               (st265, x397)
                             in
                             match p_map st265 get x397 with (st266, x398)
                             in
                             match
                               p_map
                                 st266
                                 (lam x399.
                                    subi (addi x399 1) 1)
                                 currState3
                             with
                               (st267, x400)
                             in
                             match p_apply st267 x398 x400 with (st268, x401)
                             in
                             match p_apply st268 x394 x401 with (st269, x402)
                             in
                             match p_apply st269 x389 x402 with (st270, x403)
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
                               (st271, x404)
                             in
                             p_apply st271 x403 x404)
                        x349
  in
  let anon22 = lam x921.
      addi x921 1 in
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
    lam st585.
      lam msg1.
        lam nodeLabel51.
          lam x915.
            match
              hostMsgToProb st585 msg1 (addi x915 (muli nodeLabel51 0))
            with
              (st586, x916)
            in
            match
              p_traverseSeq
                st586
                (lam st587.
                   lam x917.
                     (st587, x917))
                x916
            with
              (st588, x918)
            in
            match
              p_map st588 (lam x919.
                   mkCategorical x919) x918
            with
              (st589, x920)
            in
            p_assume st589 (hrmStoreNode nodeLabel51 x915) x920
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
                match anon23 st272 c33 c34 (get s14 0) with (st273, x405)
                in
                match splitAt s14 1 with {#label"1" = x406}
                in
                match rec15 st273 c33 c34 x406 with (st274, x407)
                in
                (st274, cons x405 x407)
              else match s14 with [ e14 ]
              then
                match splitAt s14 1 with {#label"1" = x408}
                in
                let slice13 = x408 in
                match anon23 st272 c33 c34 e14 with (st275, x409)
                in
                (st275, [ x409 ])
              else match s14 with ""
              in
              (st272, "")
  in
  let suggestNodeRep =
    lam st584.
      lam msg.
        lam nHosts4.
          lam nodeLabel5.
            let i111 = subi (addi (subi nHosts4 1) 1) 1 in
            rec15
              st584
              msg
              nodeLabel5
              (match geqi i111 0 with true
               then
                 rec36 (subi i111 1) (cons (anon22 i111) "")
               else
                 "")
  in
  recursive
    let sampleHostHistoryRec =
      lam st276.
        lam currentState.
          lam finalState11.
            lam currentAge.
              lam finalAge2.
                lam host.
                  lam nodeLabel.
                    lam embeddedQMatrix11.
                      p_bind
                        st276
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st277.
                           lam x410.
                             match
                               match ltf x410 finalAge2 with true
                               then
                                 match
                                   p_map
                                     st277
                                     (lam x411.
                                        eqi x411 finalState11)
                                     currentState
                                 with
                                   (st278, x412)
                                 in
                                 match
                                   p_traverseSeq
                                     st278
                                     (lam st279.
                                        lam x413.
                                          (st279, x413))
                                     ""
                                 with
                                   (st280, x414)
                                 in
                                 (st280, Bridge1
                                   { success = x412, events = x414 })
                               else match
                                 p_traverseSeq
                                   st277
                                   (lam st281.
                                      lam x415.
                                        p_traverseSeq
                                          st281
                                          (lam st282.
                                             lam x416.
                                               (st282, x416))
                                          x415)
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x4010
                                    then
                                      x4010.transitionProbs
                                    else
                                      let #var"246" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 323:16-323:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x417.
                                           map
                                             (lam x418.
                                                p_pure x418)
                                             x417)
                                        (exit 1))
                               with
                                 (st283, x419)
                               in
                               match
                                 p_map
                                   st283
                                   (lam x420.
                                      lam x421.
                                        mkCategorical (get x420 x421))
                                   x419
                               with
                                 (st284, x422)
                               in
                               match
                                 p_map
                                   st284
                                   (lam x423.
                                      subi (addi x423 1) 1)
                                   currentState
                               with
                                 (st285, x424)
                               in
                               match p_apply st285 x422 x424 with (st286, x425)
                               in
                               match p_assume st286 (hrmStoreBranchState nodeLabel host) x425 with (st287, nextState11)
                               in
                               match
                                 p_traverseSeq
                                   st287
                                   (lam st288.
                                      lam x426.
                                        (st288, x426))
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x3910
                                    then
                                      x3910.totalRates
                                    else
                                      let #var"247" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 327:20-327:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x427.
                                           p_pure x427)
                                        (exit 1))
                               with
                                 (st289, x428)
                               in
                               match
                                 p_map
                                   st289
                                   (lam x429.
                                      lam x430.
                                        mkExponential
                                          (addf
                                             (addf (get x429 x430) (mulf (int2float host) 0.))
                                             (mulf (int2float nodeLabel) 0.)))
                                   x428
                               with
                                 (st290, x431)
                               in
                               match
                                 p_map
                                   st290
                                   (lam x432.
                                      subi (addi x432 1) 1)
                                   nextState11
                               with
                                 (st291, x433)
                               in
                               match p_apply st291 x431 x433 with (st292, x434)
                               in
                               match p_assume st292 (hrmStoreBranchTime nodeLabel host) x434 with (st293, x435)
                               in
                               match
                                 p_map
                                   st293
                                   (lam x436.
                                      subf x410 x436)
                                   x435
                               with
                                 (st294, x437)
                               in
                               match
                                 sampleHostHistoryRec
                                   st294
                                   nextState11
                                   finalState11
                                   x437
                                   finalAge2
                                   host
                                   nodeLabel
                                   embeddedQMatrix11
                               with
                                 (st295, restOfHistory)
                               in
                               match
                                 p_map
                                   st295
                                   (lam x438.
                                      match x438 with Bridge1 x3710
                                      then
                                        x3710.success
                                      else
                                        let #var"248" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 345:18-345:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st296, x439)
                               in
                               match
                                 p_map
                                   st296
                                   (lam x440.
                                      lam x441.
                                        cons
                                          (Event1
                                             { host = host, toState = x440, eventTime = x410, fromState = x441 }))
                                   nextState11
                               with
                                 (st297, x442)
                               in
                               match p_apply st297 x442 currentState with (st298, x443)
                               in
                               match
                                 p_map
                                   st298
                                   (lam x444.
                                      match x444 with Bridge1 x3810
                                      then
                                        x3810.events
                                      else
                                        let #var"249" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 343:10-343:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st299, x445)
                               in
                               match p_apply st299 x443 x445 with (st300, x446)
                               in
                               (st300, Bridge1
                                 { success = x439, events = x446 })
                             with
                               (st301, x447)
                             in
                             match x447 with Bridge1 x448
                             in
                             match x448 with {success = x449}
                             in
                             match
                               p_map
                                 st301
                                 (lam x450.
                                    lam x451.
                                      Bridge1
                                        { success = x450, events = x451 })
                                 x449
                             with
                               (st302, x452)
                             in
                             match x448 with {events = x453}
                             in
                             p_apply st302 x452 x453)
                        currentAge
    let sampleHostHistoryRec1 =
      lam st303.
        lam currentState1.
          lam finalState12.
            lam currentAge1.
              lam finalAge21.
                lam host1.
                  lam nodeLabel1.
                    lam embeddedQMatrix12.
                      p_bind
                        st303
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st304.
                           lam x454.
                             match
                               match ltf x454 finalAge21 with true
                               then
                                 match
                                   p_map
                                     st304
                                     (lam x455.
                                        lam x456.
                                          eqi x455 x456)
                                     currentState1
                                 with
                                   (st305, x457)
                                 in
                                 match p_apply st305 x457 finalState12 with (st306, x458)
                                 in
                                 match
                                   p_traverseSeq
                                     st306
                                     (lam st307.
                                        lam x459.
                                          (st307, x459))
                                     ""
                                 with
                                   (st308, x460)
                                 in
                                 (st308, Bridge1
                                   { success = x458, events = x460 })
                               else match
                                 p_traverseSeq
                                   st304
                                   (lam st309.
                                      lam x461.
                                        p_traverseSeq
                                          st309
                                          (lam st310.
                                             lam x462.
                                               (st310, x462))
                                          x461)
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x4011
                                    then
                                      x4011.transitionProbs
                                    else
                                      let #var"250" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 323:16-323:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x463.
                                           map
                                             (lam x464.
                                                p_pure x464)
                                             x463)
                                        (exit 1))
                               with
                                 (st311, x465)
                               in
                               match
                                 p_map
                                   st311
                                   (lam x466.
                                      lam x467.
                                        mkCategorical (get x466 x467))
                                   x465
                               with
                                 (st312, x468)
                               in
                               match
                                 p_map
                                   st312
                                   (lam x469.
                                      subi (addi x469 1) 1)
                                   currentState1
                               with
                                 (st313, x470)
                               in
                               match p_apply st313 x468 x470 with (st314, x471)
                               in
                               match p_assume st314 (hrmStoreBranchState nodeLabel1 host1) x471 with (st315, nextState12)
                               in
                               match
                                 p_traverseSeq
                                   st315
                                   (lam st316.
                                      lam x472.
                                        (st316, x472))
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x3911
                                    then
                                      x3911.totalRates
                                    else
                                      let #var"251" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 327:20-327:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x473.
                                           p_pure x473)
                                        (exit 1))
                               with
                                 (st317, x474)
                               in
                               match
                                 p_map
                                   st317
                                   (lam x475.
                                      lam x476.
                                        mkExponential
                                          (addf
                                             (addf (get x475 x476) (mulf (int2float host1) 0.))
                                             (mulf (int2float nodeLabel1) 0.)))
                                   x474
                               with
                                 (st318, x477)
                               in
                               match
                                 p_map
                                   st318
                                   (lam x478.
                                      subi (addi x478 1) 1)
                                   nextState12
                               with
                                 (st319, x479)
                               in
                               match p_apply st319 x477 x479 with (st320, x480)
                               in
                               match p_assume st320 (hrmStoreBranchTime nodeLabel1 host1) x480 with (st321, x481)
                               in
                               match
                                 p_map
                                   st321
                                   (lam x482.
                                      subf x454 x482)
                                   x481
                               with
                                 (st322, x483)
                               in
                               match
                                 sampleHostHistoryRec1
                                   st322
                                   nextState12
                                   finalState12
                                   x483
                                   finalAge21
                                   host1
                                   nodeLabel1
                                   embeddedQMatrix12
                               with
                                 (st323, restOfHistory1)
                               in
                               match
                                 p_map
                                   st323
                                   (lam x484.
                                      match x484 with Bridge1 x3711
                                      then
                                        x3711.success
                                      else
                                        let #var"252" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 345:18-345:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st324, x485)
                               in
                               match
                                 p_map
                                   st324
                                   (lam x486.
                                      lam x487.
                                        cons
                                          (Event1
                                             { host = host1, toState = x486, eventTime = x454, fromState = x487 }))
                                   nextState12
                               with
                                 (st325, x488)
                               in
                               match p_apply st325 x488 currentState1 with (st326, x489)
                               in
                               match
                                 p_map
                                   st326
                                   (lam x490.
                                      match x490 with Bridge1 x3811
                                      then
                                        x3811.events
                                      else
                                        let #var"253" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 343:10-343:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st327, x491)
                               in
                               match p_apply st327 x489 x491 with (st328, x492)
                               in
                               (st328, Bridge1
                                 { success = x485, events = x492 })
                             with
                               (st329, x493)
                             in
                             match x493 with Bridge1 x494
                             in
                             match x494 with {success = x495}
                             in
                             match
                               p_map
                                 st329
                                 (lam x496.
                                    lam x497.
                                      Bridge1
                                        { success = x496, events = x497 })
                                 x495
                             with
                               (st330, x498)
                             in
                             match x494 with {events = x499}
                             in
                             p_apply st330 x498 x499)
                        currentAge1
  in
  let anon24 = lam x914.
      addi x914 1 in
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
    lam st572.
      lam startRep1.
        lam finalRep12.
          lam startAge1.
            lam finalAge33.
              lam nodeLabel12.
                lam modelParams31.
                  lam x894.
                    let startState1 = get startRep1 (subi x894 1) in
                    let embeddedQMatrix51 =
                      match modelParams31 with ModelParams1 x1052
                      then
                        x1052.embeddedQMatrix
                      else
                        let #var"2119" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 201:4-201:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st572
                        (lam st573.
                           lam x895.
                             (st573, x895))
                        (match embeddedQMatrix51 with EmbeddedMarkovChainMatrix1 x1092
                         then
                           x1092.totalRates
                         else
                           let #var"2116" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 292:18-292:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x896.
                                p_pure x896)
                             (exit 1))
                    with
                      (st574, x897)
                    in
                    match
                      p_map
                        st574
                        (lam x898.
                           lam x899.
                             mkExponential
                               (addf
                                  (addf (get x898 x899) (mulf (int2float x894) 0.))
                                  (mulf (int2float nodeLabel12) 0.)))
                        x897
                    with
                      (st575, x900)
                    in
                    match
                      p_map
                        st575
                        (lam x902.
                           subi (addi x902 1) 1)
                        startState1
                    with
                      (st576, x903)
                    in
                    match p_apply st576 x900 x903 with (st577, x904)
                    in
                    match p_assume st577 (hrmStoreBranchTime nodeLabel12 x894) x904 with (st578, x905)
                    in
                    match
                      p_map
                        st578
                        (lam x906.
                           subf startAge1 x906)
                        x905
                    with
                      (st579, x907)
                    in
                    match
                      sampleHostHistoryRec
                        st579
                        startState1
                        (get finalRep12 (subi x894 1))
                        x907
                        finalAge33
                        x894
                        nodeLabel12
                        embeddedQMatrix51
                    with
                      (st580, bridge1)
                    in
                    match
                      p_map
                        st580
                        (lam x908.
                           match x908 with Bridge1 x1082
                           then
                             x1082.success
                           else
                             let #var"2117" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 304:19-304:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge1
                    with
                      (st581, x909)
                    in
                    match bool2real st581 x909 with (st582, x910)
                    in
                    let st583 =
                      p_weight
                        st582
                        (hrmStoreBridgeSuppWeight nodeLabel12 x894)
                        (lam x913.
                           externalLog
                             (addf
                                (addf x913 (mulf (int2float x894) 0.))
                                (mulf (int2float nodeLabel12) 0.)))
                        x910
                    in
                    let foo51 = {} in
                    p_map
                      st583
                      (lam x912.
                         match x912 with Bridge1 x1072
                         then
                           x1072.events
                         else
                           let #var"2118" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 305:9-305:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge1
  in
  let anon26 =
    lam st560.
      lam startRep.
        lam finalRep11.
          lam startAge.
            lam finalAge32.
              lam nodeLabel11.
                lam modelParams3.
                  lam x874.
                    let startState = get startRep (subi x874 1) in
                    let embeddedQMatrix5 =
                      match modelParams3 with ModelParams1 x1051
                      then
                        x1051.embeddedQMatrix
                      else
                        let #var"2115" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 201:4-201:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st560
                        (lam st561.
                           lam x875.
                             (st561, x875))
                        (match embeddedQMatrix5 with EmbeddedMarkovChainMatrix1 x1091
                         then
                           x1091.totalRates
                         else
                           let #var"2112" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 292:18-292:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x876.
                                p_pure x876)
                             (exit 1))
                    with
                      (st562, x877)
                    in
                    match
                      p_map
                        st562
                        (lam x878.
                           lam x879.
                             mkExponential
                               (addf
                                  (addf (get x878 x879) (mulf (int2float x874) 0.))
                                  (mulf (int2float nodeLabel11) 0.)))
                        x877
                    with
                      (st563, x880)
                    in
                    match
                      p_map
                        st563
                        (lam x882.
                           subi (addi x882 1) 1)
                        startState
                    with
                      (st564, x883)
                    in
                    match p_apply st564 x880 x883 with (st565, x884)
                    in
                    match p_assume st565 (hrmStoreBranchTime nodeLabel11 x874) x884 with (st566, x885)
                    in
                    match
                      p_map
                        st566
                        (lam x886.
                           subf startAge x886)
                        x885
                    with
                      (st567, x887)
                    in
                    match
                      sampleHostHistoryRec1
                        st567
                        startState
                        (get finalRep11 (subi x874 1))
                        x887
                        finalAge32
                        x874
                        nodeLabel11
                        embeddedQMatrix5
                    with
                      (st568, bridge)
                    in
                    match
                      p_map
                        st568
                        (lam x888.
                           match x888 with Bridge1 x1081
                           then
                             x1081.success
                           else
                             let #var"2113" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 304:19-304:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge
                    with
                      (st569, x889)
                    in
                    match bool2real st569 x889 with (st570, x890)
                    in
                    let st571 =
                      p_weight
                        st570
                        (hrmStoreBridgeSuppWeight nodeLabel11 x874)
                        (lam x893.
                           externalLog
                             (addf
                                (addf x893 (mulf (int2float x874) 0.))
                                (mulf (int2float nodeLabel11) 0.)))
                        x890
                    in
                    let foo5 = {} in
                    p_map
                      st571
                      (lam x892.
                         match x892 with Bridge1 x1071
                         then
                           x1071.events
                         else
                           let #var"2114" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 305:9-305:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge
  in
  recursive
    let rec16 =
      lam st331.
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
                          anon25 st331 c35 c36 c37 c38 c39 c40 (get s15 0)
                        with
                          (st332, x500)
                        in
                        match splitAt s15 1 with {#label"1" = x501}
                        in
                        match rec16 st332 c35 c36 c37 c38 c39 c40 x501 with (st333, x502)
                        in
                        (st333, cons x500 x502)
                      else match s15 with [ e15 ]
                      then
                        match splitAt s15 1 with {#label"1" = x503}
                        in
                        let slice14 = x503 in
                        match anon25 st331 c35 c36 c37 c38 c39 c40 e15 with (st334, x504)
                        in
                        (st334, [ x504 ])
                      else match s15 with ""
                      in
                      (st331, "")
    let rec17 =
      lam st335.
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
                          anon26 st335 c41 c42 c43 c44 c45 c46 (get s16 0)
                        with
                          (st336, x505)
                        in
                        match splitAt s16 1 with {#label"1" = x506}
                        in
                        match rec17 st336 c41 c42 c43 c44 c45 c46 x506 with (st337, x507)
                        in
                        (st337, cons x505 x507)
                      else match s16 with [ e16 ]
                      then
                        match splitAt s16 1 with {#label"1" = x508}
                        in
                        let slice15 = x508 in
                        match anon26 st335 c41 c42 c43 c44 c45 c46 e16 with (st338, x509)
                        in
                        (st338, [ x509 ])
                      else match s16 with ""
                      in
                      (st335, "")
  in
  let anon27 =
    lam h2.
      lam x873.
        lti
          (match
             isNaN1
               (match h2 with Event1 x1101
                then
                  x1101.eventTime
                else
                  let #var"2107" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 241:12-241:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             negi 1
           else match
             isNaN1
               (match x873 with Event1 x1141
                then
                  x1141.eventTime
                else
                  let #var"2108" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 244:12-244:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
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
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 247:6-247:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
                  in
                  exit 1)
               (match x873 with Event1 x1161
                then
                  x1161.eventTime
                else
                  let #var"2111" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 247:25-247:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
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
                match splitAt seq1 1 with {#label"1" = x510}
                in
                let seq2 = x510 in
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
                match splitAt seq11 1 with {#label"1" = x511}
                in
                let seq21 = x511 in
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
                match splitAt seq12 1 with {#label"1" = x512}
                in
                let seq22 = x512 in
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
                match splitAt seq13 1 with {#label"1" = x513}
                in
                let seq23 = x513 in
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
      lam st339.
        lam seq31.
          p_map
            st339
            (lam x514.
               match null x514 with true
               then
                 x514
               else
                 let h1 = head x514 in
                 let lr1 = work14 h1 "" "" (reverse (tail x514)) in
                 match lr1 with (#var"X6",)
                 in
                 match lr1 with {#label"1" = #var"X7"}
                 in
                 concat (quickSort #var"X6") (cons h1 (quickSort #var"X7")))
            seq31
  in
  recursive
    let rec213 =
      lam st340.
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
                          let x515 = get s214 0 in
                          match
                            p_map
                              st340
                              (lam x516.
                                 lam x517.
                                   addf x516 x517)
                              acc20
                          with
                            (st341, x518)
                          in
                          match
                            hostIndepLikelihood
                              st341
                              1
                              (get c51 (subi x515 1))
                              (get c52 (subi x515 1))
                              c53
                              c54
                              (get c56 (subi x515 1))
                              (match c55 with ModelParams1 x1301
                               then
                                 x1301.embeddedQMatrix
                               else
                                 let #var"254" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st342, x519)
                          in
                          match p_apply st342 x518 x519 with (st343, x520)
                          in
                          match splitAt s214 1 with {#label"1" = x521}
                          in
                          rec213 st343 c51 c52 c53 c54 c55 c56 x520 x521
                        else match s214 with ""
                        in
                        (st340, acc20)
    let rec214 =
      lam st344.
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
                          let x522 = get s215 0 in
                          match
                            p_map
                              st344
                              (lam x523.
                                 lam x524.
                                   addf x523 x524)
                              acc23
                          with
                            (st345, x525)
                          in
                          match
                            hostIndepLikelihood2
                              st345
                              1
                              (get c57 (subi x522 1))
                              (get c58 (subi x522 1))
                              c59
                              c60
                              (get c62 (subi x522 1))
                              (match c61 with ModelParams1 x1302
                               then
                                 x1302.embeddedQMatrix
                               else
                                 let #var"255" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st346, x526)
                          in
                          match p_apply st346 x525 x526 with (st347, x527)
                          in
                          match splitAt s215 1 with {#label"1" = x528}
                          in
                          rec214 st347 c57 c58 c59 c60 c61 c62 x527 x528
                        else match s215 with ""
                        in
                        (st344, acc23)
  in
  let anon28 = lam x872.
      addi x872 1 in
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
      lam st348.
        lam acc24.
          lam s216.
            match s216 with [ _ ] ++ _
            then
              match
                p_map
                  st348
                  (lam x529.
                     lam x530.
                       addf x529 x530)
                  acc24
              with
                (st349, x531)
              in
              match p_apply st349 x531 (get s216 0) with (st350, x532)
              in
              match splitAt s216 1 with {#label"1" = x533}
              in
              rec215 st350 x532 x533
            else match s216 with ""
            in
            (st348, acc24)
  in
  let fold =
    lam st558.
      lam init1.
        lam seq5.
          match seq5 with [ _ ] ++ _
          then
            match
              p_map
                st558
                (lam x869.
                   addf init1 x869)
                (get seq5 0)
            with
              (st559, x870)
            in
            match splitAt seq5 1 with {#label"1" = x871}
            in
            rec215 st559 x870 x871
          else match seq5 with ""
          in
          (st558, p_pure init1)
  in
  recursive
    let rec216 =
      lam st351.
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
                        st351
                        (lam x534.
                           addi x534 1)
                        (get field1 0)
                    with
                      (st352, x535)
                    in
                    match mtxGet1 st352 x535 (addi (get s217 0) 1) c63 with (st353, x536)
                    in
                    match log11 st353 x536 with (st354, x537)
                    in
                    match splitAt field1 1 with {#label"1" = x538}
                    in
                    (st354, (snoc field x537, x538))
                  else
                    let x539 = error "foldl2: Cannot happen!" in
                    match x539 with (x540,)
                    in
                    match x539 with {#label"1" = x541}
                    in
                    (st351, (map (lam x542.
                         p_pure x542) x540, map (lam x543.
                         p_pure x543) x541))
                with
                  (st355, x544)
                in
                match splitAt s217 1 with {#label"1" = x545}
                in
                rec216 st355 c63 x544 x545
              else match s217 with ""
              in
              (st351, acc25)
    let rec217 =
      lam st356.
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
                        st356
                        (lam x546.
                           addi x546 1)
                        (get field3 0)
                    with
                      (st357, x547)
                    in
                    match
                      p_map
                        st357
                        (lam x548.
                           addi x548 1)
                        (get s218 0)
                    with
                      (st358, x549)
                    in
                    match mtxGet2 st358 x547 x549 c64 with (st359, x550)
                    in
                    match log11 st359 x550 with (st360, x551)
                    in
                    match splitAt field3 1 with {#label"1" = x552}
                    in
                    (st360, (snoc field2 x551, x552))
                  else
                    let x553 = error "foldl2: Cannot happen!" in
                    match x553 with (x554,)
                    in
                    match x553 with {#label"1" = x555}
                    in
                    (st356, (map (lam x556.
                         p_pure x556) x554, map (lam x557.
                         p_pure x557) x555))
                with
                  (st361, x558)
                in
                match splitAt s218 1 with {#label"1" = x559}
                in
                rec217 st361 c64 x558 x559
              else match s218 with ""
              in
              (st356, acc26)
  in
  recursive
    let rec218 =
      lam st362.
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
                        st362
                        (lam x560.
                           addi x560 1)
                        (get s219 0)
                    with
                      (st363, x561)
                    in
                    match mtxGet1 st363 x561 (addi (get field5 0) 1) c65 with (st364, x562)
                    in
                    match log11 st364 x562 with (st365, x563)
                    in
                    match splitAt field5 1 with {#label"1" = x564}
                    in
                    (st365, (snoc field4 x563, x564))
                  else
                    let x565 = error "foldl2: Cannot happen!" in
                    match x565 with (x566,)
                    in
                    match x565 with {#label"1" = x567}
                    in
                    (st362, (map (lam x568.
                         p_pure x568) x566, x567))
                with
                  (st366, x569)
                in
                match splitAt s219 1 with {#label"1" = x570}
                in
                rec218 st366 c65 x569 x570
              else match s219 with ""
              in
              (st362, acc27)
    let rec219 =
      lam st367.
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
                        st367
                        (lam x571.
                           addi x571 1)
                        (get s220 0)
                    with
                      (st368, x572)
                    in
                    match
                      p_map
                        st368
                        (lam x573.
                           addi x573 1)
                        (get field7 0)
                    with
                      (st369, x574)
                    in
                    match mtxGet2 st369 x572 x574 c66 with (st370, x575)
                    in
                    match log11 st370 x575 with (st371, x576)
                    in
                    match splitAt field7 1 with {#label"1" = x577}
                    in
                    (st371, (snoc field6 x576, x577))
                  else
                    let x578 = error "foldl2: Cannot happen!" in
                    match x578 with (x579,)
                    in
                    match x578 with {#label"1" = x580}
                    in
                    (st367, (map (lam x581.
                         p_pure x581) x579, map (lam x582.
                         p_pure x582) x580))
                with
                  (st372, x583)
                in
                match splitAt s220 1 with {#label"1" = x584}
                in
                rec219 st372 c66 x583 x584
              else match s220 with ""
              in
              (st367, acc28)
  in
  recursive
    let any =
      lam st373.
        lam seq.
          match null seq with true
          then
            (st373, p_pure false)
          else match
            p_map st373 (lam x585.
                 eqi x585 2) (head seq)
          with
            (st374, x586)
          in
          p_bind
            st374
            hrmStoreSubmodel
            (hrmInit {})
            (lam st375.
               lam x587.
                 match x587 with true
                 then
                   (st375, p_pure true)
                 else
                   any st375 (tail seq))
            x586
  in
  let any1 = lam st557.
      lam l21.
        any st557 l21 in
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 115:14-115:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 121:6-121:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
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
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 123:6-123:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create13 (addi (subi nHosts 1) 1))
                        with
                          (st377, unorderedBranch)
                        in
                        match paste01 st377 unorderedBranch with (st378, x588)
                        in
                        match quickSort1 st378 x588 with (st379, orderedEvents)
                        in
                        match length13 st379 orderedEvents with (st380, nEvents4)
                        in
                        match
                          allTimesValidBranch st380 parentRep orderedEvents 1 nEvents4 nHosts
                        with
                          (st381, x589)
                        in
                        match
                          p_bind
                            st381
                            hrmStoreSubmodel
                            (hrmInit {})
                            (lam st382.
                               lam x590.
                                 match
                                   match x590 with true
                                   then
                                     let s221 = create14 (addi (subi (length12 unorderedBranch) 1) 1)
                                     in
                                     match
                                       match s221 with [ _ ] ++ _
                                       then
                                         let x591 = get s221 0 in
                                         match
                                           hostIndepLikelihood
                                             st382
                                             1
                                             (get parentRep (subi x591 1))
                                             (get rep1 (subi x591 1))
                                             parentAge
                                             finalAge3
                                             (get unorderedBranch (subi x591 1))
                                             (match modelParams11 with ModelParams1 x1303
                                              then
                                                x1303.embeddedQMatrix
                                              else
                                                let #var"257" =
                                                  print
                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                                in
                                                exit 1)
                                         with
                                           (st383, x592)
                                         in
                                         match
                                           p_map
                                             st383
                                             (lam x593.
                                                addf 0. x593)
                                             x592
                                         with
                                           (st384, x594)
                                         in
                                         match splitAt s221 1 with {#label"1" = x595}
                                         in
                                         rec213
                                           st384
                                           parentRep
                                           rep1
                                           parentAge
                                           finalAge3
                                           modelParams11
                                           unorderedBranch
                                           x594
                                           x595
                                       else match s221 with ""
                                       in
                                       (st382, p_pure 0.)
                                     with
                                       (st385, x596)
                                     in
                                     match
                                       p_map
                                         st385
                                         (lam x597.
                                            lam x598.
                                              subf x597 x598)
                                         x596
                                     with
                                       (st386, x599)
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
                                                     (lam x600.
                                                        addi x600 1)
                                                     (get field9 0)
                                                 with
                                                   (st387, x601)
                                                 in
                                                 match
                                                   mtxGet1 st387 x601 (addi (get rep1 0) 1) branchKernel
                                                 with
                                                   (st388, x602)
                                                 in
                                                 match log11 st388 x602 with (st389, x603)
                                                 in
                                                 match splitAt field9 1 with {#label"1" = x604}
                                                 in
                                                 (st389, (snoc field8 x603, x604))
                                               else
                                                 let x605 = error "foldl2: Cannot happen!" in
                                                 match x605 with (x606,)
                                                 in
                                                 match x605 with {#label"1" = x607}
                                                 in
                                                 (st386, (map
                                                   (lam x608.
                                                      p_pure x608)
                                                   x606, map
                                                   (lam x609.
                                                      p_pure x609)
                                                   x607))
                                             with
                                               (st390, x610)
                                             in
                                             match splitAt rep1 1 with {#label"1" = x611}
                                             in
                                             rec216 st390 branchKernel x610 x611
                                           else match rep1 with ""
                                           in
                                           (st386, acc29)
                                         with
                                           (st391, x612)
                                         in
                                         match x612 with (field10, field11)
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
                                                     (lam x613.
                                                        addi x613 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st392, x614)
                                                 in
                                                 match
                                                   mtxGet1 st392 x614 (addi (get field13 0) 1) branchKernel
                                                 with
                                                   (st393, x615)
                                                 in
                                                 match log11 st393 x615 with (st394, x616)
                                                 in
                                                 match splitAt field13 1 with {#label"1" = x617}
                                                 in
                                                 (st394, (snoc field12 x616, x617))
                                               else
                                                 let x618 = error "foldl2: Cannot happen!" in
                                                 match x618 with (x619,)
                                                 in
                                                 match x618 with {#label"1" = x620}
                                                 in
                                                 (st386, (map
                                                   (lam x621.
                                                      p_pure x621)
                                                   x619, x620))
                                             with
                                               (st395, x622)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x623}
                                             in
                                             rec218 st395 branchKernel x622 x623
                                           else match parentRep with ""
                                           in
                                           (st386, acc30)
                                         with
                                           (st396, x624)
                                         in
                                         match x624 with (field14, field15)
                                         in
                                         (st396, field14)
                                     with
                                       (st397, x625)
                                     in
                                     match fold st397 0. x625 with (st398, x626)
                                     in
                                     match p_apply st398 x599 x626 with (st399, x627)
                                     in
                                     match
                                       p_bind
                                         st399
                                         hrmStoreSubmodel
                                         (hrmInit {})
                                         (lam st400.
                                            lam x628.
                                              match gti 1 x628 with true
                                              then
                                                match
                                                  getTotalRate st400 parentRep modelParams11 nHosts
                                                with
                                                  (st401, x629)
                                                in
                                                p_map
                                                  st401
                                                  (lam x630.
                                                     mulf (negf (subf parentAge finalAge3)) x630)
                                                  x629
                                              else match
                                                p_map
                                                  st400
                                                  (lam x631.
                                                     get x631 (subi 1 1))
                                                  orderedEvents
                                              with
                                                (st402, nextEvent2)
                                              in
                                              match
                                                p_map
                                                  st402
                                                  (lam x632.
                                                     match x632 with Event1 x3110
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
                                                  (lam x633.
                                                     match x633 with Event1 x1333
                                                     then
                                                       x1333.host
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
                                                  (lam x634.
                                                     lam x635.
                                                       lam st406.
                                                         match
                                                           gti
                                                             (match x634 with Event1 x1313
                                                              then
                                                                x1313.fromState
                                                              else
                                                                let #var"260" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x635
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st406 parentRep hostIndex12 modelParams11
                                                         else
                                                           getGainRate2 st406 parentRep hostIndex12 modelParams11)
                                                  nextEvent2
                                              with
                                                (st407, x636)
                                              in
                                              match
                                                p_map
                                                  st407
                                                  (lam x637.
                                                     match x637 with Event1 x1323
                                                     then
                                                       x1323.toState
                                                     else
                                                       let #var"261" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st408, x638)
                                              in
                                              match
                                                p_subApply st408 hrmStoreSubmodel (hrmInit {}) x636 x638
                                              with
                                                (st409, x639)
                                              in
                                              match p_join st409 x639 with (st410, x640)
                                              in
                                              match
                                                p_map
                                                  st410
                                                  (lam x641.
                                                     lam x642.
                                                       divf x641 x642)
                                                  x640
                                              with
                                                (st411, x643)
                                              in
                                              match p_apply st411 x643 totalLeavingRate12 with (st412, x644)
                                              in
                                              match log11 st412 x644 with (st413, x645)
                                              in
                                              match
                                                p_map
                                                  st413
                                                  (lam x646.
                                                     lam x647.
                                                       lam x648.
                                                         addf (subf x646 x647) x648)
                                                  x645
                                              with
                                                (st414, x649)
                                              in
                                              match
                                                p_map
                                                  st414
                                                  (lam x650.
                                                     lam x651.
                                                       mulf (subf parentAge x650) x651)
                                                  newAge2
                                              with
                                                (st415, x652)
                                              in
                                              match p_apply st415 x652 totalLeavingRate12 with (st416, x653)
                                              in
                                              match p_apply st416 x649 x653 with (st417, x654)
                                              in
                                              match
                                                updateRepertoire st417 parentRep nextEvent2 nHosts
                                              with
                                                (st418, x655)
                                              in
                                              match
                                                fullModelWeight
                                                  st418
                                                  (addi 1 1)
                                                  x655
                                                  rep1
                                                  newAge2
                                                  finalAge3
                                                  orderedEvents
                                                  x628
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st419, x656)
                                              in
                                              p_apply st419 x654 x656)
                                         nEvents4
                                     with
                                       (st420, x657)
                                     in
                                     (st420, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = x627,
                                         logModelDensity = x657,
                                         success = true })
                                   else
                                     (st382, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = p_pure (log1 0.),
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st421, x658)
                                 in
                                 match x658 with CorrectedBranchSample1 x659
                                 in
                                 match x659 with {history = x660}
                                 in
                                 match
                                   p_map
                                     st421
                                     (lam x661.
                                        lam x662.
                                          lam x663.
                                            match x659 with {success = x664}
                                            in
                                            CorrectedBranchSample1
                                              { history = x661,
                                                logSamplingDensity = x662,
                                                logModelDensity = x663,
                                                success = x664 })
                                     x660
                                 with
                                   (st422, x665)
                                 in
                                 match x659 with {logSamplingDensity = x666}
                                 in
                                 match p_apply st422 x665 x666 with (st423, x667)
                                 in
                                 match x659 with {logModelDensity = x668}
                                 in
                                 p_apply st423 x667 x668)
                            x589
                        with
                          (st424, branchSample)
                        in
                        match
                          p_map
                            st424
                            (lam x669.
                               lam x670.
                                 mulf
                                   (subf
                                      (match x669 with CorrectedBranchSample1 x4610
                                       then
                                         x4610.logModelDensity
                                       else
                                         let #var"262" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 129:15-129:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x670)
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
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 129:90-129:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1))
                                         0.)))
                            branchSample
                        with
                          (st425, x671)
                        in
                        match
                          p_map
                            st425
                            (lam x672.
                               match x672 with CorrectedBranchSample1 x4710
                               then
                                 x4710.logSamplingDensity
                               else
                                 let #var"264" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 129:46-129:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st426, x673)
                        in
                        match p_apply st426 x671 x673 with (st427, x674)
                        in
                        let nl = (match tree2 with MsgLeaf carried24
                                             then
                                               carried24.label
                                             else match tree2 with MsgNode carried25
                                             then
                                               carried25.label
                                             else
                                               let #var"263" =
                                                 print
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 129:90-129:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1) in
                        let st428 =
                          p_weight
                            st427
                            (hrmStoreLikrWeight nl)
                            (/-temp-/lam x677.
                               x677)
                            x674
                        in
                        let foo = {} in
                        match
                          p_map
                            st428
                            (lam x675.
                               match x675 with CorrectedBranchSample1 x4510
                               then
                                 x4510.history
                               else
                                 let #var"265" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 135:16-135:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st429, x676)
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
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 132:12-132:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 133:14-133:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            history = x676,
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 138:34-138:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 139:51-139:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                             in
                             exit 1)
                      with
                        (st431, rep2)
                      in
                      match any1 st431 rep2 with (st432, x678)
                      in
                      match bool2real st432 x678 with (st433, x679)
                      in
                      let nl = (match tree2 with MsgLeaf carried50
                                         then
                                           carried50.label
                                         else match tree2 with MsgNode carried51
                                         then
                                           carried51.label
                                         else
                                           let #var"293" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 141:43-141:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1) in
                      let st434 =
                        p_weight
                          st433
                          (hrmStoreNodeSuppWeight nl)
                          (lam x784.
                             externalLog
                               (addf
                                  x784
                                  (mulf
                                     (int2float
                                        (match tree2 with MsgLeaf carried50
                                         then
                                           carried50.label
                                         else match tree2 with MsgNode carried51
                                         then
                                           carried51.label
                                         else
                                           let #var"293" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 141:43-141:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1))
                                     0.)))
                          x679
                      in
                      let foo1 = {} in
                      let finalAge31 =
                        match tree2 with MsgLeaf carried48
                        then
                          carried48.age
                        else match tree2 with MsgNode carried49
                        then
                          carried49.age
                        else
                          let #var"292" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 149:6-149:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                          in
                          exit 1
                      in
                      match
                        rec17
                          st434
                          parentRep
                          rep2
                          parentAge
                          finalAge31
                          (match tree2 with MsgLeaf carried36
                           then
                             carried36.label
                           else match tree2 with MsgNode carried37
                           then
                             carried37.label
                           else
                             let #var"272" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 151:6-151:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                             in
                             exit 1)
                          modelParams11
                          (create13 (addi (subi nHosts 1) 1))
                      with
                        (st435, unorderedBranch1)
                      in
                      match paste01 st435 unorderedBranch1 with (st436, x680)
                      in
                      match quickSort1 st436 x680 with (st437, orderedEvents1)
                      in
                      match length13 st437 orderedEvents1 with (st438, nEvents41)
                      in
                      match
                        allTimesValidBranch st438 parentRep orderedEvents1 1 nEvents41 nHosts
                      with
                        (st439, x681)
                      in
                      match
                        p_bind
                          st439
                          hrmStoreSubmodel
                          (hrmInit {})
                          (lam st440.
                             lam x682.
                               match
                                 match x682 with true
                                 then
                                   let s222 = create14 (addi (subi (length12 unorderedBranch1) 1) 1)
                                   in
                                   match
                                     match s222 with [ _ ] ++ _
                                     then
                                       let x683 = get s222 0 in
                                       match
                                         hostIndepLikelihood2
                                           st440
                                           1
                                           (get parentRep (subi x683 1))
                                           (get rep2 (subi x683 1))
                                           parentAge
                                           finalAge31
                                           (get unorderedBranch1 (subi x683 1))
                                           (match modelParams11 with ModelParams1 x1304
                                            then
                                              x1304.embeddedQMatrix
                                            else
                                              let #var"273" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                              in
                                              exit 1)
                                       with
                                         (st441, x684)
                                       in
                                       match
                                         p_map
                                           st441
                                           (lam x685.
                                              addf 0. x685)
                                           x684
                                       with
                                         (st442, x686)
                                       in
                                       match splitAt s222 1 with {#label"1" = x687}
                                       in
                                       rec214
                                         st442
                                         parentRep
                                         rep2
                                         parentAge
                                         finalAge31
                                         modelParams11
                                         unorderedBranch1
                                         x686
                                         x687
                                     else match s222 with ""
                                     in
                                     (st440, p_pure 0.)
                                   with
                                     (st443, x688)
                                   in
                                   match
                                     p_map
                                       st443
                                       (lam x689.
                                          lam x690.
                                            subf x689 x690)
                                       x688
                                   with
                                     (st444, x691)
                                   in
                                   match
                                     match geqi (length parentRep) (length rep2) with true
                                     then
                                       let acc33 = ("", parentRep) in
                                       match
                                         match rep2 with [ _ ] ++ _
                                         then
                                           match acc33 with (field16, field17)
                                           in
                                           match
                                             match field17 with [ _ ] ++ _
                                             then
                                               match
                                                 p_map
                                                   st444
                                                   (lam x692.
                                                      addi x692 1)
                                                   (get field17 0)
                                               with
                                                 (st445, x693)
                                               in
                                               match
                                                 p_map
                                                   st445
                                                   (lam x694.
                                                      addi x694 1)
                                                   (get rep2 0)
                                               with
                                                 (st446, x695)
                                               in
                                               match mtxGet2 st446 x693 x695 branchKernel with (st447, x696)
                                               in
                                               match log11 st447 x696 with (st448, x697)
                                               in
                                               match splitAt field17 1 with {#label"1" = x698}
                                               in
                                               (st448, (snoc field16 x697, x698))
                                             else
                                               let x699 = error "foldl2: Cannot happen!" in
                                               match x699 with (x700,)
                                               in
                                               match x699 with {#label"1" = x701}
                                               in
                                               (st444, (map
                                                 (lam x702.
                                                    p_pure x702)
                                                 x700, map
                                                 (lam x703.
                                                    p_pure x703)
                                                 x701))
                                           with
                                             (st449, x704)
                                           in
                                           match splitAt rep2 1 with {#label"1" = x705}
                                           in
                                           rec217 st449 branchKernel x704 x705
                                         else match rep2 with ""
                                         in
                                         (st444, acc33)
                                       with
                                         (st450, x706)
                                       in
                                       match x706 with (field18, field19)
                                       in
                                       (st450, field18)
                                     else
                                       let acc34 = ("", rep2) in
                                       match
                                         match parentRep with [ _ ] ++ _
                                         then
                                           match acc34 with (field20, field21)
                                           in
                                           match
                                             match field21 with [ _ ] ++ _
                                             then
                                               match
                                                 p_map
                                                   st444
                                                   (lam x707.
                                                      addi x707 1)
                                                   (get parentRep 0)
                                               with
                                                 (st451, x708)
                                               in
                                               match
                                                 p_map
                                                   st451
                                                   (lam x709.
                                                      addi x709 1)
                                                   (get field21 0)
                                               with
                                                 (st452, x710)
                                               in
                                               match mtxGet2 st452 x708 x710 branchKernel with (st453, x711)
                                               in
                                               match log11 st453 x711 with (st454, x712)
                                               in
                                               match splitAt field21 1 with {#label"1" = x713}
                                               in
                                               (st454, (snoc field20 x712, x713))
                                             else
                                               let x714 = error "foldl2: Cannot happen!" in
                                               match x714 with (x715,)
                                               in
                                               match x714 with {#label"1" = x716}
                                               in
                                               (st444, (map
                                                 (lam x717.
                                                    p_pure x717)
                                                 x715, map
                                                 (lam x718.
                                                    p_pure x718)
                                                 x716))
                                           with
                                             (st455, x719)
                                           in
                                           match splitAt parentRep 1 with {#label"1" = x720}
                                           in
                                           rec219 st455 branchKernel x719 x720
                                         else match parentRep with ""
                                         in
                                         (st444, acc34)
                                       with
                                         (st456, x721)
                                       in
                                       match x721 with (field22, field23)
                                       in
                                       (st456, field22)
                                   with
                                     (st457, x722)
                                   in
                                   match fold st457 0. x722 with (st458, x723)
                                   in
                                   match p_apply st458 x691 x723 with (st459, x724)
                                   in
                                   match
                                     p_bind
                                       st459
                                       hrmStoreSubmodel
                                       (hrmInit {})
                                       (lam st460.
                                          lam x725.
                                            match gti 1 x725 with true
                                            then
                                              match
                                                getTotalRate st460 parentRep modelParams11 nHosts
                                              with
                                                (st461, x726)
                                              in
                                              p_map
                                                st461
                                                (lam x727.
                                                   mulf (negf (subf parentAge finalAge31)) x727)
                                                x726
                                            else match
                                              p_map
                                                st460
                                                (lam x728.
                                                   get x728 (subi 1 1))
                                                orderedEvents1
                                            with
                                              (st462, nextEvent3)
                                            in
                                            match
                                              p_map
                                                st462
                                                (lam x729.
                                                   match x729 with Event1 x3111
                                                   then
                                                     x3111.eventTime
                                                   else
                                                     let #var"274" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 25:17-25:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st463, newAge3)
                                            in
                                            match
                                              getTotalRate st463 parentRep modelParams11 nHosts
                                            with
                                              (st464, totalLeavingRate13)
                                            in
                                            match
                                              p_map
                                                st464
                                                (lam x730.
                                                   match x730 with Event1 x1334
                                                   then
                                                     x1334.host
                                                   else
                                                     let #var"275" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st465, hostIndex13)
                                            in
                                            match
                                              p_map
                                                st465
                                                (lam x731.
                                                   lam x732.
                                                     lam st466.
                                                       match
                                                         gti
                                                           (match x731 with Event1 x1314
                                                            then
                                                              x1314.fromState
                                                            else
                                                              let #var"276" =
                                                                print
                                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                              in
                                                              exit 1)
                                                           x732
                                                       with
                                                         true
                                                       then
                                                         getLossRate2 st466 parentRep hostIndex13 modelParams11
                                                       else
                                                         getGainRate2 st466 parentRep hostIndex13 modelParams11)
                                                nextEvent3
                                            with
                                              (st467, x733)
                                            in
                                            match
                                              p_map
                                                st467
                                                (lam x734.
                                                   match x734 with Event1 x1324
                                                   then
                                                     x1324.toState
                                                   else
                                                     let #var"277" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st468, x735)
                                            in
                                            match
                                              p_subApply st468 hrmStoreSubmodel (hrmInit {}) x733 x735
                                            with
                                              (st469, x736)
                                            in
                                            match p_join st469 x736 with (st470, x737)
                                            in
                                            match
                                              p_map
                                                st470
                                                (lam x738.
                                                   lam x739.
                                                     divf x738 x739)
                                                x737
                                            with
                                              (st471, x740)
                                            in
                                            match p_apply st471 x740 totalLeavingRate13 with (st472, x741)
                                            in
                                            match log11 st472 x741 with (st473, x742)
                                            in
                                            match
                                              p_map
                                                st473
                                                (lam x743.
                                                   lam x744.
                                                     lam x745.
                                                       addf (subf x743 x744) x745)
                                                x742
                                            with
                                              (st474, x746)
                                            in
                                            match
                                              p_map
                                                st474
                                                (lam x747.
                                                   lam x748.
                                                     mulf (subf parentAge x747) x748)
                                                newAge3
                                            with
                                              (st475, x749)
                                            in
                                            match p_apply st475 x749 totalLeavingRate13 with (st476, x750)
                                            in
                                            match p_apply st476 x746 x750 with (st477, x751)
                                            in
                                            match
                                              updateRepertoire st477 parentRep nextEvent3 nHosts
                                            with
                                              (st478, x752)
                                            in
                                            match
                                              fullModelWeight1
                                                st478
                                                (addi 1 1)
                                                x752
                                                rep2
                                                newAge3
                                                finalAge31
                                                orderedEvents1
                                                x725
                                                nHosts
                                                modelParams11
                                            with
                                              (st479, x753)
                                            in
                                            p_apply st479 x751 x753)
                                       nEvents41
                                   with
                                     (st480, x754)
                                   in
                                   (st480, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = x724,
                                       logModelDensity = x754,
                                       success = true })
                                 else
                                   (st440, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = p_pure (log1 0.),
                                       logModelDensity = p_pure (log1 0.),
                                       success = false })
                               with
                                 (st481, x755)
                               in
                               match x755 with CorrectedBranchSample1 x756
                               in
                               match x756 with {history = x757}
                               in
                               match
                                 p_map
                                   st481
                                   (lam x758.
                                      lam x759.
                                        lam x760.
                                          match x756 with {success = x761}
                                          in
                                          CorrectedBranchSample1
                                            { history = x758,
                                              logSamplingDensity = x759,
                                              logModelDensity = x760,
                                              success = x761 })
                                   x757
                               with
                                 (st482, x762)
                               in
                               match x756 with {logSamplingDensity = x763}
                               in
                               match p_apply st482 x762 x763 with (st483, x764)
                               in
                               match x756 with {logModelDensity = x765}
                               in
                               p_apply st483 x764 x765)
                          x681
                      with
                        (st484, branchSample1)
                      in
                      match
                        p_map
                          st484
                          (lam x766.
                             lam x767.
                               lam x768.
                                 subf
                                   (subf
                                      (match x766 with CorrectedBranchSample1 x7010
                                       then
                                         x7010.logModelDensity
                                       else
                                         let #var"278" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 157:14-157:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x767)
                                   x768)
                          branchSample1
                      with
                        (st485, x769)
                      in
                      match
                        p_map
                          st485
                          (lam x770.
                             match x770 with CorrectedBranchSample1 x7110
                             then
                               x7110.logSamplingDensity
                             else
                               let #var"279" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 157:45-157:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st486, x771)
                      in
                      match p_apply st486 x769 x771 with (st487, x772)
                      in
                      match
                        getRepertoireSamplingDensity st487 rep2 samplingProb
                      with
                        (st488, x773)
                      in
                      match
                        p_map
                          st488
                          (lam x774.
                             mulf
                               x774
                               (exp1
                                  (mulf
                                     (int2float
                                        (match tree2 with MsgLeaf carried38
                                         then
                                           carried38.label
                                         else match tree2 with MsgNode carried39
                                         then
                                           carried39.label
                                         else
                                           let #var"280" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 157:113-157:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1))
                                     0.)))
                          x773
                      with
                        (st489, x775)
                      in
                      match p_apply st489 x772 x775 with (st490, x776)
                      in
                      let nl = (match tree2 with MsgLeaf carried38
                                         then
                                           carried38.label
                                         else match tree2 with MsgNode carried39
                                         then
                                           carried39.label
                                         else
                                           let #var"280" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 157:113-157:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1) in
                      let st491 =
                        p_weight
                          st490
                          (hrmStoreLikrWeight nl)
                          (/-temp-/lam x783.
                             x783)
                          x776
                      in
                      let foo2 = {} in
                      match observationMessage1 st491 rep2 with (st492, newMsg)
                      in
                      -- Export node messages
                      let st492 = p_export st492 (hrmStoreNodeMsg nl) newMsg in
                      let st492 = p_export st492 (hrmStorePreorderMsg nl) preorderMsg in
                      -- Done
                      match
                        mtxMul
                          st492
                          newMsg
                          (match tree2 with MsgNode x6910
                           then
                             x6910.leftKernel
                           else
                             let #var"281" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 161:33-161:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st493, x777)
                      in
                      match
                        sampleTreeHistory
                          st493
                          (match tree2 with MsgNode x6410
                           then
                             x6410.left
                           else
                             let #var"282" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 166:6-166:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          nHosts
                          x777
                          rep2
                          (match tree2 with MsgLeaf carried40
                           then
                             carried40.age
                           else match tree2 with MsgNode carried41
                           then
                             carried41.age
                           else
                             let #var"283" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 166:39-166:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6710
                           then
                             x6710.leftKernel
                           else
                             let #var"284" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 166:62-166:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st494, x778)
                      in
                      match
                        mtxMul
                          st494
                          newMsg
                          (match tree2 with MsgNode x6810
                           then
                             x6810.rightKernel
                           else
                             let #var"285" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 162:34-162:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st495, x779)
                      in
                      match
                        sampleTreeHistory
                          st495
                          (match tree2 with MsgNode x6010
                           then
                             x6010.right
                           else
                             let #var"286" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 169:6-169:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          nHosts
                          x779
                          rep2
                          (match tree2 with MsgLeaf carried42
                           then
                             carried42.age
                           else match tree2 with MsgNode carried43
                           then
                             carried43.age
                           else
                             let #var"287" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 169:41-169:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6310
                           then
                             x6310.rightKernel
                           else
                             let #var"288" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 169:64-169:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st496, x780)
                      in
                      match
                        p_map
                          st496
                          (lam x781.
                             match x781 with CorrectedBranchSample1 x5910
                             then
                               x5910.history
                             else
                               let #var"289" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 176:16-176:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st497, x782)
                      in
                      (st497, HistoryNode
                        { age =
                            match tree2 with MsgLeaf carried44
                            then
                              carried44.age
                            else match tree2 with MsgNode carried45
                            then
                              carried45.age
                            else
                              let #var"290" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 173:12-173:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
                              in
                              exit 1,
                          label =
                            match tree2 with MsgLeaf carried46
                            then
                              carried46.label
                            else match tree2 with MsgNode carried47
                            then
                              carried47.label
                            else
                              let #var"291" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 174:14-174:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                              in
                              exit 1,
                          left = x778,
                          right = x780,
                          history = x782,
                          repertoire = rep2 })
  in
  let anon29 =
    lam n22.
      lam hostDistances2.
        lam x868.
          divf
            x868
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
              match splitAt s17 1 with {#label"1" = x785}
              in
              cons (anon29 c67 c68 (get s17 0)) (rec18 c67 c68 x785)
            else match s17 with [ e17 ]
            then
              match splitAt s17 1 with {#label"1" = x786}
              in
              let slice16 = x786 in
              [ anon29 c67 c68 e17 ]
            else match s17 with ""
            in
            ""
  in
  let anon30 =
    lam n21.
      lam hostDistances1.
        lam x867.
          rec18 n21 hostDistances1 x867
  in
  recursive
    let rec19 =
      lam c69.
        lam c70.
          lam s18.
            match s18 with [ _,
                _ ] ++ _
            then
              match splitAt s18 1 with {#label"1" = x787}
              in
              cons (anon30 c69 c70 (get s18 0)) (rec19 c69 c70 x787)
            else match s18 with [ e18 ]
            then
              match splitAt s18 1 with {#label"1" = x788}
              in
              let slice17 = x788 in
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
          [ 1., 0., 1., 1., 1. ],
          [ 2., 2., 0., 1., 1. ],
          [ 2., 2., 1., 0., 1. ],
          [ 1., 1., 1., 1., 0. ] ] }
  in
  match input1 with {symbiontTree = #var"X9"}
  in
  let symbiontTree = #var"X9" in
  match input1 with {hostDistances = #var"X10"}
  in
  let hostDistances = #var"X10" in
  let nHosts1 = length11 hostDistances in
  -- Export the input tree
  recursive let buildTree = lam stree.
    match stree with Leaf { label = label, age = _ } then 
      HRMLeaf { label = label }
    else match stree with Node { label = label, age = _, left = left, right = right } in 
      HRMNode { label = label, left = buildTree left, right = buildTree right } in
  match p_export st (hrmStoreTree (buildTree symbiontTree) (match input1 with {interactions = ints} in ints)) (p_pure ()) with st in
  -- Done
  match
    p_assume
      st hrmStoreLambda (p_pure (mkDirichlet [ 1., 1., 1., 1. ]))
  with
    (st498, lambda)
  in
  match
    p_assume st498 hrmStoreMu (p_pure (mkExponential 10.))
  with
    (st499, mu)
  in
  match
    p_assume st499 hrmStoreBeta (p_pure (mkExponential 1.))
  with
    (st500, beta)
  in
  match
    p_map
      st500
      (lam x789.
         subf 0. (get x789 (subi 1 1)))
      lambda
  with
    (st501, x790)
  in
  match
    p_map st501 (lam x791.
         get x791 (subi 1 1)) lambda
  with
    (st502, x792)
  in
  match
    p_map st502 (lam x793.
         get x793 (subi 2 1)) lambda
  with
    (st503, x794)
  in
  match
    p_map
      st503
      (lam x795.
         lam x796.
           subf 0. (addf (get x795 (subi 2 1)) x796))
      lambda
  with
    (st504, x797)
  in
  match
    p_map st504 (lam x798.
         get x798 (subi 3 1)) lambda
  with
    (st505, x799)
  in
  match p_apply st505 x797 x799 with (st506, x800)
  in
  match
    p_map st506 (lam x801.
         get x801 (subi 3 1)) lambda
  with
    (st507, x802)
  in
  match
    p_map st507 (lam x803.
         get x803 (subi 4 1)) lambda
  with
    (st508, x804)
  in
  match
    p_map
      st508
      (lam x805.
         subf 0. (get x805 (subi 4 1)))
      lambda
  with
    (st509, x806)
  in
  match
    p_traverseSeq
      st509
      (lam st510.
         lam x807.
           (st510, x807))
      [ x790,
        x792,
        p_pure 0.,
        x794,
        x800,
        x802,
        p_pure 0.,
        x804,
        x806 ]
  with
    (st511, x808)
  in
  match
    p_map
      st511
      (lam x809.
         tmOpaque (let len = length x809 in
          let a71 = externalExtArrMakeUninit extArrKindFloat64 len in
          recursive
            let work3 =
              lam i22.
                match eqi i22 len with true
                then
                  {}
                else
                  let #var"2110" = externalExtArrSet a71 i22 (get x809 i22) in
                  work3 (addi i22 1)
          in
          let #var"2210" = work3 0 in
          a71))
      x808
  with
    (st512, x810)
  in
  match matFromArrExn st512 3 3 x810 with (st513, mtx5)
  in
  match p_map st513 (lam x811.
         x811.m) mtx5 with (st514, m2)
  in
  match p_map st514 (lam x812.
         x812.n) mtx5 with (st515, n4)
  in
  match
    p_map
      st515
      (lam x813.
         lam x814.
           lam x815.
             lam x816.
               lam x817.
                 tmOpaque (let b14 = matMakeUninit (externalExtArrKind x817.arr) x813 x814
                  in
                  let #var"14" = externalCblasCopy x815 x817.arr 1 b14.arr 1 in
                  let #var"15" = externalCblasScal x815 x816 b14.arr 1 in
                  b14))
      m2
  with
    (st516, x818)
  in
  match p_apply st516 x818 n4 with (st517, x819)
  in
  match
    p_map
      st517
      (lam x820.
         lam x821.
           muli x820 x821)
      m2
  with
    (st518, x822)
  in
  match p_apply st518 x822 n4 with (st519, x823)
  in
  match p_apply st519 x819 x823 with (st520, x824)
  in
  match p_apply st520 x824 mu with (st521, x825)
  in
  match p_apply st521 x825 mtx5 with (st522, qMatrix2)
  in
  let ns = rec19 (length11 hostDistances) hostDistances hostDistances
  in
  match mtxGet st522 2 2 qMatrix2 with (st523, x826)
  in
  match p_map st523 (lam x827.
         negf x827) x826 with (st524, q2)
  in
  match mtxGet st524 1 1 qMatrix2 with (st525, x828)
  in
  match p_map st525 (lam x829.
         negf x829) x828 with (st526, x830)
  in
  match mtxGet st526 3 3 qMatrix2 with (st527, x831)
  in
  match p_map st527 (lam x832.
         negf x832) x831 with (st528, x833)
  in
  match mtxGet st528 2 1 qMatrix2 with (st529, x834)
  in
  match
    p_map
      st529
      (lam x835.
         lam x836.
           divf x835 x836)
      x834
  with
    (st530, x837)
  in
  match p_apply st530 x837 q2 with (st531, x838)
  in
  match mtxGet st531 2 3 qMatrix2 with (st532, x839)
  in
  match
    p_map
      st532
      (lam x840.
         lam x841.
           divf x840 x841)
      x839
  with
    (st533, x842)
  in
  match p_apply st533 x842 q2 with (st534, x843)
  in
  let modelParams2 =
    ModelParams1
      { beta = beta,
        hostMetric =
          mtxCreate (length11 ns) (length1 (get ns (subi 1 1))) (paste0 ns),
        embeddedQMatrix =
          EmbeddedMarkovChainMatrix1
            { totalRates =
                [ x830,
                  q2,
                  x833 ],
              transitionProbs =
                [ [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ],
                  [ x838,
                    p_pure 0.,
                    x843 ],
                  [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ] ],
              mat = qMatrix2 } }
  in
  match input1 with {interactions = #var"X11"}
  in
  match
    postorderTraverse st534 symbiontTree qMatrix2 #var"X11" nHosts1
  with
    (st535, postorderTree)
  in
  let a32 =
    match postorderTree with MsgLeaf carried64
    then
      match carried64 with {outMsg = #var"X16"}
      in
      p_pure #var"X16"
    else match postorderTree with MsgNode carried65
    then
      carried65.outMsg
    else
      let #var"2106" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 48:36-48:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n"
      in
      p_pure (exit 1)
  in
  let b4 = mtxCreate nHosts1 3 (rep (muli 3 nHosts1) 1.) in
  match
    p_map
      st535
      (lam x844.
         match x844 with {m = #var"X12"}
         in
         match b4 with {m = #var"X13"}
         in
         eqi #var"X12" #var"X13")
      a32
  with
    (st536, x845)
  in
  match
    p_map
      st536
      (lam x846.
         match x846 with {n = #var"X14"}
         in
         match b4 with {n = #var"X15"}
         in
         eqi #var"X14" #var"X15")
      a32
  with
    (st537, x847)
  in
  match and1 st537 x845 x847 with (st538, x848)
  in
  match
    p_bind
      st538
      hrmStoreSubmodel
      (hrmInit {})
      (lam st539.
         lam x849.
           match
             match x849 with true
             then
               match
                 p_map
                   st539
                   (lam x850.
                      tmOpaque (let c210 = matMakeUninit (externalExtArrKind x850.arr) x850.m x850.n
                       in
                       let #var"16" = matElemMulNoAlloc x850 b4 c210 in
                       c210))
                   a32
               with
                 (st540, x851)
               in
               (st540, Right
                 x851)
             else
               (st539, Left
                 (DimensionMismatch
                    {}))
           with
             (st541, n3)
           in
           match n3 with Right x852
           then
             p_map
               st541
               (lam x853.
                  Right
                    x853)
               x852
           else match n3 with Left x854
           in
           (st541, p_pure (Left
                x854)))
      x848
  with
    (st542, x855)
  in
  match eitherEither st542 x855 with (st543, rootSamplingProb)
  in
  match
    suggestNodeRep
      st543
      rootSamplingProb
      nHosts1
      (match postorderTree with MsgLeaf carried52
       then
         carried52.label
       else match postorderTree with MsgNode carried53
       then
         carried53.label
       else
         let #var"294" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 49:57-49:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
         in
         exit 1)
  with
    (st544, rootRep)
  in
  match any1 st544 rootRep with (st545, x856)
  in
  match bool2real st545 x856 with (st546, x857)
  in
  let rl = (match postorderTree with MsgLeaf carried62
                     then
                       carried62.label
                     else match postorderTree with MsgNode carried63
                     then
                       carried63.label
                     else
                       let #var"2105" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 51:45-51:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1) in
  let st547 =
    p_weight
      st546
      (hrmStoreNodeSuppWeight rl)
      (lam x866.
         externalLog
           (addf
              x866
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried62
                     then
                       carried62.label
                     else match postorderTree with MsgNode carried63
                     then
                       carried63.label
                     else
                       let #var"2105" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 51:45-51:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1))
                 0.)))
      x857
  in
  let foo3 = {} in
  match
    getRepertoireSamplingDensity st547 rootRep rootSamplingProb
  with
    (st548, x858)
  in
  let rl = (match postorderTree with MsgLeaf carried60
                     then
                       carried60.label
                     else match postorderTree with MsgNode carried61
                     then
                       carried61.label
                     else
                       let #var"2104" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 58:70-58:89>:\nField \'label\' not found\n[0m  logWeight (rootLogModelDensity - rootLogSamplingDensity) * exp(Real([31mpostorderTree.label[0m[0m) * 0.);\n"
                       in
                       exit 1) in
  let st549 =
    p_weight
      st548
      (hrmStoreLikrWeight rl) 
      (lam x865.
         mulf
           (subf
              (negf
                 (log1
                    (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1)))))
              x865)
           (exp1
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried60
                     then
                       carried60.label
                     else match postorderTree with MsgNode carried61
                     then
                       carried61.label
                     else
                       let #var"2104" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 58:70-58:89>:\nField \'label\' not found\n[0m  logWeight (rootLogModelDensity - rootLogSamplingDensity) * exp(Real([31mpostorderTree.label[0m[0m) * 0.);\n"
                       in
                       exit 1))
                 0.)))
      x858
  in
  let foo4 = {} in
  match observationMessage1 st549 rootRep with (st550, newMsg1)
  in
  -- Export root messages
  let st550 = p_export st550 (hrmStoreNodeMsg rl) newMsg1 in
  let st550 = p_export st550 (hrmStorePreorderMsg rl) (p_pure b4) in
  let rootAge =
    match postorderTree with MsgLeaf carried58
    then
      carried58.age
    else match postorderTree with MsgNode carried59
    then
      carried59.age
    else
      let #var"2103" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 65:16-65:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    mtxMul
      st550
      newMsg1
      (match postorderTree with MsgNode x951
       then
         x951.leftKernel
       else
         let #var"295" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 62:31-62:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st551, x859)
  in
  match
    sampleTreeHistory
      st551
      (match postorderTree with MsgNode x901
       then
         x901.left
       else
         let #var"296" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 67:4-67:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
         in
         exit 1)
      nHosts1
      x859
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x911
       then
         x911.leftKernel
       else
         let #var"297" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 67:72-67:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st552, x860)
  in
  match
    mtxMul
      st552
      newMsg1
      (match postorderTree with MsgNode x941
       then
         x941.rightKernel
       else
         let #var"298" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 63:32-63:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st553, x861)
  in
  match
    sampleTreeHistory
      st553
      (match postorderTree with MsgNode x881
       then
         x881.right
       else
         let #var"299" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 71:4-71:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
         in
         exit 1)
      nHosts1
      x861
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x891
       then
         x891.rightKernel
       else
         let #var"2100" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/flat-root-prior-HRM.tppl 71:74-71:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st554, x862)
  in
  match
    p_traverseSeq
      st554
      (lam st555.
         lam x863.
           (st555, x863))
      ""
  with
    (st556, x864)
  in
  -- Set up exports
  let createExport = lam st. lam left. lam right.
    let m = mapEmpty subi in
    let makeDirtyArray = lam st. lam arr.
      p_traverseSeq st (lam st. lam a. (st, a)) arr 
    in
    -- Traverse the tree to extract the node repertoires
    recursive let extractSamples = lam st. lam m. lam hTree.
      match hTree with HistoryLeaf _ then (st, m)
      else match hTree with HistoryNode n in
      match makeDirtyArray st n.repertoire with (st, wrappedRep) in
      let m = mapInsert n.label wrappedRep m in
      match extractSamples st m n.left with (st, m) in
      extractSamples st m n.right
    in
    -- Save the root repertoire
    match makeDirtyArray st rootRep with (st, dRootRep) in
    let m = mapInsert rl dRootRep m in
    -- Save the two subtrees
    match extractSamples st m left with (st, m) in
    match extractSamples st m right with (st, m) in
    let dirtyKeyVal = lam st. lam kv. match kv with (k, v) in p_map st (lam v. (k, v)) v in 
    match p_traverseSeq st dirtyKeyVal (mapToSeq m) with (st, wrappedReps) in
    match p_map st (
      lam mu. lam beta. lam lambda. lam reps.
        -- printLn (join ["Export root rep: [", int2string rootRep1, ", ", int2string rootRep2, "]"]);
        { mu = mu
        , beta = beta
        , lambda = lambda
        , reps = mapFromSeq subi reps 
        }
    ) mu with (st, partres) in
    match p_apply st partres beta with (st, partres) in
    match p_apply st partres lambda with (st, partres) in
    p_apply st partres wrappedReps
  in
  match createExport st556 x860 x862 with (st556, res) in
  p_export
    st556
    hrmStoreExport
    res
  -- Done
