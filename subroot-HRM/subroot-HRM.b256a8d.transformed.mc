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
    lam st985.
      lam a92.
        lam b31.
          p_select
            st985
            (lam x1557.
               match x1557 with true
               then
                 b31
               else
                 p_pure false)
            a92
  in
  let pow = lam x1903.
      lam y2.
        externalPow x1903 y2
  in
  let pow1 =
    lam st984.
      lam x1902.
        lam y1.
          p_map
            st984 (lam x1556.
               externalPow x1902 x1556) y1
  in
  let pow2 =
    lam st982.
      lam x1901.
        lam y.
          match
            p_map
              st982
              (lam x1549.
                 lam x1550.
                   externalPow x1549 x1550)
              x1901
          with
            (st983, x1555)
          in
          p_apply st983 x1555 y
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
      lam x1548.
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
    lam st981.
      lam a75.
        lam i24.
          p_map
            st981
            (lam x1547.
               externalExtArrGet x1547 i24)
            a75
  in
  let extArrOfSeq =
    lam st980.
      lam kind11.
        lam seq6.
          p_map
            st980
            (lam x1546.
               tmOpaque (let len2 = length x1546 in
                let a712 = externalExtArrMakeUninit kind11 len2 in
                recursive
                  let work32 =
                    lam i222.
                      match eqi i222 len2 with true
                      then
                        {}
                      else
                        let #var"2166" = externalExtArrSet a712 i222 (get x1546 i222)
                        in
                        work32 (addi i222 1)
                in
                let #var"2212" = work32 0 in
                a712))
            seq6
  in
  let matErrorToString =
    lam err3.
      match err3 with DimensionMismatch carried79
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
    lam st978.
      lam kind.
        lam m4.
          lam n61.
            match
              p_map
                st978
                (lam x1540.
                   externalExtArrMakeUninit kind (muli m4 x1540))
                n61
            with
              (st979, x1545)
            in
            (st979, { arr = x1545, n = n61, m = m4 })
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
    lam st975.
      lam a66.
        lam i211.
          lam j3.
            match
              p_map
                st975
                (lam x1535.
                   lam x1536.
                     match x1535 with {arr = #var"X70"}
                     in
                     externalExtArrGet #var"X70" x1536)
                a66
            with
              (st976, x1537)
            in
            match
              p_map
                st976
                (lam x1538.
                   match x1538 with {n = #var"X71"}
                   in
                   addi (muli i211 #var"X71") j3)
                a66
            with
              (st977, x1539)
            in
            p_apply st977 x1537 x1539
  in
  let matFromArrExn =
    lam st974.
      lam m3.
        lam n51.
          lam a622.
            p_map
              st974
              (lam x1530.
                 match eqi (muli m3 n51) (externalExtArrLength x1530) with true
                 then
                   { arr = x1530, n = n51, m = m3 }
                 else
                   error "matFromArrExn: dimensions mismatch")
              a622
  in
  let matCopy =
    lam st967.
      lam a60.
        match
          p_map
            st967
            (lam x1509.
               lam x1510.
                 { x1509 with arr = x1510 })
            a60
        with
          (st968, x1515)
        in
        match
          p_map
            st968
            (lam x1516.
               lam x1517.
                 tmOpaque (let b23 = extArrMakeUninit (externalExtArrKind x1516.arr) x1517
                  in
                  let #var"20" = externalCblasCopy x1517 x1516.arr 1 b23 1 in
                  b23))
            a60
        with
          (st969, x1518)
        in
        match
          p_map
            st969
            (lam x1519.
               lam x1520.
                 match x1519 with {m = #var"X69"}
                 in
                 muli #var"X69" x1520)
            a60
        with
          (st970, x1525)
        in
        match
          p_map st970 (lam x1526.
               x1526.n) a60
        with
          (st971, x1527)
        in
        match p_apply st971 x1525 x1527 with (st972, x1528)
        in
        match p_apply st972 x1518 x1528 with (st973, x1529)
        in
        p_apply st973 x1515 x1529
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
    lam st953.
      lam a48.
        lam b12.
          match
            p_map st953 (lam x1476.
                 x1476.n) a48
          with
            (st954, x1477)
          in
          match
            p_map
              st954
              (lam x1478.
                 lam x1479.
                   lam st955.
                     match
                       match eqi x1478 x1479 with true
                       then
                         match
                           p_map
                             st955
                             (lam x1480.
                                x1480.m)
                             a48
                         with
                           (st956, x1485)
                         in
                         match
                           p_map
                             st956
                             (lam x1486.
                                lam x1487.
                                  lam x1488.
                                    lam x1489.
                                      tmOpaque (let c110 = matMakeUninit (externalExtArrKind x1489.arr) x1486 x1487
                                       in
                                       let #var"13" =
                                         externalCblasGemm
                                           cblasRowMajor
                                           cblasNoTrans
                                           cblasNoTrans
                                           x1486
                                           x1487
                                           x1478
                                           1.
                                           x1488.arr
                                           x1478
                                           x1489.arr
                                           x1487
                                           0.
                                           c110.arr
                                           x1487
                                       in
                                       c110))
                             x1485
                         with
                           (st957, x1490)
                         in
                         match
                           p_map
                             st957
                             (lam x1491.
                                x1491.n)
                             b12
                         with
                           (st958, x1492)
                         in
                         match p_apply st958 x1490 x1492 with (st959, x1493)
                         in
                         match p_apply st959 x1493 a48 with (st960, x1494)
                         in
                         match p_apply st960 x1494 b12 with (st961, x1495)
                         in
                         (st961, Right
                           x1495)
                       else
                         (st955, Left
                           (DimensionMismatch
                              {}))
                     with
                       (st962, n6)
                     in
                     match n6 with Right x1496
                     then
                       p_map
                         st962
                         (lam x1497.
                            Right
                              x1497)
                         x1496
                     else match n6 with Left x1498
                     in
                     (st962, p_pure (Left
                          x1498)))
              x1477
          with
            (st963, x1499)
          in
          match
            p_map st963 (lam x1500.
                 x1500.m) b12
          with
            (st964, x1505)
          in
          match
            p_subApply st964 simpleStoreSubmodel (simpleInit {}) x1499 x1505
          with
            (st965, x1506)
          in
          match p_join st965 x1506 with (st966, x1507)
          in
          p_map
            st966
            (lam x1508.
               match x1508 with Left carried77
               then
                 error (matErrorToString carried77)
               else match x1508 with Right carried78
               in
               carried78)
            x1507
  in
  let exp1 = lam x1751.
      externalExp x1751 in
  let log1 = lam x1742.
      externalLog x1742 in
  let log11 =
    lam st952.
      lam x1741.
        p_map st952 (lam x1475.
             externalLog x1475) x1741
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
        let i118 = subi count1 1 in
        match geqi i118 0 with true
        then
          rec3 elem1 (subi i118 1) (cons (anon elem1 i118) "")
        else
          ""
  in
  let paste0 =
    lam l52.
      match l52 with [ _ ] ++ _
      then
        match splitAt l52 1 with {#label"1" = x1470}
        in
        rec2 (concat "" (get l52 0)) x1470
      else match l52 with ""
      in
      ""
  in
  let paste01 =
    lam st946.
      lam l51.
        match l51 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st946
              (lam st947.
                 lam x1464.
                   (st947, x1464))
              ""
          with
            (st948, x1465)
          in
          match p_map st948 concat x1465 with (st949, x1466)
          in
          match p_apply st949 x1466 (get l51 0) with (st950, x1467)
          in
          match splitAt l51 1 with {#label"1" = x1468}
          in
          rec22 st950 x1467 x1468
        else match l51 with ""
        in
        p_traverseSeq
          st946
          (lam st951.
             lam x1469.
               (st951, x1469))
          ""
  in
  let paste02 =
    lam st940.
      lam l5.
        match l5 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st940
              (lam st941.
                 lam x1458.
                   (st941, x1458))
              ""
          with
            (st942, x1459)
          in
          match p_map st942 concat x1459 with (st943, x1460)
          in
          match p_apply st943 x1460 (get l5 0) with (st944, x1461)
          in
          match splitAt l5 1 with {#label"1" = x1462}
          in
          rec24 st944 x1461 x1462
        else match l5 with ""
        in
        p_traverseSeq
          st940
          (lam st945.
             lam x1463.
               (st945, x1463))
          ""
  in
  let slice =
    lam l4.
      lam first2.
        lam last.
          subsequence l4 (subi first2 1) (subi last first2)
  in
  let length1 = lam l35.
      length l35 in
  let length11 = lam l34.
      length l34 in
  let length12 = lam l33.
      length l33 in
  let length13 = lam l32.
      length l32 in
  let length14 = lam st939.
      lam l31.
        p_map st939 length l31
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
    lam st937.
      lam s81.
        match s81 with [ _ ] ++ _
        then
          match
            p_map
              st937 (lam x1455.
                 addf 0. x1455) (get s81 0)
          with
            (st938, x1456)
          in
          match splitAt s81 1 with {#label"1" = x1457}
          in
          rec26 st938 x1456 x1457
        else match s81 with ""
        in
        (st937, p_pure 0.)
  in
  let anon1 =
    lam x1449.
      lam x1450.
        lam x1454.
          match x1454 with true
          then
            snoc x1449 (addi x1450 1)
          else
            x1449
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
                    simpleStoreSubmodel
                    (simpleInit {})
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
    lam st934.
      lam s62.
        match s62 with [ e24 ] ++ rest3
        then
          match
            p_map
              st934
              (lam x1446.
                 match x1446 with true
                 then
                   snoc "" (addi 0 1)
                 else
                   "")
              e24
          with
            (st935, x1447)
          in
          work1 st935 x1447 (addi 0 1) rest3
        else
          p_traverseSeq
            st934
            (lam st936.
               lam x1448.
                 (st936, x1448))
            ""
  in
  let whichTrue2 =
    lam st933.
      lam s61.
        p_map
          st933
          (lam x1445.
             match x1445 with [ e23 ] ++ rest2
             then
               work (anon1 "" 0 e23) (addi 0 1) rest2
             else
               "")
          s61
  in
  let bool2real =
    lam st932.
      lam v.
        p_map
          st932
          (lam x1440.
             match x1440 with true
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
                     let #var"2165" = externalExtArrSet a711 i221 (get data i221) in
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
    lam st931.
      lam row13.
        lam col2.
          lam mtx72.
            matGetExn1 st931 mtx72 (subi row13 1) (subi col2 1)
  in
  let mtxGet1 =
    lam st925.
      lam row12.
        lam col1.
          lam mtx71.
            match
              p_map
                st925
                (lam x1425.
                   lam x1426.
                     match x1425 with {arr = #var"X51"}
                     in
                     externalExtArrGet #var"X51" x1426)
                mtx71
            with
              (st926, x1427)
            in
            match
              p_map st926 (lam x1428.
                   subi x1428 1) row12
            with
              (st927, x1429)
            in
            match
              p_map
                st927
                (lam x1430.
                   lam x1435.
                     addi (muli x1430 x1435) (subi col1 1))
                x1429
            with
              (st928, x1436)
            in
            match
              p_map st928 (lam x1437.
                   x1437.n) mtx71
            with
              (st929, x1438)
            in
            match p_apply st929 x1436 x1438 with (st930, x1439)
            in
            p_apply st930 x1427 x1439
  in
  let mtxGet2 =
    lam st917.
      lam row11.
        lam col.
          lam mtx7.
            match
              p_map
                st917
                (lam x1406.
                   lam x1407.
                     match x1406 with {arr = #var"X50"}
                     in
                     externalExtArrGet #var"X50" x1407)
                mtx7
            with
              (st918, x1408)
            in
            match
              p_map st918 (lam x1409.
                   subi x1409 1) row11
            with
              (st919, x1410)
            in
            match
              p_map
                st919
                (lam x1411.
                   lam x1412.
                     lam x1413.
                       addi (muli x1411 x1412) x1413)
                x1410
            with
              (st920, x1414)
            in
            match
              p_map st920 (lam x1415.
                   x1415.n) mtx7
            with
              (st921, x1416)
            in
            match p_apply st921 x1414 x1416 with (st922, x1417)
            in
            match
              p_map st922 (lam x1418.
                   subi x1418 1) col
            with
              (st923, x1419)
            in
            match p_apply st923 x1417 x1419 with (st924, x1420)
            in
            p_apply st924 x1408 x1420
  in
  let anon2 =
    lam new5.
      lam mtx65.
        lam row5.
          lam x1404.
            lam x1405.
              match new5 with {arr = #var"X48"}
              in
              match new5 with {n = #var"X49"}
              in
              externalExtArrSet
                #var"X48"
                (addi (muli 0 #var"X49") x1404)
                (matGetExn mtx65 (subi row5 1) (subi x1405 1))
  in
  let anon3 =
    lam st914.
      lam new4.
        lam mtx64.
          lam row4.
            lam x1397.
              lam x1398.
                match new4 with {arr = #var"X46"}
                in
                match
                  p_map
                    st914
                    (lam x1399.
                       lam x1400.
                         externalExtArrSet x1399 x1400 (matGetExn mtx64 (subi row4 1) (subi x1398 1)))
                    #var"X46"
                with
                  (st915, x1401)
                in
                match new4 with {n = #var"X47"}
                in
                match
                  p_map
                    st915
                    (lam x1402.
                       addi (muli 0 x1402) x1397)
                    #var"X47"
                with
                  (st916, x1403)
                in
                p_apply st916 x1401 x1403
  in
  let anon4 =
    lam st908.
      lam new3.
        lam mtx63.
          lam row3.
            lam x1384.
              lam x1385.
                match new3 with {arr = #var"X42"}
                in
                match
                  p_map
                    st908
                    (lam x1386.
                       lam x1387.
                         lam x1388.
                           externalExtArrSet x1386 x1387 x1388)
                    #var"X42"
                with
                  (st909, x1389)
                in
                match new3 with {n = #var"X43"}
                in
                match
                  p_map
                    st909
                    (lam x1390.
                       addi (muli 0 x1390) x1384)
                    #var"X43"
                with
                  (st910, x1391)
                in
                match p_apply st910 x1389 x1391 with (st911, x1392)
                in
                match
                  p_map st911 (lam x1393.
                       subi x1393 1) row3
                with
                  (st912, x1394)
                in
                match
                  p_map
                    st912
                    (lam x1395.
                       match mtx63 with {arr = #var"X44"}
                       in
                       match mtx63 with {n = #var"X45"}
                       in
                       externalExtArrGet #var"X44" (addi (muli x1395 #var"X45") (subi x1385 1)))
                    x1394
                with
                  (st913, x1396)
                in
                p_apply st913 x1392 x1396
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
          match mtx62 with {arr = #var"X41"}
          in
          let new2 =
            matMakeUninit (externalExtArrKind #var"X41") 1 (length cols2)
          in
          let #var"2412" = rec1 new2 mtx62 row2 0 cols2 in
          let #var"102" = {} in
          new2
  in
  let mtxRowCols1 =
    lam st898.
      lam mtx61.
        lam row1.
          lam cols1.
            match mtx61 with {arr = #var"X40"}
            in
            match p_map st898 length cols1 with (st899, x1375)
            in
            match
              matMakeUninit1 st899 (externalExtArrKind #var"X40") 1 x1375
            with
              (st900, new1)
            in
            match
              p_bind
                st900
                simpleStoreSubmodel
                (simpleInit {})
                (lam st901.
                   lam x1376.
                     match
                       match x1376 with [ _,
                           _ ] ++ _
                       then
                         match anon3 st901 new1 mtx61 row1 0 (get x1376 0) with (st902, x1377)
                         in
                         match splitAt x1376 1 with {#label"1" = x1378}
                         in
                         match rec11 st902 new1 mtx61 row1 (addi 0 1) x1378 with (st903, x1379)
                         in
                         (st903, cons x1377 x1379)
                       else match x1376 with [ e22 ]
                       then
                         match splitAt x1376 1 with {#label"1" = x1380}
                         in
                         let slice21 = x1380 in
                         match anon3 st901 new1 mtx61 row1 0 e22 with (st904, x1381)
                         in
                         (st904, [ x1381 ])
                       else match x1376 with ""
                       in
                       (st901, "")
                     with
                       (st905, x1382)
                     in
                     p_traverseSeq
                       st905
                       (lam st906.
                          lam x1383.
                            (st906, x1383))
                       x1382)
                cols1
            with
              (st907, #var"2411")
            in
            let #var"101" = {} in
            (st907, new1)
  in
  let mtxRowCols2 =
    lam st888.
      lam mtx6.
        lam row.
          lam cols.
            match mtx6 with {arr = #var"X39"}
            in
            match p_map st888 length cols with (st889, x1366)
            in
            match
              matMakeUninit1 st889 (externalExtArrKind #var"X39") 1 x1366
            with
              (st890, new)
            in
            match
              p_bind
                st890
                simpleStoreSubmodel
                (simpleInit {})
                (lam st891.
                   lam x1367.
                     match
                       match x1367 with [ _,
                           _ ] ++ _
                       then
                         match anon4 st891 new mtx6 row 0 (get x1367 0) with (st892, x1368)
                         in
                         match splitAt x1367 1 with {#label"1" = x1369}
                         in
                         match rec12 st892 new mtx6 row (addi 0 1) x1369 with (st893, x1370)
                         in
                         (st893, cons x1368 x1370)
                       else match x1367 with [ e21 ]
                       then
                         match splitAt x1367 1 with {#label"1" = x1371}
                         in
                         let slice20 = x1371 in
                         match anon4 st891 new mtx6 row 0 e21 with (st894, x1372)
                         in
                         (st894, [ x1372 ])
                       else match x1367 with ""
                       in
                       (st891, "")
                     with
                       (st895, x1373)
                     in
                     p_traverseSeq
                       st895
                       (lam st896.
                          lam x1374.
                            (st896, x1374))
                       x1373)
                cols
            with
              (st897, #var"2410")
            in
            let #var"10" = {} in
            (st897, new)
  in
  let mtxSclrMul =
    lam st880.
      lam scalar.
        lam mtx51.
          match
            p_map st880 (lam x1353.
                 x1353.m) mtx51
          with
            (st881, m21)
          in
          match
            p_map st881 (lam x1354.
                 x1354.n) mtx51
          with
            (st882, n41)
          in
          match
            p_map
              st882
              (lam x1355.
                 lam x1356.
                   lam x1357.
                     lam x1358.
                       tmOpaque (let b141 = matMakeUninit (externalExtArrKind x1358.arr) x1355 x1356
                        in
                        let #var"141" = externalCblasCopy x1357 x1358.arr 1 b141.arr 1
                        in
                        let #var"151" = externalCblasScal x1357 scalar b141.arr 1 in
                        b141))
              m21
          with
            (st883, x1359)
          in
          match p_apply st883 x1359 n41 with (st884, x1360)
          in
          match
            p_map
              st884
              (lam x1361.
                 lam x1362.
                   muli x1361 x1362)
              m21
          with
            (st885, x1363)
          in
          match p_apply st885 x1363 n41 with (st886, x1364)
          in
          match p_apply st886 x1360 x1364 with (st887, x1365)
          in
          p_apply st887 x1365 mtx51
  in
  let mtxTrans =
    lam st879.
      lam mtx4.
        p_map
          st879
          (lam x1352.
             tmOpaque (let b17 = matMakeUninit (externalExtArrKind x1352.arr) x1352.n x1352.m
              in
              let #var"17" = matTranposeNoAlloc x1352 b17 in
              b17))
          mtx4
  in
  let anon5 =
    lam st874.
      lam mtx121.
        lam mtx241.
          lam x1343.
            match
              p_map
                st874
                (lam x1344.
                   lam x1345.
                     match x1344 with {arr = #var"X38"}
                     in
                     externalExtArrSet #var"X38" x1343 x1345)
                mtx241
            with
              (st875, x1346)
            in
            match
              p_map st875 (lam x1347.
                   x1347.arr) mtx121
            with
              (st876, x1348)
            in
            match extArrGetExn st876 x1348 x1343 with (st877, x1349)
            in
            match
              p_map
                st877
                (lam x1350.
                   match gtf x1350 0. with true
                   then
                     x1350
                   else
                     0.)
                x1349
            with
              (st878, x1351)
            in
            p_apply st878 x1346 x1351
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
    lam st847.
      lam mtx92.
        lam mtx213.
          lam x1291.
            lam x1292.
              match
                p_map
                  st847
                  (lam x1293.
                     lam x1294.
                       lam x1295.
                         match x1293 with {arr = #var"X36"}
                         in
                         externalExtArrSet #var"X36" x1294 x1295)
                  mtx213
              with
                (st848, x1296)
              in
              match
                p_map
                  st848
                  (lam x1297.
                     match x1297 with {n = #var"X37"}
                     in
                     addi (muli x1291 #var"X37") x1292)
                  mtx213
              with
                (st849, x1298)
              in
              match p_apply st849 x1296 x1298 with (st850, x1299)
              in
              match matGetExn1 st850 mtx92 x1291 x1292 with (st851, x1300)
              in
              match
                p_map
                  st851
                  (lam x1301.
                     lam x1302.
                       divf x1301 x1302)
                  x1300
              with
                (st852, x1303)
              in
              match
                p_map st852 (lam x1304.
                     x1304.m) mtx92
              with
                (st853, x1305)
              in
              match
                p_map st853 (lam x1306.
                     subi x1306 1) x1305
              with
                (st854, x1307)
              in
              match
                p_map
                  st854
                  (lam x1308.
                     match geqi x1308 0 with true
                     then
                       rec3 1. (subi x1308 1) (cons (anon 1. x1308) "")
                     else
                       "")
                  x1307
              with
                (st855, x1309)
              in
              match extArrOfSeq st855 extArrKindFloat64 x1309 with (st856, a62)
              in
              match
                p_map st856 (lam x1310.
                     x1310.m) mtx92
              with
                (st857, x1311)
              in
              match
                p_map
                  st857
                  (lam x1312.
                     lam x1313.
                       lam st858.
                         let x1314 =
                           match eqi (muli x1312 1) x1313 with true
                           then
                             { arr = a62, n = 1, m = x1312 }
                           else
                             let x1319 = error "matFromArrExn: dimensions mismatch" in
                             match x1319 with {arr = x1320}
                             in
                             match x1319 with {n = x1321}
                             in
                             match x1319 with {m = x1322}
                             in
                             { arr = p_pure x1320, n = x1321, m = x1322 }
                         in
                         match x1314 with {arr = x1315}
                         in
                         p_map
                           st858
                           (lam x1316.
                              match x1314 with {n = x1317}
                              in
                              match x1314 with {m = x1318}
                              in
                              { arr = x1316, n = x1317, m = x1318 })
                           x1315)
                  x1311
              with
                (st859, x1323)
              in
              match
                p_map
                  st859
                  (lam x1324.
                     externalExtArrLength x1324)
                  a62
              with
                (st860, x1325)
              in
              match
                p_subApply st860 simpleStoreSubmodel (simpleInit {}) x1323 x1325
              with
                (st861, x1326)
              in
              match p_join st861 x1326 with (st862, x1327)
              in
              match matMulExn st862 mtx92 x1327 with (st863, x1328)
              in
              match
                p_map
                  st863
                  (lam x1329.
                     match x1329 with {arr = field24, n = field25, m = field26}
                     in
                     field24)
                  x1328
              with
                (st864, a69)
              in
              match
                p_map
                  st864
                  (lam x1330.
                     externalExtArrLength x1330)
                  a69
              with
                (st865, x1331)
              in
              match
                p_map st865 (lam x1332.
                     subi x1332 1) x1331
              with
                (st866, x1333)
              in
              match
                p_bind
                  st866
                  simpleStoreSubmodel
                  (simpleInit {})
                  (lam st867.
                     lam x1334.
                       match
                         match geqi x1334 0 with true
                         then
                           match
                             p_map
                               st867
                               (lam x1335.
                                  externalExtArrGet x1335 x1334)
                               a69
                           with
                             (st868, x1336)
                           in
                           rec31 st868 a69 (subi x1334 1) (cons x1336 "")
                         else
                           (st867, "")
                       with
                         (st869, x1337)
                       in
                       p_traverseSeq
                         st869
                         (lam st870.
                            lam x1338.
                              (st870, x1338))
                         x1337)
                  x1333
              with
                (st871, x1339)
              in
              match
                p_map
                  st871 (lam x1340.
                     get x1340 x1291) x1339
              with
                (st872, x1341)
              in
              match p_apply st872 x1303 x1341 with (st873, x1342)
              in
              p_apply st873 x1299 x1342
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
    lam st843.
      lam mtx91.
        lam mtx212.
          lam x1287.
            match
              p_map st843 (lam x1288.
                   x1288.n) mtx91
            with
              (st844, x1289)
            in
            p_subMap
              st844
              simpleStoreSubmodel
              (simpleInit {})
              (lam x1290.
                 lam st845.
                   match geqi 0 x1290 with true
                   then
                     (st845, {})
                   else match anon6 st845 mtx91 mtx212 #frozen"x1287" 0 with (st846, #var"6")
                   in
                   rec41 st846 mtx91 mtx212 #frozen"x1287" x1290 (addi 0 1))
              x1289
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
    lam st826.
      lam mtx3.
        match
          p_map
            st826
            (lam x1268.
               lam x1269.
                 match x1268 with {m = #var"X31"}
                 in
                 match eqi #var"X31" x1269 with true
                 then
                   match x1268 with {m = #var"X32"}
                   in
                   match x1268 with {n = #var"X33"}
                   in
                   match x1268 with {arr = #var"X34"}
                   in
                   Right
                     { x1268 with arr = externalMatExp #var"X32" #var"X33" #var"X34" }
                 else
                   Left
                     (NotSquare
                        {}))
            mtx3
        with
          (st827, x1270)
        in
        match
          p_map st827 (lam x1272.
               x1272.n) mtx3
        with
          (st828, x1273)
        in
        match p_apply st828 x1270 x1273 with (st829, x1274)
        in
        match
          p_map
            st829
            (lam x1275.
               match x1275 with Left carried74
               then
                 match carried74 with NotSquare carried75
                 in
                 error "Not square"
               else match x1275 with Right carried76
               in
               carried76)
            x1274
        with
          (st830, mtx12)
        in
        match matCopy st830 mtx12 with (st831, mtx24)
        in
        match
          p_map
            st831
            (lam x1276.
               lam x1277.
                 match x1276 with {m = #var"X35"}
                 in
                 muli #var"X35" x1277)
            mtx12
        with
          (st832, x1278)
        in
        match
          p_map st832 (lam x1279.
               x1279.n) mtx12
        with
          (st833, x1280)
        in
        match p_apply st833 x1278 x1280 with (st834, x1282)
        in
        match
          p_subMap
            st834
            simpleStoreSubmodel
            (simpleInit {})
            (lam x1283.
               lam st835.
                 match geqi 0 x1283 with true
                 then
                   (st835, {})
                 else match anon5 st835 mtx12 mtx24 0 with (st836, #var"4")
                 in
                 rec4 st836 mtx12 mtx24 x1283 (addi 0 1))
            x1282
        with
          (st837, #var"12")
        in
        let mtx9 = mtx24 in
        match matCopy st837 mtx9 with (st838, mtx211)
        in
        match
          p_map st838 (lam x1284.
               x1284.m) mtx9
        with
          (st839, x1285)
        in
        match
          p_subMap
            st839
            simpleStoreSubmodel
            (simpleInit {})
            (lam x1286.
               lam st840.
                 match geqi 0 x1286 with true
                 then
                   (st840, {})
                 else match anon7 st840 mtx9 mtx211 0 with (st841, #var"5")
                 in
                 rec42 st841 mtx9 mtx211 x1286 (addi 0 1))
            x1285
        with
          (st842, #var"11")
        in
        (st842, mtx211)
  in
  let mtxMul =
    lam st825.
      lam a33.
        lam b5.
          matMulExn st825 a33 b5
  in
  let eitherEither =
    lam st824.
      lam e31.
        p_map
          st824
          (lam x1267.
             match x1267 with Left carried72
             then
               error (matErrorToString carried72)
             else match x1267 with Right carried73
             in
             carried73)
          e31
  in
  let mtxElemMul =
    lam st811.
      lam a321.
        lam b41.
          match
            p_map
              st811
              (lam x1244.
                 lam x1245.
                   match x1244 with {m = #var"X29"}
                   in
                   eqi #var"X29" x1245)
              a321
          with
            (st812, x1246)
          in
          match
            p_map st812 (lam x1247.
                 x1247.m) b41
          with
            (st813, x1248)
          in
          match p_apply st813 x1246 x1248 with (st814, x1249)
          in
          match
            p_map
              st814
              (lam x1250.
                 lam x1251.
                   match x1250 with {n = #var"X30"}
                   in
                   eqi #var"X30" x1251)
              a321
          with
            (st815, x1252)
          in
          match
            p_map st815 (lam x1253.
                 x1253.n) b41
          with
            (st816, x1254)
          in
          match p_apply st816 x1252 x1254 with (st817, x1255)
          in
          match and1 st817 x1249 x1255 with (st818, x1256)
          in
          match
            p_bind
              st818
              simpleStoreSubmodel
              (simpleInit {})
              (lam st819.
                 lam x1257.
                   match
                     match x1257 with true
                     then
                       match
                         p_map
                           st819
                           (lam x1258.
                              lam x1259.
                                tmOpaque (let c211 = matMakeUninit (externalExtArrKind x1258.arr) x1258.m x1258.n
                                 in
                                 let #var"161" = matElemMulNoAlloc x1258 x1259 c211 in
                                 c211))
                           a321
                       with
                         (st820, x1260)
                       in
                       match p_apply st820 x1260 b41 with (st821, x1262)
                       in
                       (st821, Right
                         x1262)
                     else
                       (st819, Left
                         (DimensionMismatch
                            {}))
                   with
                     (st822, n5)
                   in
                   match n5 with Right x1263
                   then
                     p_map
                       st822
                       (lam x1264.
                          Right
                            x1264)
                       x1263
                   else match n5 with Left x1265
                   in
                   (st822, p_pure (Left
                        x1265)))
              x1256
          with
            (st823, x1266)
          in
          eitherEither st823 x1266
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
    lam st803.
      lam mtx2.
        match mtx2 with {n = #var"X20"}
        in
        match
          p_map
            st803
            (lam x1232.
               match mtx2 with {m = #var"X21"}
               in
               muli #var"X21" x1232)
            #var"X20"
        with
          (st804, x1233)
        in
        match
          p_bind
            st804
            simpleStoreSubmodel
            (simpleInit {})
            (lam st805.
               lam x1234.
                 match lti 0 x1234 with true
                 then
                   match mtx2 with {arr = #var"X22"}
                   in
                   match extArrGetExn st805 #var"X22" 0 with (st806, x1235)
                   in
                   match
                     p_map
                       st806
                       (lam x1236.
                          addf 0. x1236)
                       x1235
                   with
                     (st807, x1237)
                   in
                   work21 st807 x1234 mtx2 (addi 0 1) x1237
                 else
                   (st805, p_pure 0.))
            x1233
        with
          (st808, x1238)
        in
        match
          p_map
            st808
            (lam x1239.
               lam x1240.
                 divf x1239 x1240)
            x1238
        with
          (st809, x1241)
        in
        match mtx2 with {n = #var"X23"}
        in
        match
          p_map
            st809
            (lam x1242.
               match mtx2 with {m = #var"X24"}
               in
               int2float (muli #var"X24" x1242))
            #var"X23"
        with
          (st810, x1243)
        in
        p_apply st810 x1241 x1243
  in
  let anon8 =
    lam x1230.
      lam x1231.
        match eqi (addi x1230 1) (addi x1231 1) with true
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
      lam c72.
        let i117 = subi l64 1 in
        match geqi i117 0 with true
        then
          rec32 c72 (subi i117 1) (cons (anon8 c72 i117) "")
        else
          ""
  in
  let anon9 =
    lam x1229.
      match
        match geqi x1229 0 with true
        then
          leqi x1229 2
        else
          false
      with
        true
      then
        create1 3 #frozen"x1229"
      else
        rep 3 1.
  in
  let anon10 =
    lam st802.
      lam x1227.
        p_map
          st802
          (lam x1228.
             match
               match geqi x1228 0 with true
               then
                 leqi x1228 2
               else
                 false
             with
               true
             then
               create1 3 x1228
             else
               rep 3 1.)
          x1227
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
    lam st793.
      lam obsRepertoire.
        match rec5 st793 obsRepertoire with (st794, s229)
        in
        match
          match s229 with [ _ ] ++ _
          then
            match
              p_traverseSeq
                st794
                (lam st795.
                   lam x1219.
                     (st795, x1219))
                ""
            with
              (st796, x1220)
            in
            match p_map st796 concat x1220 with (st797, x1221)
            in
            match p_apply st797 x1221 (get s229 0) with (st798, x1222)
            in
            match splitAt s229 1 with {#label"1" = x1223}
            in
            rec23 st798 x1222 x1223
          else match s229 with ""
          in
          p_traverseSeq
            st794
            (lam st799.
               lam x1224.
                 (st799, x1224))
            ""
        with
          (st800, x1225)
        in
        match extArrOfSeq st800 extArrKindFloat64 x1225 with (st801, x1226)
        in
        matFromArrExn st801 (length13 obsRepertoire) 3 x1226
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
  let anon11 = lam x1218.
      addi x1218 1 in
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
    lam st792.
      lam mtx1.
        lam i101.
          lam x1217.
            mtxGet st792 i101 x1217 mtx1
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
    lam st789.
      lam s72.
        lam x1212.
          match
            p_map
              st789
              (lam x1213.
                 lam x1214.
                   divf x1213 x1214)
              x1212
          with
            (st790, x1215)
          in
          match seqSumReal st790 s72 with (st791, x1216)
          in
          p_apply st791 x1215 x1216
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
    lam st787.
      lam mtx.
        lam i10.
          let i116 = subi (addi (subi 3 1) 1) 1 in
          match
            rec6
              st787
              mtx
              i10
              (match geqi i116 0 with true
               then
                 rec33 (subi i116 1) (cons (anon11 i116) "")
               else
                 "")
          with
            (st788, s71)
          in
          rec7 st788 s71 s71
  in
  let anon14 =
    lam st784.
      lam samplingProb11.
        lam x1208.
          lam x1209.
            match
              hostMsgToProb st784 samplingProb11 (addi x1208 1)
            with
              (st785, param6)
            in
            p_bind
              st785
              simpleStoreSubmodel
              (simpleInit {})
              (lam st786.
                 lam x1210.
                   match
                     match leqi 0 x1210 with true
                     then
                       lti x1210 (length param6)
                     else
                       false
                   with
                     true
                   then
                     log11 st786 (get param6 (subi (addi x1210 1) 1))
                   else
                     (st786, p_pure (log1 0.)))
              x1209
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
  recursive
    let rec27 =
      lam st64.
        lam c25.
          lam acc7.
            lam s27.
              match s27 with [ _ ] ++ _
              then
                match
                  p_map
                    st64
                    (lam x66.
                       lam x67.
                         mulf x66 x67)
                    acc7
                with
                  (st65, x68)
                in
                match hostMsgToProb st65 c25 (get s27 0) with (st66, x69)
                in
                match
                  p_map
                    st66
                    (lam x70.
                       subf 1. x70)
                    (get x69 (subi 3 1))
                with
                  (st67, x71)
                in
                match p_apply st67 x68 x71 with (st68, x72)
                in
                match splitAt s27 1 with {#label"1" = x73}
                in
                rec27 st68 c25 x72 x73
              else match s27 with ""
              in
              (st64, acc7)
  in
  let anon15 = lam x1207.
      addi x1207 1 in
  recursive
    let rec34 =
      lam i14.
        lam acc15.
          match geqi i14 0 with true
          then
            rec34 (subi i14 1) (cons (anon15 i14) acc15)
          else
            acc15
  in
  let getRepertoireSamplingDensity =
    lam st775.
      lam x1611.
        lam samplingProb1.
          match rec13 st775 samplingProb1 0 x1611 with (st776, x1190)
          in
          match seqSumReal st776 x1190 with (st777, x1193)
          in
          match
            p_map
              st777
              (lam x1194.
                 lam x1195.
                   subf x1194 x1195)
              x1193
          with
            (st778, x1196)
          in
          let i115 = subi (addi (subi (length13 x1611) 1) 1) 1 in
          let s228 =
            match geqi i115 0 with true
            then
              rec34 (subi i115 1) (cons (anon15 i115) "")
            else
              ""
          in
          match
            match s228 with [ _ ] ++ _
            then
              match hostMsgToProb st778 samplingProb1 (get s228 0) with (st779, x1197)
              in
              match
                p_map
                  st779
                  (lam x1198.
                     mulf 1. (subf 1. x1198))
                  (get x1197 (subi 3 1))
              with
                (st780, x1199)
              in
              match splitAt s228 1 with {#label"1" = x1200}
              in
              rec27 st780 samplingProb1 x1199 x1200
            else match s228 with ""
            in
            (st778, p_pure 1.)
          with
            (st781, x1203)
          in
          match
            p_map st781 (lam x1204.
                 subf 1. x1204) x1203
          with
            (st782, x1205)
          in
          match log11 st782 x1205 with (st783, x1206)
          in
          p_apply st783 x1196 x1206
  in
  let anon16 =
    lam x1188.
      lam x1189.
        match eqi x1189 2 with true
        then
          addi x1188 1
        else
          x1188
  in
  recursive
    let rec28 =
      lam acc8.
        lam s28.
          match s28 with [ _ ] ++ _
          then
            match splitAt s28 1 with {#label"1" = x74}
            in
            rec28 (anon16 acc8 (get s28 0)) x74
          else match s28 with ""
          in
          acc8
    let rec29 =
      lam st69.
        lam acc9.
          lam s29.
            match s29 with [ _ ] ++ _
            then
              match
                p_bind
                  st69
                  simpleStoreSubmodel
                  (simpleInit {})
                  (lam st70.
                     lam x75.
                       match eqi x75 2 with true
                       then
                         p_map
                           st70 (lam x76.
                              addi x76 1) acc9
                       else
                         (st70, acc9))
                  (get s29 0)
              with
                (st71, x77)
              in
              match splitAt s29 1 with {#label"1" = x78}
              in
              rec29 st71 x77 x78
            else match s29 with ""
            in
            (st69, acc9)
  in
  let count2s =
    lam st773.
      lam repertoire21.
        match repertoire21 with [ _ ] ++ _
        then
          match
            p_map
              st773
              (lam x1185.
                 match eqi x1185 2 with true
                 then
                   addi 0 1
                 else
                   0)
              (get repertoire21 0)
          with
            (st774, x1186)
          in
          match splitAt repertoire21 1 with {#label"1" = x1187}
          in
          rec29 st774 x1186 x1187
        else match repertoire21 with ""
        in
        (st773, p_pure 0)
  in
  let updateRepertoire =
    lam st755.
      lam currRep81.
        lam event31.
          lam nhosts71.
            match
              p_map
                st755
                (lam x1159.
                   match x1159 with Event1 x1592
                   then
                     x1592.host
                   else
                     let #var"2163" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event31
            with
              (st756, hostIndex42)
            in
            match
              p_traverseSeq
                st756
                (lam st757.
                   lam x1160.
                     (st757, x1160))
                currRep81
            with
              (st758, x1163)
            in
            match
              p_map
                st758
                (lam x1164.
                   subsequence x1164 (subi 1 1))
                x1163
            with
              (st759, x1165)
            in
            match
              p_map
                st759
                (lam x1166.
                   subi x1166 1)
                hostIndex42
            with
              (st760, x1167)
            in
            match p_apply st760 x1165 x1167 with (st761, x1168)
            in
            match
              p_map
                st761
                (lam x1169.
                   match x1169 with Event1 x1582
                   then
                     x1582.toState
                   else
                     let #var"2164" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event31
            with
              (st762, x1170)
            in
            match
              p_traverseSeq
                st762
                (lam st763.
                   lam x1171.
                     (st763, x1171))
                [ x1170 ]
            with
              (st764, x1172)
            in
            match
              p_map
                st764
                (lam x1173.
                   addi x1173 1)
                hostIndex42
            with
              (st765, first1)
            in
            match
              p_traverseSeq
                st765
                (lam st766.
                   lam x1174.
                     (st766, x1174))
                currRep81
            with
              (st767, x1175)
            in
            match p_map st767 subsequence x1175 with (st768, x1176)
            in
            match
              p_map st768 (lam x1177.
                   subi x1177 1) first1
            with
              (st769, x1178)
            in
            match p_apply st769 x1176 x1178 with (st770, x1179)
            in
            match
              p_map
                st770
                (lam x1180.
                   subi (addi nhosts71 1) x1180)
                first1
            with
              (st771, x1183)
            in
            match p_apply st771 x1179 x1183 with (st772, x1184)
            in
            paste02
              st772
              [ x1168,
                x1172,
                x1184 ]
  in
  let updateRepertoire1 =
    lam st741.
      lam currRep8.
        lam event3.
          lam nhosts7.
            match
              p_map
                st741
                (lam x1141.
                   match x1141 with Event1 x1591
                   then
                     x1591.host
                   else
                     let #var"2161" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event3
            with
              (st742, hostIndex41)
            in
            match
              p_map
                st742
                (lam x1142.
                   subsequence x1142 (subi 1 1))
                currRep8
            with
              (st743, x1143)
            in
            match
              p_map
                st743
                (lam x1144.
                   subi x1144 1)
                hostIndex41
            with
              (st744, x1145)
            in
            match p_apply st744 x1143 x1145 with (st745, x1146)
            in
            match
              p_map
                st745
                (lam x1147.
                   match x1147 with Event1 x1581
                   then
                     x1581.toState
                   else
                     let #var"2162" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event3
            with
              (st746, x1148)
            in
            match
              p_traverseSeq
                st746
                (lam st747.
                   lam x1149.
                     (st747, x1149))
                [ x1148 ]
            with
              (st748, x1150)
            in
            match
              p_map
                st748
                (lam x1151.
                   addi x1151 1)
                hostIndex41
            with
              (st749, first)
            in
            match p_map st749 subsequence currRep8 with (st750, x1152)
            in
            match
              p_map st750 (lam x1153.
                   subi x1153 1) first
            with
              (st751, x1154)
            in
            match p_apply st751 x1152 x1154 with (st752, x1155)
            in
            match
              p_map
                st752
                (lam x1156.
                   subi (addi nhosts7 1) x1156)
                first
            with
              (st753, x1157)
            in
            match p_apply st753 x1155 x1157 with (st754, x1158)
            in
            paste02
              st754
              [ x1146,
                x1150,
                x1158 ]
  in
  recursive
    let ifCont3 =
      lam st72.
        lam currRep.
          lam eventSeq.
            lam eventIndex.
              lam nEvents.
                lam nhosts2.
                  lam event.
                    lam #var"3".
                      let hostIndex4 =
                        match event with Event1 x159
                        then
                          x159.host
                        else
                          let #var"216" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                          in
                          exit 1
                      in
                      let s210 =
                        [ slice currRep 1 hostIndex4,
                          [ p_pure
                              (match event with Event1 x158
                               then
                                 x158.toState
                               else
                                 let #var"215" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                                 in
                                 exit 1) ],
                          slice currRep (addi hostIndex4 1) (addi nhosts2 1) ]
                      in
                      let currRep1 =
                        match s210 with [ _ ] ++ _
                        then
                          match splitAt s210 1 with {#label"1" = x84}
                          in
                          rec21 (concat "" (get s210 0)) x84
                        else match s210 with ""
                        in
                        ""
                      in
                      let eventIndex1 = addi eventIndex 1 in
                      match gti eventIndex1 nEvents with true
                      then
                        (st72, p_pure true)
                      else match
                        p_map
                          st72
                          (lam x79.
                             get x79 (subi eventIndex1 1))
                          eventSeq
                      with
                        (st73, x80)
                      in
                      p_bind
                        st73
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st74.
                           lam x81.
                             match
                               eqi
                                 (match x81 with Event1 x301
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
                               match count2s st74 currRep1 with (st75, x82)
                               in
                               p_bind
                                 st75
                                 simpleStoreSubmodel
                                 (simpleInit {})
                                 (lam st76.
                                    lam x83.
                                      match eqi x83 1 with true
                                      then
                                        (st76, p_pure false)
                                      else
                                        ifCont3 st76 currRep1 eventSeq eventIndex1 nEvents nhosts2 x81 0)
                                 x82
                             else
                               ifCont3 st74 currRep1 eventSeq eventIndex1 nEvents nhosts2 x81 0)
                        x80
    let allTimesValidBranch =
      lam st77.
        lam currRep11.
          lam eventSeq1.
            lam eventIndex11.
              lam nEvents1.
                lam nhosts3.
                  p_bind
                    st77
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st78.
                       lam x85.
                         match gti eventIndex11 x85 with true
                         then
                           (st78, p_pure true)
                         else match
                           p_map
                             st78
                             (lam x86.
                                get x86 (subi eventIndex11 1))
                             eventSeq1
                         with
                           (st79, x87)
                         in
                         p_bind
                           st79
                           simpleStoreSubmodel
                           (simpleInit {})
                           (lam st80.
                              lam x88.
                                match
                                  eqi
                                    (match x88 with Event1 x302
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
                                  match count2s st80 currRep11 with (st81, x89)
                                  in
                                  p_bind
                                    st81
                                    simpleStoreSubmodel
                                    (simpleInit {})
                                    (lam st82.
                                       lam x90.
                                         match eqi x90 1 with true
                                         then
                                           (st82, p_pure false)
                                         else
                                           ifCont3 st82 currRep11 eventSeq1 eventIndex11 x85 nhosts3 x88 0)
                                    x89
                                else
                                  ifCont3 st80 currRep11 eventSeq1 eventIndex11 x85 nhosts3 x88 0)
                           x87)
                    nEvents1
  in
  let anon17 =
    lam x1140.
      match eqi x1140 2 with true
      then
        true
      else
        eqi x1140 1
  in
  let anon18 =
    lam st740.
      lam x1138.
        p_map
          st740
          (lam x1139.
             match eqi x1139 2 with true
             then
               true
             else
               eqi x1139 1)
          x1138
  in
  recursive
    let rec8 =
      lam s7.
        match s7 with [ _,
            _ ] ++ _
        then
          match splitAt s7 1 with {#label"1" = x91}
          in
          cons (anon17 (get s7 0)) (rec8 x91)
        else match s7 with [ e10 ]
        then
          match splitAt s7 1 with {#label"1" = x92}
          in
          let slice9 = x92 in
          [ anon17 e10 ]
        else match s7 with ""
        in
        ""
    let rec9 =
      lam st83.
        lam s8.
          match s8 with [ _,
              _ ] ++ _
          then
            match anon18 st83 (get s8 0) with (st84, x93)
            in
            match splitAt s8 1 with {#label"1" = x94}
            in
            match rec9 st84 x94 with (st85, x95)
            in
            (st85, cons x93 x95)
          else match s8 with [ e11 ]
          then
            match splitAt s8 1 with {#label"1" = x96}
            in
            let slice10 = x96 in
            match anon18 st83 e11 with (st86, x97)
            in
            (st86, [ x97 ])
          else match s8 with ""
          in
          (st83, "")
  in
  let sapply = lam st739.
      lam s102.
        rec9 st739 s102
  in
  let anon19 = lam x1137.
      eqi x1137 2 in
  let anon20 =
    lam st738.
      lam x1135.
        p_map st738 (lam x1136.
             eqi x1136 2) x1135
  in
  recursive
    let rec10 =
      lam s9.
        match s9 with [ _,
            _ ] ++ _
        then
          match splitAt s9 1 with {#label"1" = x98}
          in
          cons (anon19 (get s9 0)) (rec10 x98)
        else match s9 with [ e12 ]
        then
          match splitAt s9 1 with {#label"1" = x99}
          in
          let slice11 = x99 in
          [ anon19 e12 ]
        else match s9 with ""
        in
        ""
    let rec14 =
      lam st87.
        lam s10.
          match s10 with [ _,
              _ ] ++ _
          then
            match anon20 st87 (get s10 0) with (st88, x100)
            in
            match splitAt s10 1 with {#label"1" = x101}
            in
            match rec14 st88 x101 with (st89, x102)
            in
            (st89, cons x100 x102)
          else match s10 with [ e13 ]
          then
            match splitAt s10 1 with {#label"1" = x103}
            in
            let slice12 = x103 in
            match anon20 st87 e13 with (st90, x104)
            in
            (st90, [ x104 ])
          else match s10 with ""
          in
          (st87, "")
  in
  let sapply1 = lam st737.
      lam s101.
        rec14 st737 s101
  in
  let getGainRate =
    lam st729.
      lam repertoire14.
        lam hostIndex33.
          lam modelParams123.
            let fromState53 = get repertoire14 (subi hostIndex33 1) in
            match
              mtxGet
                st729
                (addi fromState53 1)
                (addi (addi fromState53 1) 1)
                (match
                   match modelParams123 with ModelParams1 x1554
                   then
                     x1554.embeddedQMatrix
                   else
                     let #var"2155" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1544
                 then
                   x1544.mat
                 else
                   let #var"2156" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st730, baseRate13)
            in
            match eqi fromState53 0 with true
            then
              match
                p_map
                  st730
                  (lam x1123.
                     lam x1124.
                       mulf x1123 x1124)
                  baseRate13
              with
                (st731, x1125)
              in
              match
                p_map
                  st731
                  (lam x1126.
                     negf x1126)
                  (match modelParams123 with ModelParams1 x1504
                   then
                     x1504.beta
                   else
                     let #var"2157" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                     in
                     p_pure (exit 1))
              with
                (st732, x1127)
              in
              match
                pow1
                  st732
                  (mtxMean
                     (mtxRowCols
                        (match modelParams123 with ModelParams1 x1514
                         then
                           x1514.hostMetric
                         else
                           let #var"2158" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                           in
                           exit 1)
                        hostIndex33
                        (whichTrue (rec8 repertoire14))))
                  x1127
              with
                (st733, x1128)
              in
              p_apply st733 x1125 x1128
            else match
              p_map
                st730
                (lam x1129.
                   lam x1130.
                     mulf x1129 x1130)
                baseRate13
            with
              (st734, x1131)
            in
            match
              p_map
                st734
                (lam x1132.
                   negf x1132)
                (match modelParams123 with ModelParams1 x1524
                 then
                   x1524.beta
                 else
                   let #var"2159" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                   in
                   p_pure (exit 1))
            with
              (st735, x1133)
            in
            match
              pow1
                st735
                (mtxMean
                   (mtxRowCols
                      (match modelParams123 with ModelParams1 x1534
                       then
                         x1534.hostMetric
                       else
                         let #var"2160" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                         in
                         exit 1)
                      hostIndex33
                      (whichTrue (rec10 repertoire14))))
                x1133
            with
              (st736, x1134)
            in
            p_apply st736 x1131 x1134
  in
  let getGainRate1 =
    lam st710.
      lam repertoire13.
        lam hostIndex32.
          lam modelParams122.
            let fromState52 = get repertoire13 (subi hostIndex32 1) in
            match
              p_map
                st710
                (lam x1097.
                   addi x1097 1)
                fromState52
            with
              (st711, x1098)
            in
            match
              p_map
                st711
                (lam x1099.
                   addi (addi x1099 1) 1)
                fromState52
            with
              (st712, x1100)
            in
            match
              mtxGet2
                st712
                x1098
                x1100
                (match
                   match modelParams122 with ModelParams1 x1553
                   then
                     x1553.embeddedQMatrix
                   else
                     let #var"2149" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1543
                 then
                   x1543.mat
                 else
                   let #var"2150" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st713, baseRate12)
            in
            p_bind
              st713
              simpleStoreSubmodel
              (simpleInit {})
              (lam st714.
                 lam x1101.
                   match eqi x1101 0 with true
                   then
                     match
                       p_map
                         st714
                         (lam x1102.
                            lam x1103.
                              mulf x1102 x1103)
                         baseRate12
                     with
                       (st715, x1104)
                     in
                     match sapply st715 repertoire13 with (st716, x1105)
                     in
                     match whichTrue1 st716 x1105 with (st717, x1106)
                     in
                     match
                       mtxRowCols1
                         st717
                         (match modelParams122 with ModelParams1 x1513
                          then
                            x1513.hostMetric
                          else
                            let #var"2151" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex32
                         x1106
                     with
                       (st718, x1107)
                     in
                     match mtxMean1 st718 x1107 with (st719, x1108)
                     in
                     match
                       p_map
                         st719
                         (lam x1109.
                            negf x1109)
                         (match modelParams122 with ModelParams1 x1503
                          then
                            x1503.beta
                          else
                            let #var"2152" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st720, x1110)
                     in
                     match pow2 st720 x1108 x1110 with (st721, x1112)
                     in
                     p_apply st721 x1104 x1112
                   else match
                     p_map
                       st714
                       (lam x1113.
                          lam x1114.
                            mulf x1113 x1114)
                       baseRate12
                   with
                     (st722, x1115)
                   in
                   match sapply1 st722 repertoire13 with (st723, x1116)
                   in
                   match whichTrue1 st723 x1116 with (st724, x1117)
                   in
                   match
                     mtxRowCols1
                       st724
                       (match modelParams122 with ModelParams1 x1533
                        then
                          x1533.hostMetric
                        else
                          let #var"2153" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex32
                       x1117
                   with
                     (st725, x1118)
                   in
                   match mtxMean1 st725 x1118 with (st726, x1119)
                   in
                   match
                     p_map
                       st726
                       (lam x1120.
                          negf x1120)
                       (match modelParams122 with ModelParams1 x1523
                        then
                          x1523.beta
                        else
                          let #var"2154" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st727, x1121)
                   in
                   match pow2 st727 x1119 x1121 with (st728, x1122)
                   in
                   p_apply st728 x1115 x1122)
              fromState52
  in
  let getGainRate2 =
    lam st686.
      lam repertoire12.
        lam hostIndex31.
          lam modelParams121.
            match
              p_traverseSeq
                st686
                (lam st687.
                   lam x1067.
                     (st687, x1067))
                repertoire12
            with
              (st688, x1068)
            in
            match p_map st688 get x1068 with (st689, x1069)
            in
            match
              p_map
                st689
                (lam x1070.
                   subi x1070 1)
                hostIndex31
            with
              (st690, x1071)
            in
            match p_apply st690 x1069 x1071 with (st691, fromState51)
            in
            match
              p_map
                st691
                (lam x1072.
                   addi x1072 1)
                fromState51
            with
              (st692, x1073)
            in
            match
              p_map
                st692
                (lam x1074.
                   addi (addi x1074 1) 1)
                fromState51
            with
              (st693, x1075)
            in
            match
              mtxGet2
                st693
                x1073
                x1075
                (match
                   match modelParams121 with ModelParams1 x1552
                   then
                     x1552.embeddedQMatrix
                   else
                     let #var"2143" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1542
                 then
                   x1542.mat
                 else
                   let #var"2144" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st694, baseRate11)
            in
            p_bind
              st694
              simpleStoreSubmodel
              (simpleInit {})
              (lam st695.
                 lam x1076.
                   match eqi x1076 0 with true
                   then
                     match
                       p_map
                         st695
                         (lam x1077.
                            lam x1078.
                              mulf x1077 x1078)
                         baseRate11
                     with
                       (st696, x1079)
                     in
                     match sapply st696 repertoire12 with (st697, x1080)
                     in
                     match whichTrue1 st697 x1080 with (st698, x1081)
                     in
                     match
                       mtxRowCols2
                         st698
                         (match modelParams121 with ModelParams1 x1512
                          then
                            x1512.hostMetric
                          else
                            let #var"2145" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex31
                         x1081
                     with
                       (st699, x1082)
                     in
                     match mtxMean1 st699 x1082 with (st700, x1083)
                     in
                     match
                       p_map
                         st700
                         (lam x1084.
                            negf x1084)
                         (match modelParams121 with ModelParams1 x1502
                          then
                            x1502.beta
                          else
                            let #var"2146" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st701, x1085)
                     in
                     match pow2 st701 x1083 x1085 with (st702, x1086)
                     in
                     p_apply st702 x1079 x1086
                   else match
                     p_map
                       st695
                       (lam x1087.
                          lam x1088.
                            mulf x1087 x1088)
                       baseRate11
                   with
                     (st703, x1089)
                   in
                   match sapply1 st703 repertoire12 with (st704, x1090)
                   in
                   match whichTrue1 st704 x1090 with (st705, x1091)
                   in
                   match
                     mtxRowCols2
                       st705
                       (match modelParams121 with ModelParams1 x1532
                        then
                          x1532.hostMetric
                        else
                          let #var"2147" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex31
                       x1091
                   with
                     (st706, x1092)
                   in
                   match mtxMean1 st706 x1092 with (st707, x1093)
                   in
                   match
                     p_map
                       st707
                       (lam x1094.
                          negf x1094)
                       (match modelParams121 with ModelParams1 x1522
                        then
                          x1522.beta
                        else
                          let #var"2148" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st708, x1095)
                   in
                   match pow2 st708 x1093 x1095 with (st709, x1096)
                   in
                   p_apply st709 x1089 x1096)
              fromState51
  in
  let getGainRate3 =
    lam st664.
      lam repertoire11.
        lam hostIndex3.
          lam modelParams12.
            match p_map st664 get repertoire11 with (st665, x1032)
            in
            match
              p_map
                st665 (lam x1033.
                   subi x1033 1) hostIndex3
            with
              (st666, x1034)
            in
            match p_apply st666 x1032 x1034 with (st667, fromState5)
            in
            match
              p_map
                st667 (lam x1035.
                   addi x1035 1) fromState5
            with
              (st668, x1036)
            in
            match
              p_map
                st668
                (lam x1037.
                   addi (addi x1037 1) 1)
                fromState5
            with
              (st669, x1038)
            in
            match
              mtxGet2
                st669
                x1036
                x1038
                (match
                   match modelParams12 with ModelParams1 x1551
                   then
                     x1551.embeddedQMatrix
                   else
                     let #var"2137" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1541
                 then
                   x1541.mat
                 else
                   let #var"2138" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st670, baseRate1)
            in
            p_bind
              st670
              simpleStoreSubmodel
              (simpleInit {})
              (lam st671.
                 lam x1039.
                   match eqi x1039 0 with true
                   then
                     match
                       p_map
                         st671
                         (lam x1040.
                            lam x1042.
                              mulf x1040 x1042)
                         baseRate1
                     with
                       (st672, x1043)
                     in
                     match
                       p_map
                         st672
                         (lam x1044.
                            match x1044 with [ _,
                                _ ] ++ _
                            then
                              match splitAt x1044 1 with {#label"1" = x1045}
                              in
                              cons (anon17 (get x1044 0)) (rec8 x1045)
                            else match x1044 with [ e19 ]
                            then
                              match splitAt x1044 1 with {#label"1" = x1046}
                              in
                              let slice18 = x1046 in
                              [ anon17 e19 ]
                            else match x1044 with ""
                            in
                            "")
                         repertoire11
                     with
                       (st673, x1047)
                     in
                     match whichTrue2 st673 x1047 with (st674, x1048)
                     in
                     match
                       mtxRowCols2
                         st674
                         (match modelParams12 with ModelParams1 x1511
                          then
                            x1511.hostMetric
                          else
                            let #var"2139" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex3
                         x1048
                     with
                       (st675, x1049)
                     in
                     match mtxMean1 st675 x1049 with (st676, x1050)
                     in
                     match
                       p_map
                         st676
                         (lam x1051.
                            negf x1051)
                         (match modelParams12 with ModelParams1 x1501
                          then
                            x1501.beta
                          else
                            let #var"2140" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                            in
                            p_pure (exit 1))
                     with
                       (st677, x1052)
                     in
                     match pow2 st677 x1050 x1052 with (st678, x1053)
                     in
                     p_apply st678 x1043 x1053
                   else match
                     p_map
                       st671
                       (lam x1054.
                          lam x1055.
                            mulf x1054 x1055)
                       baseRate1
                   with
                     (st679, x1056)
                   in
                   match
                     p_map
                       st679
                       (lam x1057.
                          match x1057 with [ _,
                              _ ] ++ _
                          then
                            match splitAt x1057 1 with {#label"1" = x1058}
                            in
                            cons (anon19 (get x1057 0)) (rec10 x1058)
                          else match x1057 with [ e20 ]
                          then
                            match splitAt x1057 1 with {#label"1" = x1059}
                            in
                            let slice19 = x1059 in
                            [ anon19 e20 ]
                          else match x1057 with ""
                          in
                          "")
                       repertoire11
                   with
                     (st680, x1060)
                   in
                   match whichTrue2 st680 x1060 with (st681, x1061)
                   in
                   match
                     mtxRowCols2
                       st681
                       (match modelParams12 with ModelParams1 x1531
                        then
                          x1531.hostMetric
                        else
                          let #var"2141" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex3
                       x1061
                   with
                     (st682, x1062)
                   in
                   match mtxMean1 st682 x1062 with (st683, x1063)
                   in
                   match
                     p_map
                       st683
                       (lam x1064.
                          negf x1064)
                       (match modelParams12 with ModelParams1 x1521
                        then
                          x1521.beta
                        else
                          let #var"2142" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                          in
                          p_pure (exit 1))
                   with
                     (st684, x1065)
                   in
                   match pow2 st684 x1063 x1065 with (st685, x1066)
                   in
                   p_apply st685 x1056 x1066)
              fromState5
  in
  let getLossRate =
    lam st663.
      lam repertoire3.
        lam hostIndex23.
          lam modelParams103.
            let fromState33 = get repertoire3 (subi hostIndex23 1) in
            match
              match eqi fromState33 2 with true
              then
                eqi (rec28 0 repertoire3) 1
              else
                false
            with
              true
            then
              (st663, p_pure 0.)
            else
              mtxGet
                st663
                (addi fromState33 1)
                (addi (subi fromState33 1) 1)
                (match
                   match modelParams103 with ModelParams1 x1484
                   then
                     x1484.embeddedQMatrix
                   else
                     let #var"2135" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1474
                 then
                   x1474.mat
                 else
                   let #var"2136" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
  in
  let getLossRate1 =
    lam st656.
      lam repertoire2.
        lam hostIndex22.
          lam modelParams102.
            let fromState32 = get repertoire2 (subi hostIndex22 1) in
            match
              p_bind
                st656
                simpleStoreSubmodel
                (simpleInit {})
                (lam st657.
                   lam x1023.
                     match eqi x1023 2 with true
                     then
                       match count2s st657 repertoire2 with (st658, x1024)
                       in
                       p_map
                         st658
                         (lam x1025.
                            eqi x1025 1)
                         x1024
                     else
                       (st657, p_pure false))
                fromState32
            with
              (st659, x1026)
            in
            p_bind
              st659
              simpleStoreSubmodel
              (simpleInit {})
              (lam st660.
                 lam x1027.
                   match x1027 with true
                   then
                     (st660, p_pure 0.)
                   else match
                     p_map
                       st660
                       (lam x1028.
                          addi x1028 1)
                       fromState32
                   with
                     (st661, x1029)
                   in
                   match
                     p_map
                       st661
                       (lam x1030.
                          addi (subi x1030 1) 1)
                       fromState32
                   with
                     (st662, x1031)
                   in
                   mtxGet2
                     st662
                     x1029
                     x1031
                     (match
                        match modelParams102 with ModelParams1 x1483
                        then
                          x1483.embeddedQMatrix
                        else
                          let #var"2133" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1473
                      then
                        x1473.mat
                      else
                        let #var"2134" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x1026
  in
  let getLossRate2 =
    lam st644.
      lam repertoire1.
        lam hostIndex21.
          lam modelParams101.
            match
              p_traverseSeq
                st644
                (lam st645.
                   lam x1008.
                     (st645, x1008))
                repertoire1
            with
              (st646, x1009)
            in
            match p_map st646 get x1009 with (st647, x1010)
            in
            match
              p_map
                st647
                (lam x1012.
                   subi x1012 1)
                hostIndex21
            with
              (st648, x1013)
            in
            match p_apply st648 x1010 x1013 with (st649, fromState31)
            in
            match
              p_bind
                st649
                simpleStoreSubmodel
                (simpleInit {})
                (lam st650.
                   lam x1014.
                     match eqi x1014 2 with true
                     then
                       match count2s st650 repertoire1 with (st651, x1015)
                       in
                       p_map
                         st651
                         (lam x1016.
                            eqi x1016 1)
                         x1015
                     else
                       (st650, p_pure false))
                fromState31
            with
              (st652, x1017)
            in
            p_bind
              st652
              simpleStoreSubmodel
              (simpleInit {})
              (lam st653.
                 lam x1018.
                   match x1018 with true
                   then
                     (st653, p_pure 0.)
                   else match
                     p_map
                       st653
                       (lam x1019.
                          addi x1019 1)
                       fromState31
                   with
                     (st654, x1020)
                   in
                   match
                     p_map
                       st654
                       (lam x1021.
                          addi (subi x1021 1) 1)
                       fromState31
                   with
                     (st655, x1022)
                   in
                   mtxGet2
                     st655
                     x1020
                     x1022
                     (match
                        match modelParams101 with ModelParams1 x1482
                        then
                          x1482.embeddedQMatrix
                        else
                          let #var"2131" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1472
                      then
                        x1472.mat
                      else
                        let #var"2132" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x1017
  in
  let getLossRate3 =
    lam st634.
      lam repertoire.
        lam hostIndex2.
          lam modelParams10.
            match p_map st634 get repertoire with (st635, x994)
            in
            match
              p_map st635 (lam x995.
                   subi x995 1) hostIndex2
            with
              (st636, x996)
            in
            match p_apply st636 x994 x996 with (st637, fromState3)
            in
            match
              p_bind
                st637
                simpleStoreSubmodel
                (simpleInit {})
                (lam st638.
                   lam x997.
                     match eqi x997 2 with true
                     then
                       match
                         p_map
                           st638
                           (lam x998.
                              match x998 with [ _ ] ++ _
                              then
                                match splitAt x998 1 with {#label"1" = x999}
                                in
                                rec28 (anon16 0 (get x998 0)) x999
                              else match x998 with ""
                              in
                              0)
                           repertoire
                       with
                         (st639, x1000)
                       in
                       p_map
                         st639
                         (lam x1001.
                            eqi x1001 1)
                         x1000
                     else
                       (st638, p_pure false))
                fromState3
            with
              (st640, x1002)
            in
            p_bind
              st640
              simpleStoreSubmodel
              (simpleInit {})
              (lam st641.
                 lam x1003.
                   match x1003 with true
                   then
                     (st641, p_pure 0.)
                   else match
                     p_map
                       st641
                       (lam x1004.
                          addi x1004 1)
                       fromState3
                   with
                     (st642, x1005)
                   in
                   match
                     p_map
                       st642
                       (lam x1006.
                          addi (subi x1006 1) 1)
                       fromState3
                   with
                     (st643, x1007)
                   in
                   mtxGet2
                     st643
                     x1005
                     x1007
                     (match
                        match modelParams10 with ModelParams1 x1481
                        then
                          x1481.embeddedQMatrix
                        else
                          let #var"2129" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1471
                      then
                        x1471.mat
                      else
                        let #var"2130" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x1002
  in
  recursive
    let rec210 =
      lam st91.
        lam c26.
          lam c27.
            lam acc10.
              lam s211.
                match s211 with [ _ ] ++ _
                then
                  let x105 = get s211 0 in
                  match
                    p_bind
                      st91
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st92.
                         lam x106.
                           match eqi x106 2 with true
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
                           match getGainRate1 st93 c26 x105 c27 with (st94, x110)
                           in
                           p_apply st94 x109 x110)
                      (get c26 (subi x105 1))
                  with
                    (st95, x111)
                  in
                  match splitAt s211 1 with {#label"1" = x112}
                  in
                  rec210 st95 c26 c27 x111 x112
                else match s211 with ""
                in
                (st91, acc10)
    let rec211 =
      lam st96.
        lam c28.
          lam c29.
            lam acc16.
              lam s212.
                match s212 with [ _ ] ++ _
                then
                  let x113 = get s212 0 in
                  match
                    p_bind
                      st96
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st97.
                         lam x114.
                           match eqi (get x114 (subi x113 1)) 2 with true
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
                           match getGainRate st98 x114 x113 c29 with (st99, x118)
                           in
                           p_apply st99 x117 x118)
                      c28
                  with
                    (st100, x119)
                  in
                  match splitAt s212 1 with {#label"1" = x120}
                  in
                  rec211 st100 c28 c29 x119 x120
                else match s212 with ""
                in
                (st96, acc16)
  in
  let anon21 = lam x993.
      addi x993 1 in
  recursive
    let rec35 =
      lam i15.
        lam acc17.
          match geqi i15 0 with true
          then
            rec35 (subi i15 1) (cons (anon21 i15) acc17)
          else
            acc17
  in
  let create11 =
    lam l63.
      let i114 = subi l63 1 in
      match geqi i114 0 with true
      then
        rec35 (subi i114 1) (cons (anon21 i114) "")
      else
        ""
  in
  recursive
    let rec212 =
      lam st101.
        lam c30.
          lam c31.
            lam acc18.
              lam s213.
                match s213 with [ _ ] ++ _
                then
                  let x121 = get s213 0 in
                  match
                    p_bind
                      st101
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st102.
                         lam x122.
                           match eqi x122 0 with true
                           then
                             (st102, acc18)
                           else match
                             p_map
                               st102
                               (lam x123.
                                  lam x124.
                                    addf x123 x124)
                               acc18
                           with
                             (st103, x125)
                           in
                           match getLossRate1 st103 c30 x121 c31 with (st104, x126)
                           in
                           p_apply st104 x125 x126)
                      (get c30 (subi x121 1))
                  with
                    (st105, x127)
                  in
                  match splitAt s213 1 with {#label"1" = x128}
                  in
                  rec212 st105 c30 c31 x127 x128
                else match s213 with ""
                in
                (st101, acc18)
    let rec213 =
      lam st106.
        lam c32.
          lam c33.
            lam acc19.
              lam s214.
                match s214 with [ _ ] ++ _
                then
                  let x129 = get s214 0 in
                  match
                    p_bind
                      st106
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st107.
                         lam x130.
                           match eqi (get x130 (subi x129 1)) 0 with true
                           then
                             (st107, acc19)
                           else match
                             p_map
                               st107
                               (lam x131.
                                  lam x132.
                                    addf x131 x132)
                               acc19
                           with
                             (st108, x133)
                           in
                           match getLossRate st108 x130 x129 c33 with (st109, x134)
                           in
                           p_apply st109 x133 x134)
                      c32
                  with
                    (st110, x135)
                  in
                  match splitAt s214 1 with {#label"1" = x136}
                  in
                  rec213 st110 c32 c33 x135 x136
                else match s214 with ""
                in
                (st106, acc19)
  in
  let anon22 = lam x992.
      addi x992 1 in
  recursive
    let rec36 =
      lam i16.
        lam acc110.
          match geqi i16 0 with true
          then
            rec36 (subi i16 1) (cons (anon22 i16) acc110)
          else
            acc110
  in
  let create12 =
    lam l62.
      let i113 = subi l62 1 in
      match geqi i113 0 with true
      then
        rec36 (subi i113 1) (cons (anon22 i113) "")
      else
        ""
  in
  let getTotalRate =
    lam st624.
      lam currRep51.
        lam modelParams81.
          lam nhosts61.
            let s226 = create11 (addi (subi nhosts61 1) 1) in
            match
              match s226 with [ _ ] ++ _
              then
                let x974 = get s226 0 in
                match
                  p_bind
                    st624
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st625.
                       lam x975.
                         match eqi x975 2 with true
                         then
                           (st625, p_pure 0.)
                         else match getGainRate1 st625 currRep51 x974 modelParams81 with (st626, x976)
                         in
                         p_map
                           st626
                           (lam x977.
                              addf 0. x977)
                           x976)
                    (get currRep51 (subi x974 1))
                with
                  (st627, x978)
                in
                match splitAt s226 1 with {#label"1" = x979}
                in
                rec210 st627 currRep51 modelParams81 x978 x979
              else match s226 with ""
              in
              (st624, p_pure 0.)
            with
              (st628, x980)
            in
            match
              p_map
                st628
                (lam x982.
                   lam x983.
                     addf x982 x983)
                x980
            with
              (st629, x984)
            in
            let s227 = create12 (addi (subi nhosts61 1) 1) in
            match
              match s227 with [ _ ] ++ _
              then
                let x985 = get s227 0 in
                match
                  p_bind
                    st629
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st630.
                       lam x986.
                         match eqi x986 0 with true
                         then
                           (st630, p_pure 0.)
                         else match getLossRate1 st630 currRep51 x985 modelParams81 with (st631, x987)
                         in
                         p_map
                           st631
                           (lam x988.
                              addf 0. x988)
                           x987)
                    (get currRep51 (subi x985 1))
                with
                  (st632, x989)
                in
                match splitAt s227 1 with {#label"1" = x990}
                in
                rec212 st632 currRep51 modelParams81 x989 x990
              else match s227 with ""
              in
              (st629, p_pure 0.)
            with
              (st633, x991)
            in
            p_apply st633 x984 x991
  in
  let getTotalRate1 =
    lam st614.
      lam currRep5.
        lam modelParams8.
          lam nhosts6.
            let s224 = create11 (addi (subi nhosts6 1) 1) in
            match
              match s224 with [ _ ] ++ _
              then
                let x955 = get s224 0 in
                match
                  p_bind
                    st614
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st615.
                       lam x956.
                         match eqi (get x956 (subi x955 1)) 2 with true
                         then
                           (st615, p_pure 0.)
                         else match getGainRate st615 x956 x955 modelParams8 with (st616, x957)
                         in
                         p_map
                           st616
                           (lam x958.
                              addf 0. x958)
                           x957)
                    currRep5
                with
                  (st617, x959)
                in
                match splitAt s224 1 with {#label"1" = x960}
                in
                rec211 st617 currRep5 modelParams8 x959 x960
              else match s224 with ""
              in
              (st614, p_pure 0.)
            with
              (st618, x962)
            in
            match
              p_map
                st618
                (lam x963.
                   lam x964.
                     addf x963 x964)
                x962
            with
              (st619, x965)
            in
            let s225 = create12 (addi (subi nhosts6 1) 1) in
            match
              match s225 with [ _ ] ++ _
              then
                let x966 = get s225 0 in
                match
                  p_bind
                    st619
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st620.
                       lam x967.
                         match eqi (get x967 (subi x966 1)) 0 with true
                         then
                           (st620, p_pure 0.)
                         else match getLossRate st620 x967 x966 modelParams8 with (st621, x968)
                         in
                         p_map
                           st621
                           (lam x969.
                              addf 0. x969)
                           x968)
                    currRep5
                with
                  (st622, x970)
                in
                match splitAt s225 1 with {#label"1" = x972}
                in
                rec213 st622 currRep5 modelParams8 x970 x972
              else match s225 with ""
              in
              (st619, p_pure 0.)
            with
              (st623, x973)
            in
            p_apply st623 x965 x973
  in
  recursive
    let fullModelWeight =
      lam st111.
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
                                st111
                                (lam x137.
                                   lam x138.
                                     mulf (negf (subf x137 finalAge)) x138)
                                currAge
                            with
                              (st112, x139)
                            in
                            match
                              getTotalRate1 st112 currRep3 modelParams nhosts5
                            with
                              (st113, x140)
                            in
                            p_apply st113 x139 x140
                          else match
                            p_map
                              st111
                              (lam x141.
                                 get x141 (subi nextIndex 1))
                              eventSeq3
                          with
                            (st114, nextEvent)
                          in
                          match
                            p_map
                              st114
                              (lam x142.
                                 match x142 with Event1 x311
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
                            (st115, newAge)
                          in
                          match
                            getTotalRate1 st115 currRep3 modelParams nhosts5
                          with
                            (st116, totalLeavingRate1)
                          in
                          match
                            p_map
                              st116
                              (lam x143.
                                 match x143 with Event1 x145
                                 then
                                   x145.host
                                 else
                                   let #var"219" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st117, hostIndex1)
                          in
                          match
                            p_map
                              st117
                              (lam x144.
                                 lam x146.
                                   lam st118.
                                     match
                                       gti
                                         (match x144 with Event1 x1431
                                          then
                                            x1431.fromState
                                          else
                                            let #var"220" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x146
                                     with
                                       true
                                     then
                                       getLossRate3 st118 currRep3 hostIndex1 modelParams
                                     else
                                       getGainRate3 st118 currRep3 hostIndex1 modelParams)
                              nextEvent
                          with
                            (st119, x147)
                          in
                          match
                            p_map
                              st119
                              (lam x148.
                                 match x148 with Event1 x1441
                                 then
                                   x1441.toState
                                 else
                                   let #var"221" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st120, x149)
                          in
                          match
                            p_subApply st120 simpleStoreSubmodel (simpleInit {}) x147 x149
                          with
                            (st121, x150)
                          in
                          match p_join st121 x150 with (st122, x151)
                          in
                          match
                            p_map
                              st122
                              (lam x152.
                                 lam x153.
                                   divf x152 x153)
                              x151
                          with
                            (st123, x154)
                          in
                          match p_apply st123 x154 totalLeavingRate1 with (st124, x155)
                          in
                          match log11 st124 x155 with (st125, x156)
                          in
                          match
                            p_map
                              st125
                              (lam x157.
                                 lam x160.
                                   lam x161.
                                     addf (subf x157 x160) x161)
                              x156
                          with
                            (st126, x162)
                          in
                          match
                            p_map
                              st126
                              (lam x163.
                                 lam x164.
                                   lam x165.
                                     mulf (subf x163 x164) x165)
                              currAge
                          with
                            (st127, x166)
                          in
                          match p_apply st127 x166 newAge with (st128, x167)
                          in
                          match p_apply st128 x167 totalLeavingRate1 with (st129, x168)
                          in
                          match p_apply st129 x162 x168 with (st130, x169)
                          in
                          match
                            updateRepertoire1 st130 currRep3 nextEvent nhosts5
                          with
                            (st131, x170)
                          in
                          match
                            fullModelWeight
                              st131
                              (addi nextIndex 1)
                              x170
                              finalRep
                              newAge
                              finalAge
                              eventSeq3
                              nEvents3
                              nhosts5
                              modelParams
                          with
                            (st132, x171)
                          in
                          p_apply st132 x169 x171
    let fullModelWeight1 =
      lam st133.
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
                                st133
                                (lam x172.
                                   lam x173.
                                     mulf (negf (subf x172 finalAge1)) x173)
                                currAge1
                            with
                              (st134, x174)
                            in
                            match
                              getTotalRate1 st134 currRep31 modelParams1 nhosts51
                            with
                              (st135, x175)
                            in
                            p_apply st135 x174 x175
                          else match
                            p_map
                              st133
                              (lam x176.
                                 get x176 (subi nextIndex1 1))
                              eventSeq31
                          with
                            (st136, nextEvent1)
                          in
                          match
                            p_map
                              st136
                              (lam x177.
                                 match x177 with Event1 x312
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
                            (st137, newAge1)
                          in
                          match
                            getTotalRate1 st137 currRep31 modelParams1 nhosts51
                          with
                            (st138, totalLeavingRate11)
                          in
                          match
                            p_map
                              st138
                              (lam x178.
                                 match x178 with Event1 x1451
                                 then
                                   x1451.host
                                 else
                                   let #var"223" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st139, hostIndex11)
                          in
                          match
                            p_map
                              st139
                              (lam x179.
                                 lam x180.
                                   lam st140.
                                     match
                                       gti
                                         (match x179 with Event1 x1432
                                          then
                                            x1432.fromState
                                          else
                                            let #var"224" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x180
                                     with
                                       true
                                     then
                                       getLossRate3 st140 currRep31 hostIndex11 modelParams1
                                     else
                                       getGainRate3 st140 currRep31 hostIndex11 modelParams1)
                              nextEvent1
                          with
                            (st141, x181)
                          in
                          match
                            p_map
                              st141
                              (lam x182.
                                 match x182 with Event1 x1442
                                 then
                                   x1442.toState
                                 else
                                   let #var"225" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st142, x183)
                          in
                          match
                            p_subApply st142 simpleStoreSubmodel (simpleInit {}) x181 x183
                          with
                            (st143, x184)
                          in
                          match p_join st143 x184 with (st144, x185)
                          in
                          match
                            p_map
                              st144
                              (lam x186.
                                 lam x187.
                                   divf x186 x187)
                              x185
                          with
                            (st145, x188)
                          in
                          match p_apply st145 x188 totalLeavingRate11 with (st146, x189)
                          in
                          match log11 st146 x189 with (st147, x190)
                          in
                          match
                            p_map
                              st147
                              (lam x191.
                                 lam x192.
                                   lam x193.
                                     addf (subf x191 x192) x193)
                              x190
                          with
                            (st148, x194)
                          in
                          match
                            p_map
                              st148
                              (lam x195.
                                 lam x196.
                                   lam x197.
                                     mulf (subf x195 x196) x197)
                              currAge1
                          with
                            (st149, x198)
                          in
                          match p_apply st149 x198 newAge1 with (st150, x199)
                          in
                          match p_apply st150 x199 totalLeavingRate11 with (st151, x200)
                          in
                          match p_apply st151 x194 x200 with (st152, x201)
                          in
                          match
                            updateRepertoire1 st152 currRep31 nextEvent1 nhosts51
                          with
                            (st153, x202)
                          in
                          match
                            fullModelWeight1
                              st153
                              (addi nextIndex1 1)
                              x202
                              finalRep1
                              newAge1
                              finalAge1
                              eventSeq31
                              nEvents31
                              nhosts51
                              modelParams1
                          with
                            (st154, x203)
                          in
                          p_apply st154 x201 x203
  in
  recursive
    let hostIndepLikelihood =
      lam st155.
        lam nextIndex11.
          lam currState.
            lam finalState.
              lam currAge11.
                lam finalAge11.
                  lam eventSeq4.
                    lam embeddedQMatrix.
                      match length14 st155 eventSeq4 with (st156, x204)
                      in
                      p_bind
                        st156
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st157.
                           lam x205.
                             match gti nextIndex11 x205 with true
                             then
                               match
                                 p_traverseSeq
                                   st157
                                   (lam st158.
                                      lam x206.
                                        (st158, x206))
                                   (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x321
                                    then
                                      x321.totalRates
                                    else
                                      let #var"226" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x207.
                                           p_pure x207)
                                        (exit 1))
                               with
                                 (st159, x208)
                               in
                               match
                                 p_map
                                   st159
                                   (lam x209.
                                      lam x210.
                                        mulf (negf (subf currAge11 finalAge11)) (get x209 x210))
                                   x208
                               with
                                 (st160, x211)
                               in
                               match
                                 p_map
                                   st160
                                   (lam x212.
                                      subi (addi x212 1) 1)
                                   currState
                               with
                                 (st161, x213)
                               in
                               p_apply st161 x211 x213
                             else match
                               p_map
                                 st157
                                 (lam x214.
                                    get x214 (subi nextIndex11 1))
                                 eventSeq4
                             with
                               (st162, nextEvent11)
                             in
                             match
                               p_map
                                 st162
                                 (lam x215.
                                    match x215 with Event1 x361
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
                               (st163, nextState)
                             in
                             match
                               p_map
                                 st163
                                 (lam x216.
                                    match x216 with Event1 x351
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
                               (st164, nextAge)
                             in
                             match
                               p_traverseSeq
                                 st164
                                 (lam st165.
                                    lam x217.
                                      p_traverseSeq
                                        st165
                                        (lam st166.
                                           lam x218.
                                             (st166, x218))
                                        x217)
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x331
                                  then
                                    x331.transitionProbs
                                  else
                                    let #var"229" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x219.
                                         map
                                           (lam x220.
                                              p_pure x220)
                                           x219)
                                      (exit 1))
                             with
                               (st167, x222)
                             in
                             match
                               p_map
                                 st167
                                 (lam x223.
                                    lam x224.
                                      get (get x223 x224))
                                 x222
                             with
                               (st168, x225)
                             in
                             match
                               p_map
                                 st168
                                 (lam x226.
                                    subi (addi x226 1) 1)
                                 currState
                             with
                               (st169, x227)
                             in
                             match p_apply st169 x225 x227 with (st170, x228)
                             in
                             match
                               p_map
                                 st170
                                 (lam x229.
                                    subi (addi x229 1) 1)
                                 nextState
                             with
                               (st171, x230)
                             in
                             match p_apply st171 x228 x230 with (st172, x232)
                             in
                             match log11 st172 x232 with (st173, x233)
                             in
                             match
                               p_map
                                 st173
                                 (lam x234.
                                    lam x235.
                                      lam x236.
                                        addf (subf x234 x235) x236)
                                 x233
                             with
                               (st174, x237)
                             in
                             match
                               p_map
                                 st174
                                 (lam x238.
                                    lam x239.
                                      mulf (subf currAge11 x238) x239)
                                 nextAge
                             with
                               (st175, x240)
                             in
                             match
                               p_traverseSeq
                                 st175
                                 (lam st176.
                                    lam x241.
                                      (st176, x241))
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x341
                                  then
                                    x341.totalRates
                                  else
                                    let #var"230" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x242.
                                         p_pure x242)
                                      (exit 1))
                             with
                               (st177, x243)
                             in
                             match p_map st177 get x243 with (st178, x244)
                             in
                             match
                               p_map
                                 st178
                                 (lam x245.
                                    subi (addi x245 1) 1)
                                 currState
                             with
                               (st179, x246)
                             in
                             match p_apply st179 x244 x246 with (st180, x247)
                             in
                             match p_apply st180 x240 x247 with (st181, x248)
                             in
                             match p_apply st181 x237 x248 with (st182, x249)
                             in
                             match
                               hostIndepLikelihood1
                                 st182
                                 (addi nextIndex11 1)
                                 nextState
                                 finalState
                                 nextAge
                                 finalAge11
                                 eventSeq4
                                 embeddedQMatrix
                             with
                               (st183, x250)
                             in
                             p_apply st183 x249 x250)
                        x204
    let hostIndepLikelihood1 =
      lam st184.
        lam nextIndex12.
          lam currState1.
            lam finalState1.
              lam currAge12.
                lam finalAge12.
                  lam eventSeq41.
                    lam embeddedQMatrix1.
                      match length14 st184 eventSeq41 with (st185, x251)
                      in
                      p_bind
                        st185
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st186.
                           lam x252.
                             match gti nextIndex12 x252 with true
                             then
                               match
                                 p_map
                                   st186
                                   (lam x253.
                                      lam x254.
                                        mulf (negf (subf x253 finalAge12)) x254)
                                   currAge12
                               with
                                 (st187, x255)
                               in
                               match
                                 p_traverseSeq
                                   st187
                                   (lam st188.
                                      lam x256.
                                        (st188, x256))
                                   (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x322
                                    then
                                      x322.totalRates
                                    else
                                      let #var"231" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x257.
                                           p_pure x257)
                                        (exit 1))
                               with
                                 (st189, x258)
                               in
                               match p_map st189 get x258 with (st190, x259)
                               in
                               match
                                 p_map
                                   st190
                                   (lam x260.
                                      subi (addi x260 1) 1)
                                   currState1
                               with
                                 (st191, x261)
                               in
                               match p_apply st191 x259 x261 with (st192, x262)
                               in
                               p_apply st192 x255 x262
                             else match
                               p_map
                                 st186
                                 (lam x263.
                                    get x263 (subi nextIndex12 1))
                                 eventSeq41
                             with
                               (st193, nextEvent12)
                             in
                             match
                               p_map
                                 st193
                                 (lam x264.
                                    match x264 with Event1 x362
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
                               (st194, nextState1)
                             in
                             match
                               p_map
                                 st194
                                 (lam x265.
                                    match x265 with Event1 x352
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
                               (st195, nextAge1)
                             in
                             match
                               p_traverseSeq
                                 st195
                                 (lam st196.
                                    lam x266.
                                      p_traverseSeq
                                        st196
                                        (lam st197.
                                           lam x267.
                                             (st197, x267))
                                        x266)
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x332
                                  then
                                    x332.transitionProbs
                                  else
                                    let #var"234" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x268.
                                         map
                                           (lam x269.
                                              p_pure x269)
                                           x268)
                                      (exit 1))
                             with
                               (st198, x270)
                             in
                             match
                               p_map
                                 st198
                                 (lam x271.
                                    lam x272.
                                      get (get x271 x272))
                                 x270
                             with
                               (st199, x273)
                             in
                             match
                               p_map
                                 st199
                                 (lam x274.
                                    subi (addi x274 1) 1)
                                 currState1
                             with
                               (st200, x275)
                             in
                             match p_apply st200 x273 x275 with (st201, x276)
                             in
                             match
                               p_map
                                 st201
                                 (lam x277.
                                    subi (addi x277 1) 1)
                                 nextState1
                             with
                               (st202, x278)
                             in
                             match p_apply st202 x276 x278 with (st203, x279)
                             in
                             match log11 st203 x279 with (st204, x280)
                             in
                             match
                               p_map
                                 st204
                                 (lam x281.
                                    lam x282.
                                      lam x283.
                                        addf (subf x281 x282) x283)
                                 x280
                             with
                               (st205, x284)
                             in
                             match
                               p_map
                                 st205
                                 (lam x285.
                                    lam x286.
                                      lam x287.
                                        mulf (subf x285 x286) x287)
                                 currAge12
                             with
                               (st206, x288)
                             in
                             match p_apply st206 x288 nextAge1 with (st207, x289)
                             in
                             match
                               p_traverseSeq
                                 st207
                                 (lam st208.
                                    lam x290.
                                      (st208, x290))
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x342
                                  then
                                    x342.totalRates
                                  else
                                    let #var"235" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x291.
                                         p_pure x291)
                                      (exit 1))
                             with
                               (st209, x292)
                             in
                             match p_map st209 get x292 with (st210, x293)
                             in
                             match
                               p_map
                                 st210
                                 (lam x294.
                                    subi (addi x294 1) 1)
                                 currState1
                             with
                               (st211, x295)
                             in
                             match p_apply st211 x293 x295 with (st212, x296)
                             in
                             match p_apply st212 x289 x296 with (st213, x297)
                             in
                             match p_apply st213 x284 x297 with (st214, x298)
                             in
                             match
                               hostIndepLikelihood1
                                 st214
                                 (addi nextIndex12 1)
                                 nextState1
                                 finalState1
                                 nextAge1
                                 finalAge12
                                 eventSeq41
                                 embeddedQMatrix1
                             with
                               (st215, x299)
                             in
                             p_apply st215 x298 x299)
                        x251
    let hostIndepLikelihood2 =
      lam st216.
        lam nextIndex13.
          lam currState2.
            lam finalState2.
              lam currAge13.
                lam finalAge13.
                  lam eventSeq42.
                    lam embeddedQMatrix2.
                      match length14 st216 eventSeq42 with (st217, x300)
                      in
                      p_bind
                        st217
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st218.
                           lam x303.
                             match gti nextIndex13 x303 with true
                             then
                               match
                                 p_traverseSeq
                                   st218
                                   (lam st219.
                                      lam x304.
                                        (st219, x304))
                                   (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x323
                                    then
                                      x323.totalRates
                                    else
                                      let #var"236" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x305.
                                           p_pure x305)
                                        (exit 1))
                               with
                                 (st220, x306)
                               in
                               match
                                 p_map
                                   st220
                                   (lam x307.
                                      lam x308.
                                        mulf (negf (subf currAge13 finalAge13)) (get x307 x308))
                                   x306
                               with
                                 (st221, x309)
                               in
                               match
                                 p_map
                                   st221
                                   (lam x310.
                                      subi (addi x310 1) 1)
                                   currState2
                               with
                                 (st222, x313)
                               in
                               p_apply st222 x309 x313
                             else match
                               p_map
                                 st218
                                 (lam x314.
                                    get x314 (subi nextIndex13 1))
                                 eventSeq42
                             with
                               (st223, nextEvent13)
                             in
                             match
                               p_map
                                 st223
                                 (lam x315.
                                    match x315 with Event1 x363
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
                               (st224, nextState2)
                             in
                             match
                               p_map
                                 st224
                                 (lam x316.
                                    match x316 with Event1 x353
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
                               (st225, nextAge2)
                             in
                             match
                               p_traverseSeq
                                 st225
                                 (lam st226.
                                    lam x317.
                                      p_traverseSeq
                                        st226
                                        (lam st227.
                                           lam x318.
                                             (st227, x318))
                                        x317)
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x333
                                  then
                                    x333.transitionProbs
                                  else
                                    let #var"239" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x319.
                                         map
                                           (lam x320.
                                              p_pure x320)
                                           x319)
                                      (exit 1))
                             with
                               (st228, x324)
                             in
                             match
                               p_map
                                 st228
                                 (lam x325.
                                    lam x326.
                                      get (get x325 x326))
                                 x324
                             with
                               (st229, x327)
                             in
                             match
                               p_map
                                 st229
                                 (lam x328.
                                    subi (addi x328 1) 1)
                                 currState2
                             with
                               (st230, x329)
                             in
                             match p_apply st230 x327 x329 with (st231, x330)
                             in
                             match
                               p_map
                                 st231
                                 (lam x334.
                                    subi (addi x334 1) 1)
                                 nextState2
                             with
                               (st232, x335)
                             in
                             match p_apply st232 x330 x335 with (st233, x336)
                             in
                             match log11 st233 x336 with (st234, x337)
                             in
                             match
                               p_map
                                 st234
                                 (lam x338.
                                    lam x339.
                                      lam x340.
                                        addf (subf x338 x339) x340)
                                 x337
                             with
                               (st235, x343)
                             in
                             match
                               p_map
                                 st235
                                 (lam x344.
                                    lam x345.
                                      mulf (subf currAge13 x344) x345)
                                 nextAge2
                             with
                               (st236, x346)
                             in
                             match
                               p_traverseSeq
                                 st236
                                 (lam st237.
                                    lam x347.
                                      (st237, x347))
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x348
                                  then
                                    x348.totalRates
                                  else
                                    let #var"240" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x349.
                                         p_pure x349)
                                      (exit 1))
                             with
                               (st238, x350)
                             in
                             match p_map st238 get x350 with (st239, x354)
                             in
                             match
                               p_map
                                 st239
                                 (lam x355.
                                    subi (addi x355 1) 1)
                                 currState2
                             with
                               (st240, x356)
                             in
                             match p_apply st240 x354 x356 with (st241, x357)
                             in
                             match p_apply st241 x346 x357 with (st242, x358)
                             in
                             match p_apply st242 x343 x358 with (st243, x359)
                             in
                             match
                               hostIndepLikelihood3
                                 st243
                                 (addi nextIndex13 1)
                                 nextState2
                                 finalState2
                                 nextAge2
                                 finalAge13
                                 eventSeq42
                                 embeddedQMatrix2
                             with
                               (st244, x360)
                             in
                             p_apply st244 x359 x360)
                        x300
    let hostIndepLikelihood3 =
      lam st245.
        lam nextIndex14.
          lam currState3.
            lam finalState3.
              lam currAge14.
                lam finalAge14.
                  lam eventSeq43.
                    lam embeddedQMatrix3.
                      match length14 st245 eventSeq43 with (st246, x364)
                      in
                      p_bind
                        st246
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st247.
                           lam x365.
                             match gti nextIndex14 x365 with true
                             then
                               match
                                 p_map
                                   st247
                                   (lam x366.
                                      lam x367.
                                        mulf (negf (subf x366 finalAge14)) x367)
                                   currAge14
                               with
                                 (st248, x368)
                               in
                               match
                                 p_traverseSeq
                                   st248
                                   (lam st249.
                                      lam x369.
                                        (st249, x369))
                                   (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3210
                                    then
                                      x3210.totalRates
                                    else
                                      let #var"241" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x370.
                                           p_pure x370)
                                        (exit 1))
                               with
                                 (st250, x371)
                               in
                               match p_map st250 get x371 with (st251, x372)
                               in
                               match
                                 p_map
                                   st251
                                   (lam x373.
                                      subi (addi x373 1) 1)
                                   currState3
                               with
                                 (st252, x374)
                               in
                               match p_apply st252 x372 x374 with (st253, x375)
                               in
                               p_apply st253 x368 x375
                             else match
                               p_map
                                 st247
                                 (lam x376.
                                    get x376 (subi nextIndex14 1))
                                 eventSeq43
                             with
                               (st254, nextEvent14)
                             in
                             match
                               p_map
                                 st254
                                 (lam x377.
                                    match x377 with Event1 x3610
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
                               (st255, nextState3)
                             in
                             match
                               p_map
                                 st255
                                 (lam x378.
                                    match x378 with Event1 x3510
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
                               (st256, nextAge3)
                             in
                             match
                               p_traverseSeq
                                 st256
                                 (lam st257.
                                    lam x379.
                                      p_traverseSeq
                                        st257
                                        (lam st258.
                                           lam x380.
                                             (st258, x380))
                                        x379)
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3310
                                  then
                                    x3310.transitionProbs
                                  else
                                    let #var"244" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x381.
                                         map
                                           (lam x382.
                                              p_pure x382)
                                           x381)
                                      (exit 1))
                             with
                               (st259, x383)
                             in
                             match
                               p_map
                                 st259
                                 (lam x384.
                                    lam x385.
                                      get (get x384 x385))
                                 x383
                             with
                               (st260, x386)
                             in
                             match
                               p_map
                                 st260
                                 (lam x387.
                                    subi (addi x387 1) 1)
                                 currState3
                             with
                               (st261, x388)
                             in
                             match p_apply st261 x386 x388 with (st262, x389)
                             in
                             match
                               p_map
                                 st262
                                 (lam x390.
                                    subi (addi x390 1) 1)
                                 nextState3
                             with
                               (st263, x391)
                             in
                             match p_apply st263 x389 x391 with (st264, x392)
                             in
                             match log11 st264 x392 with (st265, x393)
                             in
                             match
                               p_map
                                 st265
                                 (lam x394.
                                    lam x395.
                                      lam x396.
                                        addf (subf x394 x395) x396)
                                 x393
                             with
                               (st266, x397)
                             in
                             match
                               p_map
                                 st266
                                 (lam x398.
                                    lam x399.
                                      lam x400.
                                        mulf (subf x398 x399) x400)
                                 currAge14
                             with
                               (st267, x401)
                             in
                             match p_apply st267 x401 nextAge3 with (st268, x402)
                             in
                             match
                               p_traverseSeq
                                 st268
                                 (lam st269.
                                    lam x403.
                                      (st269, x403))
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3410
                                  then
                                    x3410.totalRates
                                  else
                                    let #var"245" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x404.
                                         p_pure x404)
                                      (exit 1))
                             with
                               (st270, x405)
                             in
                             match p_map st270 get x405 with (st271, x406)
                             in
                             match
                               p_map
                                 st271
                                 (lam x407.
                                    subi (addi x407 1) 1)
                                 currState3
                             with
                               (st272, x408)
                             in
                             match p_apply st272 x406 x408 with (st273, x409)
                             in
                             match p_apply st273 x402 x409 with (st274, x410)
                             in
                             match p_apply st274 x397 x410 with (st275, x411)
                             in
                             match
                               hostIndepLikelihood3
                                 st275
                                 (addi nextIndex14 1)
                                 nextState3
                                 finalState3
                                 nextAge3
                                 finalAge14
                                 eventSeq43
                                 embeddedQMatrix3
                             with
                               (st276, x412)
                             in
                             p_apply st276 x411 x412)
                        x364
  in
  let anon23 = lam x954.
      addi x954 1 in
  recursive
    let rec37 =
      lam i17.
        lam acc111.
          match geqi i17 0 with true
          then
            rec37 (subi i17 1) (cons (anon23 i17) acc111)
          else
            acc111
  in
  let anon24 =
    lam st609.
      lam msg1.
        lam nodeLabel51.
          lam x947.
            match
              hostMsgToProb st609 msg1 (addi x947 (muli nodeLabel51 0))
            with
              (st610, x948)
            in
            match
              p_traverseSeq
                st610
                (lam st611.
                   lam x949.
                     (st611, x949))
                x948
            with
              (st612, x950)
            in
            match
              p_map st612 (lam x952.
                   mkCategorical x952) x950
            with
              (st613, x953)
            in
            p_assume st613 simpleStoreAssume x953
  in
  recursive
    let rec15 =
      lam st277.
        lam c34.
          lam c35.
            lam s14.
              match s14 with [ _,
                  _ ] ++ _
              then
                match anon24 st277 c34 c35 (get s14 0) with (st278, x413)
                in
                match splitAt s14 1 with {#label"1" = x414}
                in
                match rec15 st278 c34 c35 x414 with (st279, x415)
                in
                (st279, cons x413 x415)
              else match s14 with [ e14 ]
              then
                match splitAt s14 1 with {#label"1" = x416}
                in
                let slice13 = x416 in
                match anon24 st277 c34 c35 e14 with (st280, x417)
                in
                (st280, [ x417 ])
              else match s14 with ""
              in
              (st277, "")
  in
  let suggestNodeRep =
    lam st608.
      lam msg.
        lam nHosts5.
          lam nodeLabel5.
            let i112 = subi (addi (subi nHosts5 1) 1) 1 in
            rec15
              st608
              msg
              nodeLabel5
              (match geqi i112 0 with true
               then
                 rec37 (subi i112 1) (cons (anon23 i112) "")
               else
                 "")
  in
  recursive
    let any =
      lam st281.
        lam seq.
          match null seq with true
          then
            (st281, p_pure false)
          else match
            p_map st281 (lam x418.
                 eqi x418 2) (head seq)
          with
            (st282, x419)
          in
          p_bind
            st282
            simpleStoreSubmodel
            (simpleInit {})
            (lam st283.
               lam x420.
                 match x420 with true
                 then
                   (st283, p_pure true)
                 else
                   any st283 (tail seq))
            x419
  in
  let any1 = lam st607.
      lam l21.
        any st607 l21 in
  recursive
    let sampleHostHistoryRec =
      lam st284.
        lam currentState.
          lam finalState11.
            lam currentAge.
              lam finalAge2.
                lam host.
                  lam nodeLabel.
                    lam embeddedQMatrix11.
                      p_bind
                        st284
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st285.
                           lam x421.
                             match
                               match ltf x421 finalAge2 with true
                               then
                                 match
                                   p_map
                                     st285
                                     (lam x422.
                                        eqi x422 finalState11)
                                     currentState
                                 with
                                   (st286, x423)
                                 in
                                 match
                                   p_traverseSeq
                                     st286
                                     (lam st287.
                                        lam x424.
                                          (st287, x424))
                                     ""
                                 with
                                   (st288, x425)
                                 in
                                 (st288, Bridge1
                                   { success = x423, events = x425 })
                               else match
                                 p_traverseSeq
                                   st285
                                   (lam st289.
                                      lam x426.
                                        p_traverseSeq
                                          st289
                                          (lam st290.
                                             lam x427.
                                               (st290, x427))
                                          x426)
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x4010
                                    then
                                      x4010.transitionProbs
                                    else
                                      let #var"246" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 375:16-375:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x428.
                                           map
                                             (lam x429.
                                                p_pure x429)
                                             x428)
                                        (exit 1))
                               with
                                 (st291, x430)
                               in
                               match
                                 p_map
                                   st291
                                   (lam x431.
                                      lam x432.
                                        mkCategorical (get x431 x432))
                                   x430
                               with
                                 (st292, x433)
                               in
                               match
                                 p_map
                                   st292
                                   (lam x434.
                                      subi (addi x434 1) 1)
                                   currentState
                               with
                                 (st293, x435)
                               in
                               match p_apply st293 x433 x435 with (st294, x436)
                               in
                               match p_assume st294 simpleStoreAssume x436 with (st295, nextState11)
                               in
                               match
                                 p_traverseSeq
                                   st295
                                   (lam st296.
                                      lam x437.
                                        (st296, x437))
                                   (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x3910
                                    then
                                      x3910.totalRates
                                    else
                                      let #var"247" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 379:20-379:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x438.
                                           p_pure x438)
                                        (exit 1))
                               with
                                 (st297, x439)
                               in
                               match
                                 p_map
                                   st297
                                   (lam x440.
                                      lam x441.
                                        mkExponential
                                          (addf
                                             (addf (get x440 x441) (mulf (int2float host) 0.))
                                             (mulf (int2float nodeLabel) 0.)))
                                   x439
                               with
                                 (st298, x442)
                               in
                               match
                                 p_map
                                   st298
                                   (lam x443.
                                      subi (addi x443 1) 1)
                                   nextState11
                               with
                                 (st299, x444)
                               in
                               match p_apply st299 x442 x444 with (st300, x445)
                               in
                               match p_assume st300 simpleStoreAssume x445 with (st301, x446)
                               in
                               match
                                 p_map
                                   st301
                                   (lam x447.
                                      subf x421 x447)
                                   x446
                               with
                                 (st302, x448)
                               in
                               match
                                 sampleHostHistoryRec
                                   st302
                                   nextState11
                                   finalState11
                                   x448
                                   finalAge2
                                   host
                                   nodeLabel
                                   embeddedQMatrix11
                               with
                                 (st303, restOfHistory)
                               in
                               match
                                 p_map
                                   st303
                                   (lam x449.
                                      match x449 with Bridge1 x3710
                                      then
                                        x3710.success
                                      else
                                        let #var"248" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 397:18-397:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st304, x450)
                               in
                               match
                                 p_map
                                   st304
                                   (lam x451.
                                      lam x452.
                                        cons
                                          (Event1
                                             { host = host, toState = x451, eventTime = x421, fromState = x452 }))
                                   nextState11
                               with
                                 (st305, x453)
                               in
                               match p_apply st305 x453 currentState with (st306, x454)
                               in
                               match
                                 p_map
                                   st306
                                   (lam x455.
                                      match x455 with Bridge1 x3810
                                      then
                                        x3810.events
                                      else
                                        let #var"249" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 395:10-395:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory
                               with
                                 (st307, x456)
                               in
                               match p_apply st307 x454 x456 with (st308, x457)
                               in
                               (st308, Bridge1
                                 { success = x450, events = x457 })
                             with
                               (st309, x458)
                             in
                             match x458 with Bridge1 x459
                             in
                             match x459 with {success = x460}
                             in
                             match
                               p_map
                                 st309
                                 (lam x461.
                                    lam x462.
                                      Bridge1
                                        { success = x461, events = x462 })
                                 x460
                             with
                               (st310, x463)
                             in
                             match x459 with {events = x464}
                             in
                             p_apply st310 x463 x464)
                        currentAge
    let sampleHostHistoryRec1 =
      lam st311.
        lam currentState1.
          lam finalState12.
            lam currentAge1.
              lam finalAge21.
                lam host1.
                  lam nodeLabel1.
                    lam embeddedQMatrix12.
                      p_bind
                        st311
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st312.
                           lam x465.
                             match
                               match ltf x465 finalAge21 with true
                               then
                                 match
                                   p_map
                                     st312
                                     (lam x466.
                                        lam x467.
                                          eqi x466 x467)
                                     currentState1
                                 with
                                   (st313, x468)
                                 in
                                 match p_apply st313 x468 finalState12 with (st314, x469)
                                 in
                                 match
                                   p_traverseSeq
                                     st314
                                     (lam st315.
                                        lam x470.
                                          (st315, x470))
                                     ""
                                 with
                                   (st316, x471)
                                 in
                                 (st316, Bridge1
                                   { success = x469, events = x471 })
                               else match
                                 p_traverseSeq
                                   st312
                                   (lam st317.
                                      lam x472.
                                        p_traverseSeq
                                          st317
                                          (lam st318.
                                             lam x473.
                                               (st318, x473))
                                          x472)
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x4011
                                    then
                                      x4011.transitionProbs
                                    else
                                      let #var"250" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 375:16-375:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                      in
                                      map
                                        (lam x474.
                                           map
                                             (lam x475.
                                                p_pure x475)
                                             x474)
                                        (exit 1))
                               with
                                 (st319, x476)
                               in
                               match
                                 p_map
                                   st319
                                   (lam x477.
                                      lam x478.
                                        mkCategorical (get x477 x478))
                                   x476
                               with
                                 (st320, x479)
                               in
                               match
                                 p_map
                                   st320
                                   (lam x480.
                                      subi (addi x480 1) 1)
                                   currentState1
                               with
                                 (st321, x481)
                               in
                               match p_apply st321 x479 x481 with (st322, x482)
                               in
                               match p_assume st322 simpleStoreAssume x482 with (st323, nextState12)
                               in
                               match
                                 p_traverseSeq
                                   st323
                                   (lam st324.
                                      lam x483.
                                        (st324, x483))
                                   (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x3911
                                    then
                                      x3911.totalRates
                                    else
                                      let #var"251" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 379:20-379:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                      in
                                      map
                                        (lam x484.
                                           p_pure x484)
                                        (exit 1))
                               with
                                 (st325, x485)
                               in
                               match
                                 p_map
                                   st325
                                   (lam x486.
                                      lam x487.
                                        mkExponential
                                          (addf
                                             (addf (get x486 x487) (mulf (int2float host1) 0.))
                                             (mulf (int2float nodeLabel1) 0.)))
                                   x485
                               with
                                 (st326, x488)
                               in
                               match
                                 p_map
                                   st326
                                   (lam x489.
                                      subi (addi x489 1) 1)
                                   nextState12
                               with
                                 (st327, x490)
                               in
                               match p_apply st327 x488 x490 with (st328, x491)
                               in
                               match p_assume st328 simpleStoreAssume x491 with (st329, x492)
                               in
                               match
                                 p_map
                                   st329
                                   (lam x493.
                                      subf x465 x493)
                                   x492
                               with
                                 (st330, x494)
                               in
                               match
                                 sampleHostHistoryRec1
                                   st330
                                   nextState12
                                   finalState12
                                   x494
                                   finalAge21
                                   host1
                                   nodeLabel1
                                   embeddedQMatrix12
                               with
                                 (st331, restOfHistory1)
                               in
                               match
                                 p_map
                                   st331
                                   (lam x495.
                                      match x495 with Bridge1 x3711
                                      then
                                        x3711.success
                                      else
                                        let #var"252" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 397:18-397:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st332, x496)
                               in
                               match
                                 p_map
                                   st332
                                   (lam x497.
                                      lam x498.
                                        cons
                                          (Event1
                                             { host = host1, toState = x497, eventTime = x465, fromState = x498 }))
                                   nextState12
                               with
                                 (st333, x499)
                               in
                               match p_apply st333 x499 currentState1 with (st334, x500)
                               in
                               match
                                 p_map
                                   st334
                                   (lam x501.
                                      match x501 with Bridge1 x3811
                                      then
                                        x3811.events
                                      else
                                        let #var"253" =
                                          print
                                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 395:10-395:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                        in
                                        exit 1)
                                   restOfHistory1
                               with
                                 (st335, x502)
                               in
                               match p_apply st335 x500 x502 with (st336, x503)
                               in
                               (st336, Bridge1
                                 { success = x496, events = x503 })
                             with
                               (st337, x504)
                             in
                             match x504 with Bridge1 x505
                             in
                             match x505 with {success = x506}
                             in
                             match
                               p_map
                                 st337
                                 (lam x507.
                                    lam x508.
                                      Bridge1
                                        { success = x507, events = x508 })
                                 x506
                             with
                               (st338, x509)
                             in
                             match x505 with {events = x510}
                             in
                             p_apply st338 x509 x510)
                        currentAge1
  in
  let anon25 = lam x946.
      addi x946 1 in
  recursive
    let rec38 =
      lam i18.
        lam acc112.
          match geqi i18 0 with true
          then
            rec38 (subi i18 1) (cons (anon25 i18) acc112)
          else
            acc112
  in
  let create13 =
    lam l61.
      let i111 = subi l61 1 in
      match geqi i111 0 with true
      then
        rec38 (subi i111 1) (cons (anon25 i111) "")
      else
        ""
  in
  let anon26 =
    lam st595.
      lam startRep2.
        lam finalRep13.
          lam startAge2.
            lam finalAge33.
              lam nodeLabel13.
                lam modelParams32.
                  lam x928.
                    let startState1 = get startRep2 (subi x928 1) in
                    let embeddedQMatrix51 =
                      match modelParams32 with ModelParams1 x1162
                      then
                        x1162.embeddedQMatrix
                      else
                        let #var"2128" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 253:4-253:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st595
                        (lam st596.
                           lam x929.
                             (st596, x929))
                        (match embeddedQMatrix51 with EmbeddedMarkovChainMatrix1 x1202
                         then
                           x1202.totalRates
                         else
                           let #var"2125" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 344:18-344:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x930.
                                p_pure x930)
                             (exit 1))
                    with
                      (st597, x931)
                    in
                    match
                      p_map
                        st597
                        (lam x932.
                           lam x933.
                             mkExponential
                               (addf
                                  (addf (get x932 x933) (mulf (int2float x928) 0.))
                                  (mulf (int2float nodeLabel13) 0.)))
                        x931
                    with
                      (st598, x934)
                    in
                    match
                      p_map
                        st598
                        (lam x935.
                           subi (addi x935 1) 1)
                        startState1
                    with
                      (st599, x936)
                    in
                    match p_apply st599 x934 x936 with (st600, x937)
                    in
                    match p_assume st600 simpleStoreAssume x937 with (st601, x938)
                    in
                    match
                      p_map
                        st601
                        (lam x939.
                           subf startAge2 x939)
                        x938
                    with
                      (st602, x940)
                    in
                    match
                      sampleHostHistoryRec
                        st602
                        startState1
                        (get finalRep13 (subi x928 1))
                        x940
                        finalAge33
                        x928
                        nodeLabel13
                        embeddedQMatrix51
                    with
                      (st603, bridge1)
                    in
                    match
                      p_map
                        st603
                        (lam x941.
                           match x941 with Bridge1 x1192
                           then
                             x1192.success
                           else
                             let #var"2126" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 356:19-356:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge1
                    with
                      (st604, x942)
                    in
                    match bool2real st604 x942 with (st605, x943)
                    in
                    let st606 =
                      p_weight
                        st605
                        simpleStoreWeight
                        (lam x945.
                           externalLog
                             (addf
                                (addf x945 (mulf (int2float x928) 0.))
                                (mulf (int2float nodeLabel13) 0.)))
                        x943
                    in
                    let foo51 = {} in
                    p_map
                      st606
                      (lam x944.
                         match x944 with Bridge1 x1182
                         then
                           x1182.events
                         else
                           let #var"2127" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 357:9-357:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge1
  in
  let anon27 =
    lam st583.
      lam startRep1.
        lam finalRep12.
          lam startAge1.
            lam finalAge32.
              lam nodeLabel12.
                lam modelParams31.
                  lam x908.
                    let startState = get startRep1 (subi x908 1) in
                    let embeddedQMatrix5 =
                      match modelParams31 with ModelParams1 x1161
                      then
                        x1161.embeddedQMatrix
                      else
                        let #var"2124" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 253:4-253:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st583
                        (lam st584.
                           lam x909.
                             (st584, x909))
                        (match embeddedQMatrix5 with EmbeddedMarkovChainMatrix1 x1201
                         then
                           x1201.totalRates
                         else
                           let #var"2121" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 344:18-344:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x910.
                                p_pure x910)
                             (exit 1))
                    with
                      (st585, x912)
                    in
                    match
                      p_map
                        st585
                        (lam x913.
                           lam x914.
                             mkExponential
                               (addf
                                  (addf (get x913 x914) (mulf (int2float x908) 0.))
                                  (mulf (int2float nodeLabel12) 0.)))
                        x912
                    with
                      (st586, x915)
                    in
                    match
                      p_map
                        st586
                        (lam x916.
                           subi (addi x916 1) 1)
                        startState
                    with
                      (st587, x917)
                    in
                    match p_apply st587 x915 x917 with (st588, x918)
                    in
                    match p_assume st588 simpleStoreAssume x918 with (st589, x919)
                    in
                    match
                      p_map
                        st589
                        (lam x920.
                           subf startAge1 x920)
                        x919
                    with
                      (st590, x922)
                    in
                    match
                      sampleHostHistoryRec1
                        st590
                        startState
                        (get finalRep12 (subi x908 1))
                        x922
                        finalAge32
                        x908
                        nodeLabel12
                        embeddedQMatrix5
                    with
                      (st591, bridge)
                    in
                    match
                      p_map
                        st591
                        (lam x923.
                           match x923 with Bridge1 x1191
                           then
                             x1191.success
                           else
                             let #var"2122" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 356:19-356:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge
                    with
                      (st592, x924)
                    in
                    match bool2real st592 x924 with (st593, x925)
                    in
                    let st594 =
                      p_weight
                        st593
                        simpleStoreWeight
                        (lam x927.
                           externalLog
                             (addf
                                (addf x927 (mulf (int2float x908) 0.))
                                (mulf (int2float nodeLabel12) 0.)))
                        x925
                    in
                    let foo5 = {} in
                    p_map
                      st594
                      (lam x926.
                         match x926 with Bridge1 x1181
                         then
                           x1181.events
                         else
                           let #var"2123" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 357:9-357:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge
  in
  recursive
    let rec16 =
      lam st339.
        lam c36.
          lam c37.
            lam c38.
              lam c39.
                lam c40.
                  lam c41.
                    lam s15.
                      match s15 with [ _,
                          _ ] ++ _
                      then
                        match
                          anon26 st339 c36 c37 c38 c39 c40 c41 (get s15 0)
                        with
                          (st340, x511)
                        in
                        match splitAt s15 1 with {#label"1" = x512}
                        in
                        match rec16 st340 c36 c37 c38 c39 c40 c41 x512 with (st341, x513)
                        in
                        (st341, cons x511 x513)
                      else match s15 with [ e15 ]
                      then
                        match splitAt s15 1 with {#label"1" = x514}
                        in
                        let slice14 = x514 in
                        match anon26 st339 c36 c37 c38 c39 c40 c41 e15 with (st342, x515)
                        in
                        (st342, [ x515 ])
                      else match s15 with ""
                      in
                      (st339, "")
    let rec17 =
      lam st343.
        lam c42.
          lam c43.
            lam c44.
              lam c45.
                lam c46.
                  lam c47.
                    lam s16.
                      match s16 with [ _,
                          _ ] ++ _
                      then
                        match
                          anon27 st343 c42 c43 c44 c45 c46 c47 (get s16 0)
                        with
                          (st344, x516)
                        in
                        match splitAt s16 1 with {#label"1" = x517}
                        in
                        match rec17 st344 c42 c43 c44 c45 c46 c47 x517 with (st345, x518)
                        in
                        (st345, cons x516 x518)
                      else match s16 with [ e16 ]
                      then
                        match splitAt s16 1 with {#label"1" = x519}
                        in
                        let slice15 = x519 in
                        match anon27 st343 c42 c43 c44 c45 c46 c47 e16 with (st346, x520)
                        in
                        (st346, [ x520 ])
                      else match s16 with ""
                      in
                      (st343, "")
  in
  let anon28 =
    lam h2.
      lam x907.
        lti
          (match
             isNaN1
               (match h2 with Event1 x1211
                then
                  x1211.eventTime
                else
                  let #var"2117" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 293:12-293:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             negi 1
           else match
             isNaN1
               (match x907 with Event1 x1261
                then
                  x1261.eventTime
                else
                  let #var"2118" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 296:12-296:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             1
           else match
             geqf
               (match h2 with Event1 x1271
                then
                  x1271.eventTime
                else
                  let #var"2119" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 299:6-299:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
                  in
                  exit 1)
               (match x907 with Event1 x1281
                then
                  x1281.eventTime
                else
                  let #var"2120" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 299:25-299:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
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
      lam c48.
        lam l.
          lam r.
            lam seq1.
              match seq1 with [ _ ] ++ _
              then
                let s41 = get seq1 0 in
                match splitAt seq1 1 with {#label"1" = x521}
                in
                let seq2 = x521 in
                match anon28 c48 s41 with true
                then
                  work11 c48 (cons s41 l) r seq2
                else
                  work11 c48 l (cons s41 r) seq2
              else match seq1 with ""
              in
              (l, r)
    let work12 =
      lam c49.
        lam l1.
          lam r1.
            lam seq11.
              match seq11 with [ _ ] ++ _
              then
                let s42 = get seq11 0 in
                match splitAt seq11 1 with {#label"1" = x522}
                in
                let seq21 = x522 in
                match anon28 c49 s42 with true
                then
                  work12 c49 (cons s42 l1) r1 seq21
                else
                  work11 c49 l1 (cons s42 r1) seq21
              else match seq11 with ""
              in
              (l1, r1)
    let work13 =
      lam c50.
        lam l2.
          lam r2.
            lam seq12.
              match seq12 with [ _ ] ++ _
              then
                let s43 = get seq12 0 in
                match splitAt seq12 1 with {#label"1" = x523}
                in
                let seq22 = x523 in
                match anon28 c50 s43 with true
                then
                  work11 c50 (cons s43 l2) r2 seq22
                else
                  work13 c50 l2 (cons s43 r2) seq22
              else match seq12 with ""
              in
              (l2, r2)
    let work14 =
      lam c51.
        lam l3.
          lam r3.
            lam seq13.
              match seq13 with [ _ ] ++ _
              then
                let s44 = get seq13 0 in
                match splitAt seq13 1 with {#label"1" = x524}
                in
                let seq23 = x524 in
                match anon28 c51 s44 with true
                then
                  work12 c51 (cons s44 l3) r3 seq23
                else
                  work13 c51 l3 (cons s44 r3) seq23
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
      lam st347.
        lam seq31.
          p_map
            st347
            (lam x525.
               match null x525 with true
               then
                 x525
               else
                 let h1 = head x525 in
                 let lr1 = work14 h1 "" "" (reverse (tail x525)) in
                 match lr1 with (#var"X6",)
                 in
                 match lr1 with {#label"1" = #var"X7"}
                 in
                 concat (quickSort #var"X6") (cons h1 (quickSort #var"X7")))
            seq31
  in
  recursive
    let rec214 =
      lam st348.
        lam c52.
          lam c53.
            lam c54.
              lam c55.
                lam c56.
                  lam c57.
                    lam acc20.
                      lam s215.
                        match s215 with [ _ ] ++ _
                        then
                          let x526 = get s215 0 in
                          match
                            p_map
                              st348
                              (lam x527.
                                 lam x528.
                                   addf x527 x528)
                              acc20
                          with
                            (st349, x529)
                          in
                          match
                            hostIndepLikelihood
                              st349
                              1
                              (get c52 (subi x526 1))
                              (get c53 (subi x526 1))
                              c54
                              c55
                              (get c57 (subi x526 1))
                              (match c56 with ModelParams1 x1421
                               then
                                 x1421.embeddedQMatrix
                               else
                                 let #var"254" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st350, x530)
                          in
                          match p_apply st350 x529 x530 with (st351, x531)
                          in
                          match splitAt s215 1 with {#label"1" = x532}
                          in
                          rec214 st351 c52 c53 c54 c55 c56 c57 x531 x532
                        else match s215 with ""
                        in
                        (st348, acc20)
    let rec215 =
      lam st352.
        lam c58.
          lam c59.
            lam c60.
              lam c61.
                lam c62.
                  lam c63.
                    lam acc23.
                      lam s216.
                        match s216 with [ _ ] ++ _
                        then
                          let x533 = get s216 0 in
                          match
                            p_map
                              st352
                              (lam x534.
                                 lam x535.
                                   addf x534 x535)
                              acc23
                          with
                            (st353, x536)
                          in
                          match
                            hostIndepLikelihood2
                              st353
                              1
                              (get c58 (subi x533 1))
                              (get c59 (subi x533 1))
                              c60
                              c61
                              (get c63 (subi x533 1))
                              (match c62 with ModelParams1 x1422
                               then
                                 x1422.embeddedQMatrix
                               else
                                 let #var"255" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st354, x537)
                          in
                          match p_apply st354 x536 x537 with (st355, x538)
                          in
                          match splitAt s216 1 with {#label"1" = x539}
                          in
                          rec215 st355 c58 c59 c60 c61 c62 c63 x538 x539
                        else match s216 with ""
                        in
                        (st352, acc23)
  in
  let anon29 = lam x906.
      addi x906 1 in
  recursive
    let rec39 =
      lam i19.
        lam acc113.
          match geqi i19 0 with true
          then
            rec39 (subi i19 1) (cons (anon29 i19) acc113)
          else
            acc113
  in
  let create14 =
    lam l6.
      let i110 = subi l6 1 in
      match geqi i110 0 with true
      then
        rec39 (subi i110 1) (cons (anon29 i110) "")
      else
        ""
  in
  recursive
    let rec216 =
      lam st356.
        lam acc24.
          lam s217.
            match s217 with [ _ ] ++ _
            then
              match
                p_map
                  st356
                  (lam x540.
                     lam x541.
                       addf x540 x541)
                  acc24
              with
                (st357, x542)
              in
              match p_apply st357 x542 (get s217 0) with (st358, x543)
              in
              match splitAt s217 1 with {#label"1" = x544}
              in
              rec216 st358 x543 x544
            else match s217 with ""
            in
            (st356, acc24)
  in
  let fold =
    lam st581.
      lam init1.
        lam seq5.
          match seq5 with [ _ ] ++ _
          then
            match
              p_map
                st581
                (lam x903.
                   addf init1 x903)
                (get seq5 0)
            with
              (st582, x904)
            in
            match splitAt seq5 1 with {#label"1" = x905}
            in
            rec216 st582 x904 x905
          else match seq5 with ""
          in
          (st581, p_pure init1)
  in
  recursive
    let rec217 =
      lam st359.
        lam c64.
          lam acc25.
            lam s218.
              match s218 with [ _ ] ++ _
              then
                match acc25 with (field, field1)
                in
                match
                  match field1 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st359
                        (lam x545.
                           addi x545 1)
                        (get field1 0)
                    with
                      (st360, x546)
                    in
                    match mtxGet1 st360 x546 (addi (get s218 0) 1) c64 with (st361, x547)
                    in
                    match log11 st361 x547 with (st362, x548)
                    in
                    match splitAt field1 1 with {#label"1" = x549}
                    in
                    (st362, (snoc field x548, x549))
                  else
                    let x550 = error "foldl2: Cannot happen!" in
                    match x550 with (x551,)
                    in
                    match x550 with {#label"1" = x552}
                    in
                    (st359, (map (lam x553.
                         p_pure x553) x551, map (lam x554.
                         p_pure x554) x552))
                with
                  (st363, x555)
                in
                match splitAt s218 1 with {#label"1" = x556}
                in
                rec217 st363 c64 x555 x556
              else match s218 with ""
              in
              (st359, acc25)
    let rec218 =
      lam st364.
        lam c65.
          lam acc26.
            lam s219.
              match s219 with [ _ ] ++ _
              then
                match acc26 with (field2, field3)
                in
                match
                  match field3 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st364
                        (lam x557.
                           addi x557 1)
                        (get field3 0)
                    with
                      (st365, x558)
                    in
                    match
                      p_map
                        st365
                        (lam x559.
                           addi x559 1)
                        (get s219 0)
                    with
                      (st366, x560)
                    in
                    match mtxGet2 st366 x558 x560 c65 with (st367, x561)
                    in
                    match log11 st367 x561 with (st368, x562)
                    in
                    match splitAt field3 1 with {#label"1" = x563}
                    in
                    (st368, (snoc field2 x562, x563))
                  else
                    let x564 = error "foldl2: Cannot happen!" in
                    match x564 with (x565,)
                    in
                    match x564 with {#label"1" = x566}
                    in
                    (st364, (map (lam x567.
                         p_pure x567) x565, map (lam x568.
                         p_pure x568) x566))
                with
                  (st369, x569)
                in
                match splitAt s219 1 with {#label"1" = x570}
                in
                rec218 st369 c65 x569 x570
              else match s219 with ""
              in
              (st364, acc26)
  in
  recursive
    let rec219 =
      lam st370.
        lam c66.
          lam acc27.
            lam s220.
              match s220 with [ _ ] ++ _
              then
                match acc27 with (field4, field5)
                in
                match
                  match field5 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st370
                        (lam x571.
                           addi x571 1)
                        (get s220 0)
                    with
                      (st371, x572)
                    in
                    match mtxGet1 st371 x572 (addi (get field5 0) 1) c66 with (st372, x573)
                    in
                    match log11 st372 x573 with (st373, x574)
                    in
                    match splitAt field5 1 with {#label"1" = x575}
                    in
                    (st373, (snoc field4 x574, x575))
                  else
                    let x576 = error "foldl2: Cannot happen!" in
                    match x576 with (x577,)
                    in
                    match x576 with {#label"1" = x578}
                    in
                    (st370, (map (lam x579.
                         p_pure x579) x577, x578))
                with
                  (st374, x580)
                in
                match splitAt s220 1 with {#label"1" = x581}
                in
                rec219 st374 c66 x580 x581
              else match s220 with ""
              in
              (st370, acc27)
    let rec220 =
      lam st375.
        lam c67.
          lam acc28.
            lam s221.
              match s221 with [ _ ] ++ _
              then
                match acc28 with (field6, field7)
                in
                match
                  match field7 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st375
                        (lam x582.
                           addi x582 1)
                        (get s221 0)
                    with
                      (st376, x583)
                    in
                    match
                      p_map
                        st376
                        (lam x584.
                           addi x584 1)
                        (get field7 0)
                    with
                      (st377, x585)
                    in
                    match mtxGet2 st377 x583 x585 c67 with (st378, x586)
                    in
                    match log11 st378 x586 with (st379, x587)
                    in
                    match splitAt field7 1 with {#label"1" = x588}
                    in
                    (st379, (snoc field6 x587, x588))
                  else
                    let x589 = error "foldl2: Cannot happen!" in
                    match x589 with (x590,)
                    in
                    match x589 with {#label"1" = x591}
                    in
                    (st375, (map (lam x592.
                         p_pure x592) x590, map (lam x593.
                         p_pure x593) x591))
                with
                  (st380, x594)
                in
                match splitAt s221 1 with {#label"1" = x595}
                in
                rec220 st380 c67 x594 x595
              else match s221 with ""
              in
              (st375, acc28)
  in
  let sampleBranch =
    lam st531.
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
                          st531
                          startRep
                          finalRep11
                          startAge
                          finalAge31
                          nodeLabel11
                          modelParams3
                          (create13 (addi (subi nHosts2 1) 1))
                      with
                        (st532, unorderedBranch1)
                      in
                      match paste01 st532 unorderedBranch1 with (st533, x814)
                      in
                      match quickSort1 st533 x814 with (st534, orderedEvents1)
                      in
                      match length14 st534 orderedEvents1 with (st535, nEvents41)
                      in
                      match
                        allTimesValidBranch st535 startRep orderedEvents1 1 nEvents41 nHosts2
                      with
                        (st536, x815)
                      in
                      p_bind
                        st536
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st537.
                           lam x816.
                             match
                               match x816 with true
                               then
                                 let s223 = create14 (addi (subi (length12 unorderedBranch1) 1) 1)
                                 in
                                 match
                                   match s223 with [ _ ] ++ _
                                   then
                                     let x817 = get s223 0 in
                                     match
                                       hostIndepLikelihood2
                                         st537
                                         1
                                         (get startRep (subi x817 1))
                                         (get finalRep11 (subi x817 1))
                                         startAge
                                         finalAge31
                                         (get unorderedBranch1 (subi x817 1))
                                         (match modelParams3 with ModelParams1 x1424
                                          then
                                            x1424.embeddedQMatrix
                                          else
                                            let #var"2112" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                            in
                                            exit 1)
                                     with
                                       (st538, x818)
                                     in
                                     match
                                       p_map
                                         st538
                                         (lam x819.
                                            addf 0. x819)
                                         x818
                                     with
                                       (st539, x820)
                                     in
                                     match splitAt s223 1 with {#label"1" = x821}
                                     in
                                     rec215
                                       st539
                                       startRep
                                       finalRep11
                                       startAge
                                       finalAge31
                                       modelParams3
                                       unorderedBranch1
                                       x820
                                       x821
                                   else match s223 with ""
                                   in
                                   (st537, p_pure 0.)
                                 with
                                   (st540, x822)
                                 in
                                 match
                                   p_map
                                     st540
                                     (lam x823.
                                        lam x824.
                                          subf x823 x824)
                                     x822
                                 with
                                   (st541, x825)
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
                                                 st541
                                                 (lam x826.
                                                    addi x826 1)
                                                 (get field17 0)
                                             with
                                               (st542, x827)
                                             in
                                             match
                                               p_map
                                                 st542
                                                 (lam x828.
                                                    addi x828 1)
                                                 (get finalRep11 0)
                                             with
                                               (st543, x829)
                                             in
                                             match mtxGet2 st543 x827 x829 branchKernel1 with (st544, x830)
                                             in
                                             match log11 st544 x830 with (st545, x831)
                                             in
                                             match splitAt field17 1 with {#label"1" = x832}
                                             in
                                             (st545, (snoc field16 x831, x832))
                                           else
                                             let x833 = error "foldl2: Cannot happen!" in
                                             match x833 with (x834,)
                                             in
                                             match x833 with {#label"1" = x835}
                                             in
                                             (st541, (map
                                               (lam x836.
                                                  p_pure x836)
                                               x834, map
                                               (lam x837.
                                                  p_pure x837)
                                               x835))
                                         with
                                           (st546, x838)
                                         in
                                         match splitAt finalRep11 1 with {#label"1" = x839}
                                         in
                                         rec218 st546 branchKernel1 x838 x839
                                       else match finalRep11 with ""
                                       in
                                       (st541, acc33)
                                     with
                                       (st547, x840)
                                     in
                                     match x840 with (field18, field19)
                                     in
                                     (st547, field18)
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
                                                 st541
                                                 (lam x841.
                                                    addi x841 1)
                                                 (get startRep 0)
                                             with
                                               (st548, x842)
                                             in
                                             match
                                               p_map
                                                 st548
                                                 (lam x843.
                                                    addi x843 1)
                                                 (get field21 0)
                                             with
                                               (st549, x844)
                                             in
                                             match mtxGet2 st549 x842 x844 branchKernel1 with (st550, x845)
                                             in
                                             match log11 st550 x845 with (st551, x846)
                                             in
                                             match splitAt field21 1 with {#label"1" = x847}
                                             in
                                             (st551, (snoc field20 x846, x847))
                                           else
                                             let x848 = error "foldl2: Cannot happen!" in
                                             match x848 with (x849,)
                                             in
                                             match x848 with {#label"1" = x850}
                                             in
                                             (st541, (map
                                               (lam x851.
                                                  p_pure x851)
                                               x849, map
                                               (lam x852.
                                                  p_pure x852)
                                               x850))
                                         with
                                           (st552, x853)
                                         in
                                         match splitAt startRep 1 with {#label"1" = x854}
                                         in
                                         rec220 st552 branchKernel1 x853 x854
                                       else match startRep with ""
                                       in
                                       (st541, acc34)
                                     with
                                       (st553, x855)
                                     in
                                     match x855 with (field22, field23)
                                     in
                                     (st553, field22)
                                 with
                                   (st554, x856)
                                 in
                                 match fold st554 0. x856 with (st555, x857)
                                 in
                                 match p_apply st555 x825 x857 with (st556, x858)
                                 in
                                 match
                                   p_bind
                                     st556
                                     simpleStoreSubmodel
                                     (simpleInit {})
                                     (lam st557.
                                        lam x859.
                                          match gti 1 x859 with true
                                          then
                                            match
                                              getTotalRate st557 startRep modelParams3 nHosts2
                                            with
                                              (st558, x860)
                                            in
                                            p_map
                                              st558
                                              (lam x861.
                                                 mulf (negf (subf startAge finalAge31)) x861)
                                              x860
                                          else match
                                            p_map
                                              st557
                                              (lam x862.
                                                 get x862 (subi 1 1))
                                              orderedEvents1
                                          with
                                            (st559, nextEvent3)
                                          in
                                          match
                                            p_map
                                              st559
                                              (lam x863.
                                                 match x863 with Event1 x3111
                                                 then
                                                   x3111.eventTime
                                                 else
                                                   let #var"2113" =
                                                     print
                                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 25:17-25:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                   in
                                                   exit 1)
                                              nextEvent3
                                          with
                                            (st560, newAge3)
                                          in
                                          match
                                            getTotalRate st560 startRep modelParams3 nHosts2
                                          with
                                            (st561, totalLeavingRate13)
                                          in
                                          match
                                            p_map
                                              st561
                                              (lam x864.
                                                 match x864 with Event1 x1453
                                                 then
                                                   x1453.host
                                                 else
                                                   let #var"2114" =
                                                     print
                                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                   in
                                                   exit 1)
                                              nextEvent3
                                          with
                                            (st562, hostIndex13)
                                          in
                                          match
                                            p_map
                                              st562
                                              (lam x865.
                                                 lam x866.
                                                   lam st563.
                                                     match
                                                       gti
                                                         (match x865 with Event1 x1434
                                                          then
                                                            x1434.fromState
                                                          else
                                                            let #var"2115" =
                                                              print
                                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                            in
                                                            exit 1)
                                                         x866
                                                     with
                                                       true
                                                     then
                                                       getLossRate2 st563 startRep hostIndex13 modelParams3
                                                     else
                                                       getGainRate2 st563 startRep hostIndex13 modelParams3)
                                              nextEvent3
                                          with
                                            (st564, x867)
                                          in
                                          match
                                            p_map
                                              st564
                                              (lam x868.
                                                 match x868 with Event1 x1444
                                                 then
                                                   x1444.toState
                                                 else
                                                   let #var"2116" =
                                                     print
                                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                   in
                                                   exit 1)
                                              nextEvent3
                                          with
                                            (st565, x869)
                                          in
                                          match
                                            p_subApply st565 simpleStoreSubmodel (simpleInit {}) x867 x869
                                          with
                                            (st566, x870)
                                          in
                                          match p_join st566 x870 with (st567, x871)
                                          in
                                          match
                                            p_map
                                              st567
                                              (lam x872.
                                                 lam x873.
                                                   divf x872 x873)
                                              x871
                                          with
                                            (st568, x874)
                                          in
                                          match p_apply st568 x874 totalLeavingRate13 with (st569, x875)
                                          in
                                          match log11 st569 x875 with (st570, x876)
                                          in
                                          match
                                            p_map
                                              st570
                                              (lam x877.
                                                 lam x878.
                                                   lam x879.
                                                     addf (subf x877 x878) x879)
                                              x876
                                          with
                                            (st571, x880)
                                          in
                                          match
                                            p_map
                                              st571
                                              (lam x882.
                                                 lam x883.
                                                   mulf (subf startAge x882) x883)
                                              newAge3
                                          with
                                            (st572, x884)
                                          in
                                          match p_apply st572 x884 totalLeavingRate13 with (st573, x885)
                                          in
                                          match p_apply st573 x880 x885 with (st574, x886)
                                          in
                                          match
                                            updateRepertoire st574 startRep nextEvent3 nHosts2
                                          with
                                            (st575, x887)
                                          in
                                          match
                                            fullModelWeight1
                                              st575
                                              (addi 1 1)
                                              x887
                                              finalRep11
                                              newAge3
                                              finalAge31
                                              orderedEvents1
                                              x859
                                              nHosts2
                                              modelParams3
                                          with
                                            (st576, x888)
                                          in
                                          p_apply st576 x886 x888)
                                     nEvents41
                                 with
                                   (st577, x889)
                                 in
                                 (st577, CorrectedBranchSample1
                                   { history = orderedEvents1,
                                     logSamplingDensity = x858,
                                     logModelDensity = x889,
                                     success = true })
                               else
                                 (st537, CorrectedBranchSample1
                                   { history = orderedEvents1,
                                     logSamplingDensity = p_pure 0.,
                                     logModelDensity = p_pure (log1 0.),
                                     success = false })
                             with
                               (st578, x890)
                             in
                             match x890 with CorrectedBranchSample1 x892
                             in
                             match x892 with {history = x893}
                             in
                             match
                               p_map
                                 st578
                                 (lam x894.
                                    lam x895.
                                      lam x896.
                                        match x892 with {success = x897}
                                        in
                                        CorrectedBranchSample1
                                          { history = x894,
                                            logSamplingDensity = x895,
                                            logModelDensity = x896,
                                            success = x897 })
                                 x893
                             with
                               (st579, x898)
                             in
                             match x892 with {logSamplingDensity = x899}
                             in
                             match p_apply st579 x898 x899 with (st580, x900)
                             in
                             match x892 with {logModelDensity = x902}
                             in
                             p_apply st580 x900 x902)
                        x815
  in
  recursive
    let sampleTreeHistory =
      lam st381.
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 167:14-167:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 173:6-173:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                            in
                            exit 1
                        in
                        match
                          rec16
                            st381
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
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 175:6-175:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create13 (addi (subi nHosts 1) 1))
                        with
                          (st382, unorderedBranch)
                        in
                        match paste01 st382 unorderedBranch with (st383, x596)
                        in
                        match quickSort1 st383 x596 with (st384, orderedEvents)
                        in
                        match length14 st384 orderedEvents with (st385, nEvents4)
                        in
                        match
                          allTimesValidBranch st385 parentRep orderedEvents 1 nEvents4 nHosts
                        with
                          (st386, x597)
                        in
                        match
                          p_bind
                            st386
                            simpleStoreSubmodel
                            (simpleInit {})
                            (lam st387.
                               lam x598.
                                 match
                                   match x598 with true
                                   then
                                     let s222 = create14 (addi (subi (length12 unorderedBranch) 1) 1)
                                     in
                                     match
                                       match s222 with [ _ ] ++ _
                                       then
                                         let x599 = get s222 0 in
                                         match
                                           hostIndepLikelihood
                                             st387
                                             1
                                             (get parentRep (subi x599 1))
                                             (get rep1 (subi x599 1))
                                             parentAge
                                             finalAge3
                                             (get unorderedBranch (subi x599 1))
                                             (match modelParams11 with ModelParams1 x1423
                                              then
                                                x1423.embeddedQMatrix
                                              else
                                                let #var"257" =
                                                  print
                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                                in
                                                exit 1)
                                         with
                                           (st388, x600)
                                         in
                                         match
                                           p_map
                                             st388
                                             (lam x601.
                                                addf 0. x601)
                                             x600
                                         with
                                           (st389, x602)
                                         in
                                         match splitAt s222 1 with {#label"1" = x603}
                                         in
                                         rec214
                                           st389
                                           parentRep
                                           rep1
                                           parentAge
                                           finalAge3
                                           modelParams11
                                           unorderedBranch
                                           x602
                                           x603
                                       else match s222 with ""
                                       in
                                       (st387, p_pure 0.)
                                     with
                                       (st390, x604)
                                     in
                                     match
                                       p_map
                                         st390
                                         (lam x605.
                                            lam x606.
                                              subf x605 x606)
                                         x604
                                     with
                                       (st391, x607)
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
                                                     st391
                                                     (lam x608.
                                                        addi x608 1)
                                                     (get field9 0)
                                                 with
                                                   (st392, x609)
                                                 in
                                                 match
                                                   mtxGet1 st392 x609 (addi (get rep1 0) 1) branchKernel
                                                 with
                                                   (st393, x610)
                                                 in
                                                 match log11 st393 x610 with (st394, x611)
                                                 in
                                                 match splitAt field9 1 with {#label"1" = x612}
                                                 in
                                                 (st394, (snoc field8 x611, x612))
                                               else
                                                 let x613 = error "foldl2: Cannot happen!" in
                                                 match x613 with (x614,)
                                                 in
                                                 match x613 with {#label"1" = x615}
                                                 in
                                                 (st391, (map
                                                   (lam x616.
                                                      p_pure x616)
                                                   x614, map
                                                   (lam x617.
                                                      p_pure x617)
                                                   x615))
                                             with
                                               (st395, x618)
                                             in
                                             match splitAt rep1 1 with {#label"1" = x619}
                                             in
                                             rec217 st395 branchKernel x618 x619
                                           else match rep1 with ""
                                           in
                                           (st391, acc29)
                                         with
                                           (st396, x620)
                                         in
                                         match x620 with (field10, field11)
                                         in
                                         (st396, field10)
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
                                                     st391
                                                     (lam x621.
                                                        addi x621 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st397, x622)
                                                 in
                                                 match
                                                   mtxGet1 st397 x622 (addi (get field13 0) 1) branchKernel
                                                 with
                                                   (st398, x623)
                                                 in
                                                 match log11 st398 x623 with (st399, x624)
                                                 in
                                                 match splitAt field13 1 with {#label"1" = x625}
                                                 in
                                                 (st399, (snoc field12 x624, x625))
                                               else
                                                 let x626 = error "foldl2: Cannot happen!" in
                                                 match x626 with (x627,)
                                                 in
                                                 match x626 with {#label"1" = x628}
                                                 in
                                                 (st391, (map
                                                   (lam x629.
                                                      p_pure x629)
                                                   x627, x628))
                                             with
                                               (st400, x630)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x631}
                                             in
                                             rec219 st400 branchKernel x630 x631
                                           else match parentRep with ""
                                           in
                                           (st391, acc30)
                                         with
                                           (st401, x632)
                                         in
                                         match x632 with (field14, field15)
                                         in
                                         (st401, field14)
                                     with
                                       (st402, x633)
                                     in
                                     match fold st402 0. x633 with (st403, x634)
                                     in
                                     match p_apply st403 x607 x634 with (st404, x635)
                                     in
                                     match
                                       p_bind
                                         st404
                                         simpleStoreSubmodel
                                         (simpleInit {})
                                         (lam st405.
                                            lam x636.
                                              match gti 1 x636 with true
                                              then
                                                match
                                                  getTotalRate st405 parentRep modelParams11 nHosts
                                                with
                                                  (st406, x637)
                                                in
                                                p_map
                                                  st406
                                                  (lam x638.
                                                     mulf (negf (subf parentAge finalAge3)) x638)
                                                  x637
                                              else match
                                                p_map
                                                  st405
                                                  (lam x639.
                                                     get x639 (subi 1 1))
                                                  orderedEvents
                                              with
                                                (st407, nextEvent2)
                                              in
                                              match
                                                p_map
                                                  st407
                                                  (lam x640.
                                                     match x640 with Event1 x3110
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
                                                (st408, newAge2)
                                              in
                                              match
                                                getTotalRate st408 parentRep modelParams11 nHosts
                                              with
                                                (st409, totalLeavingRate12)
                                              in
                                              match
                                                p_map
                                                  st409
                                                  (lam x641.
                                                     match x641 with Event1 x1452
                                                     then
                                                       x1452.host
                                                     else
                                                       let #var"259" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st410, hostIndex12)
                                              in
                                              match
                                                p_map
                                                  st410
                                                  (lam x642.
                                                     lam x643.
                                                       lam st411.
                                                         match
                                                           gti
                                                             (match x642 with Event1 x1433
                                                              then
                                                                x1433.fromState
                                                              else
                                                                let #var"260" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x643
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st411 parentRep hostIndex12 modelParams11
                                                         else
                                                           getGainRate2 st411 parentRep hostIndex12 modelParams11)
                                                  nextEvent2
                                              with
                                                (st412, x644)
                                              in
                                              match
                                                p_map
                                                  st412
                                                  (lam x645.
                                                     match x645 with Event1 x1443
                                                     then
                                                       x1443.toState
                                                     else
                                                       let #var"261" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st413, x646)
                                              in
                                              match
                                                p_subApply st413 simpleStoreSubmodel (simpleInit {}) x644 x646
                                              with
                                                (st414, x647)
                                              in
                                              match p_join st414 x647 with (st415, x648)
                                              in
                                              match
                                                p_map
                                                  st415
                                                  (lam x649.
                                                     lam x650.
                                                       divf x649 x650)
                                                  x648
                                              with
                                                (st416, x651)
                                              in
                                              match p_apply st416 x651 totalLeavingRate12 with (st417, x652)
                                              in
                                              match log11 st417 x652 with (st418, x653)
                                              in
                                              match
                                                p_map
                                                  st418
                                                  (lam x654.
                                                     lam x655.
                                                       lam x656.
                                                         addf (subf x654 x655) x656)
                                                  x653
                                              with
                                                (st419, x657)
                                              in
                                              match
                                                p_map
                                                  st419
                                                  (lam x658.
                                                     lam x659.
                                                       mulf (subf parentAge x658) x659)
                                                  newAge2
                                              with
                                                (st420, x660)
                                              in
                                              match p_apply st420 x660 totalLeavingRate12 with (st421, x661)
                                              in
                                              match p_apply st421 x657 x661 with (st422, x662)
                                              in
                                              match
                                                updateRepertoire st422 parentRep nextEvent2 nHosts
                                              with
                                                (st423, x663)
                                              in
                                              match
                                                fullModelWeight
                                                  st423
                                                  (addi 1 1)
                                                  x663
                                                  rep1
                                                  newAge2
                                                  finalAge3
                                                  orderedEvents
                                                  x636
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st424, x664)
                                              in
                                              p_apply st424 x662 x664)
                                         nEvents4
                                     with
                                       (st425, x665)
                                     in
                                     (st425, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = x635,
                                         logModelDensity = x665,
                                         success = true })
                                   else
                                     (st387, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = p_pure 0.,
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st426, x666)
                                 in
                                 match x666 with CorrectedBranchSample1 x667
                                 in
                                 match x667 with {history = x668}
                                 in
                                 match
                                   p_map
                                     st426
                                     (lam x669.
                                        lam x670.
                                          lam x671.
                                            match x667 with {success = x672}
                                            in
                                            CorrectedBranchSample1
                                              { history = x669,
                                                logSamplingDensity = x670,
                                                logModelDensity = x671,
                                                success = x672 })
                                     x668
                                 with
                                   (st427, x673)
                                 in
                                 match x667 with {logSamplingDensity = x674}
                                 in
                                 match p_apply st427 x673 x674 with (st428, x675)
                                 in
                                 match x667 with {logModelDensity = x676}
                                 in
                                 p_apply st428 x675 x676)
                            x597
                        with
                          (st429, branchSample)
                        in
                        match
                          p_map
                            st429
                            (lam x677.
                               lam x678.
                                 mulf
                                   (subf
                                      (match x677 with CorrectedBranchSample1 x4610
                                       then
                                         x4610.logModelDensity
                                       else
                                         let #var"262" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 181:15-181:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x678)
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
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 181:90-181:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1))
                                         0.)))
                            branchSample
                        with
                          (st430, x679)
                        in
                        match
                          p_map
                            st430
                            (lam x680.
                               match x680 with CorrectedBranchSample1 x4710
                               then
                                 x4710.logSamplingDensity
                               else
                                 let #var"264" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 181:46-181:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st431, x681)
                        in
                        match p_apply st431 x679 x681 with (st432, x682)
                        in
                        let st433 =
                          p_weight
                            st432
                            simpleStoreWeight
                            (/-temp-/lam x685.
                               x685)
                            x682
                        in
                        let foo = {} in
                        match
                          p_map
                            st433
                            (lam x683.
                               match x683 with CorrectedBranchSample1 x4510
                               then
                                 x4510.history
                               else
                                 let #var"265" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 187:16-187:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st434, x684)
                        in
                        (st434, HistoryLeaf
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
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 184:12-184:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 185:14-185:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            history = x684,
                            repertoire = rep1 })
                      else match
                        mtxElemMul
                          st381
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 190:34-190:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                             in
                             p_pure (exit 1))
                          preorderMsg
                      with
                        (st435, samplingProb)
                      in
                      match
                        suggestNodeRep
                          st435
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 191:51-191:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                             in
                             exit 1)
                      with
                        (st436, rep2)
                      in
                      match any1 st436 rep2 with (st437, x686)
                      in
                      match bool2real st437 x686 with (st438, x687)
                      in
                      let st439 =
                        p_weight
                          st438
                          simpleStoreWeight
                          (lam x708.
                             externalLog
                               (addf
                                  x708
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
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 193:43-193:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1))
                                     0.)))
                          x687
                      in
                      let foo1 = {} in
                      match
                        sampleBranch
                          st439
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 201:6-201:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 203:6-203:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                             in
                             exit 1)
                          modelParams11
                          branchKernel
                      with
                        (st440, branchSample1)
                      in
                      match
                        p_map
                          st440
                          (lam x688.
                             lam x689.
                               lam x690.
                                 subf
                                   (subf
                                      (match x688 with CorrectedBranchSample1 x701
                                       then
                                         x701.logModelDensity
                                       else
                                         let #var"274" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 209:14-209:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x689)
                                   x690)
                          branchSample1
                      with
                        (st441, x691)
                      in
                      match
                        p_map
                          st441
                          (lam x692.
                             match x692 with CorrectedBranchSample1 x711
                             then
                               x711.logSamplingDensity
                             else
                               let #var"275" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 209:45-209:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st442, x693)
                      in
                      match p_apply st442 x691 x693 with (st443, x694)
                      in
                      match
                        getRepertoireSamplingDensity st443 rep2 samplingProb
                      with
                        (st444, x695)
                      in
                      match
                        p_map
                          st444
                          (lam x696.
                             mulf
                               x696
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
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 209:113-209:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1))
                                     0.)))
                          x695
                      with
                        (st445, x697)
                      in
                      match p_apply st445 x694 x697 with (st446, x698)
                      in
                      let st447 =
                        p_weight
                          st446
                          simpleStoreWeight
                          (/-temp-/lam x707.
                             x707)
                          x698
                      in
                      let foo2 = {} in
                      match observationMessage1 st447 rep2 with (st448, newMsg)
                      in
                      match
                        mtxMul
                          st448
                          newMsg
                          (match tree2 with MsgNode x699
                           then
                             x699.leftKernel
                           else
                             let #var"277" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 213:33-213:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st449, x700)
                      in
                      match
                        sampleTreeHistory
                          st449
                          (match tree2 with MsgNode x6410
                           then
                             x6410.left
                           else
                             let #var"278" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 218:6-218:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          nHosts
                          x700
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 218:39-218:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6710
                           then
                             x6710.leftKernel
                           else
                             let #var"280" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 218:62-218:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st450, x702)
                      in
                      match
                        mtxMul
                          st450
                          newMsg
                          (match tree2 with MsgNode x6810
                           then
                             x6810.rightKernel
                           else
                             let #var"281" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 214:34-214:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st451, x703)
                      in
                      match
                        sampleTreeHistory
                          st451
                          (match tree2 with MsgNode x6010
                           then
                             x6010.right
                           else
                             let #var"282" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 221:6-221:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          nHosts
                          x703
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
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 221:41-221:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6310
                           then
                             x6310.rightKernel
                           else
                             let #var"284" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 221:64-221:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st452, x704)
                      in
                      match
                        p_map
                          st452
                          (lam x705.
                             match x705 with CorrectedBranchSample1 x5910
                             then
                               x5910.history
                             else
                               let #var"285" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 228:16-228:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st453, x706)
                      in
                      (st453, HistoryNode
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
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 225:12-225:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 226:14-226:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                              in
                              exit 1,
                          left = x702,
                          right = x704,
                          history = x706,
                          repertoire = rep2 })
  in
  let anon30 =
    lam n22.
      lam hostDistances2.
        lam x813.
          divf
            x813
            (divf
               (rec25 0. (paste0 hostDistances2))
               (int2float (muli n22 (subi n22 1))))
  in
  recursive
    let rec18 =
      lam c68.
        lam c69.
          lam s17.
            match s17 with [ _,
                _ ] ++ _
            then
              match splitAt s17 1 with {#label"1" = x709}
              in
              cons (anon30 c68 c69 (get s17 0)) (rec18 c68 c69 x709)
            else match s17 with [ e17 ]
            then
              match splitAt s17 1 with {#label"1" = x710}
              in
              let slice16 = x710 in
              [ anon30 c68 c69 e17 ]
            else match s17 with ""
            in
            ""
  in
  let anon31 =
    lam n21.
      lam hostDistances1.
        lam x812.
          rec18 n21 hostDistances1 x812
  in
  recursive
    let rec19 =
      lam c70.
        lam c71.
          lam s18.
            match s18 with [ _,
                _ ] ++ _
            then
              match splitAt s18 1 with {#label"1" = x712}
              in
              cons (anon31 c70 c71 (get s18 0)) (rec19 c70 c71 x712)
            else match s18 with [ e18 ]
            then
              match splitAt s18 1 with {#label"1" = x713}
              in
              let slice17 = x713 in
              [ anon31 c70 c71 e18 ]
            else match s18 with ""
            in
            ""
  in
  let input1 =
    { interactions =
        [ [ 2, 0 ],
          [ 2, 0 ],
          [ 2, 0 ],
          [ 2, 0 ],
          [ 2, 0 ],
          [ 2, 0 ],
          [ 2, 0 ],
          [ 2, 0 ],
          [ 2, 1 ],
          [ 2, 1 ],
          [ 2, 1 ],
          [ 2, 1 ],
          [ 2, 1 ],
          [ 2, 1 ],
          [ 2, 1 ],
          [ 2, 1 ],
          [ 2, 2 ],
          [ 2, 2 ],
          [ 2, 2 ],
          [ 2, 2 ],
          [ 2, 2 ],
          [ 2, 2 ],
          [ 2, 2 ],
          [ 2, 2 ],
          [ 1, 2 ],
          [ 1, 2 ],
          [ 1, 2 ],
          [ 1, 2 ],
          [ 1, 2 ],
          [ 1, 2 ],
          [ 1, 2 ],
          [ 1, 2 ] ],
      subrootLabel = (negi 1),
      symbiontTree =
        Node
          { age = 5.,
            label = 33,
            left =
              Node
                { age = 4.,
                  label = 34,
                  left =
                    Node
                      { age = 3.,
                        label = 35,
                        left =
                          Node
                            { age = 2.,
                              label = 36,
                              left =
                                Node
                                  { age = 0.,
                                    label = 37,
                                    left =
                                      Leaf
                                        { age = 0., label = 1 },
                                    right =
                                      Leaf
                                        { age = 0., label = 2 } },
                              right =
                                Node
                                  { age = 0.,
                                    label = 38,
                                    left =
                                      Leaf
                                        { age = 0., label = 3 },
                                    right =
                                      Leaf
                                        { age = 0., label = 4 } } },
                        right =
                          Node
                            { age = 2.,
                              label = 39,
                              left =
                                Node
                                  { age = 0.,
                                    label = 40,
                                    left =
                                      Leaf
                                        { age = 0., label = 5 },
                                    right =
                                      Leaf
                                        { age = 0., label = 6 } },
                              right =
                                Node
                                  { age = 0.,
                                    label = 41,
                                    left =
                                      Leaf
                                        { age = 0., label = 7 },
                                    right =
                                      Leaf
                                        { age = 0., label = 8 } } } },
                  right =
                    Node
                      { age = 3.,
                        label = 42,
                        left =
                          Node
                            { age = 2.,
                              label = 43,
                              left =
                                Node
                                  { age = 0.,
                                    label = 44,
                                    left =
                                      Leaf
                                        { age = 0., label = 9 },
                                    right =
                                      Leaf
                                        { age = 0., label = 10 } },
                              right =
                                Node
                                  { age = 0.,
                                    label = 45,
                                    left =
                                      Leaf
                                        { age = 0., label = 11 },
                                    right =
                                      Leaf
                                        { age = 0., label = 12 } } },
                        right =
                          Node
                            { age = 2.,
                              label = 46,
                              left =
                                Node
                                  { age = 0.,
                                    label = 47,
                                    left =
                                      Leaf
                                        { age = 0., label = 13 },
                                    right =
                                      Leaf
                                        { age = 0., label = 14 } },
                              right =
                                Node
                                  { age = 0.,
                                    label = 48,
                                    left =
                                      Leaf
                                        { age = 0., label = 15 },
                                    right =
                                      Leaf
                                        { age = 0., label = 16 } } } } },
            right =
              Node
                { age = 4.,
                  label = 49,
                  left =
                    Node
                      { age = 3.,
                        label = 50,
                        left =
                          Node
                            { age = 2.,
                              label = 51,
                              left =
                                Node
                                  { age = 0.,
                                    label = 52,
                                    left =
                                      Leaf
                                        { age = 0., label = 17 },
                                    right =
                                      Leaf
                                        { age = 0., label = 18 } },
                              right =
                                Node
                                  { age = 0.,
                                    label = 53,
                                    left =
                                      Leaf
                                        { age = 0., label = 19 },
                                    right =
                                      Leaf
                                        { age = 0., label = 20 } } },
                        right =
                          Node
                            { age = 2.,
                              label = 54,
                              left =
                                Node
                                  { age = 0.,
                                    label = 55,
                                    left =
                                      Leaf
                                        { age = 0., label = 21 },
                                    right =
                                      Leaf
                                        { age = 0., label = 22 } },
                              right =
                                Node
                                  { age = 0.,
                                    label = 56,
                                    left =
                                      Leaf
                                        { age = 0., label = 23 },
                                    right =
                                      Leaf
                                        { age = 0., label = 24 } } } },
                  right =
                    Node
                      { age = 3.,
                        label = 57,
                        left =
                          Node
                            { age = 2.,
                              label = 58,
                              left =
                                Node
                                  { age = 0.,
                                    label = 59,
                                    left =
                                      Leaf
                                        { age = 0., label = 25 },
                                    right =
                                      Leaf
                                        { age = 0., label = 26 } },
                              right =
                                Node
                                  { age = 0.,
                                    label = 60,
                                    left =
                                      Leaf
                                        { age = 0., label = 27 },
                                    right =
                                      Leaf
                                        { age = 0., label = 28 } } },
                        right =
                          Node
                            { age = 2.,
                              label = 61,
                              left =
                                Node
                                  { age = 0.,
                                    label = 62,
                                    left =
                                      Leaf
                                        { age = 0., label = 29 },
                                    right =
                                      Leaf
                                        { age = 0., label = 30 } },
                              right =
                                Node
                                  { age = 0.,
                                    label = 63,
                                    left =
                                      Leaf
                                        { age = 0., label = 31 },
                                    right =
                                      Leaf
                                        { age = 0., label = 32 } } } } } },
      hostDistances = [ [ 0., 2. ],
          [ 2., 0. ] ],
      subrootLength = 5. }
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
      st simpleStoreAssume (p_pure (mkDirichlet [ 1., 1., 1., 1. ]))
  with
    (st454, lambda)
  in
  match
    p_assume st454 simpleStoreAssume (p_pure (mkExponential 10.))
  with
    (st455, mu)
  in
  match
    p_assume st455 simpleStoreAssume (p_pure (mkExponential 1.))
  with
    (st456, beta)
  in
  match
    p_map
      st456
      (lam x714.
         subf 0. (get x714 (subi 1 1)))
      lambda
  with
    (st457, x715)
  in
  match
    p_map st457 (lam x716.
         get x716 (subi 1 1)) lambda
  with
    (st458, x717)
  in
  match
    p_map st458 (lam x718.
         get x718 (subi 2 1)) lambda
  with
    (st459, x719)
  in
  match
    p_map
      st459
      (lam x720.
         lam x721.
           subf 0. (addf (get x720 (subi 2 1)) x721))
      lambda
  with
    (st460, x722)
  in
  match
    p_map st460 (lam x723.
         get x723 (subi 3 1)) lambda
  with
    (st461, x724)
  in
  match p_apply st461 x722 x724 with (st462, x725)
  in
  match
    p_map st462 (lam x726.
         get x726 (subi 3 1)) lambda
  with
    (st463, x727)
  in
  match
    p_map st463 (lam x728.
         get x728 (subi 4 1)) lambda
  with
    (st464, x729)
  in
  match
    p_map
      st464
      (lam x730.
         subf 0. (get x730 (subi 4 1)))
      lambda
  with
    (st465, x731)
  in
  match
    p_traverseSeq
      st465
      (lam st466.
         lam x732.
           (st466, x732))
      [ x715,
        x717,
        p_pure 0.,
        x719,
        x725,
        x727,
        p_pure 0.,
        x729,
        x731 ]
  with
    (st467, x733)
  in
  match
    p_map
      st467
      (lam x734.
         tmOpaque (let len = length x734 in
          let a71 = externalExtArrMakeUninit extArrKindFloat64 len in
          recursive
            let work3 =
              lam i22.
                match eqi i22 len with true
                then
                  {}
                else
                  let #var"2110" = externalExtArrSet a71 i22 (get x734 i22) in
                  work3 (addi i22 1)
          in
          let #var"2210" = work3 0 in
          a71))
      x733
  with
    (st468, x735)
  in
  match matFromArrExn st468 3 3 x735 with (st469, mtx5)
  in
  match p_map st469 (lam x736.
         x736.m) mtx5 with (st470, m2)
  in
  match p_map st470 (lam x737.
         x737.n) mtx5 with (st471, n4)
  in
  match
    p_map
      st471
      (lam x738.
         lam x739.
           lam x740.
             lam x741.
               lam x742.
                 tmOpaque (let b14 = matMakeUninit (externalExtArrKind x742.arr) x738 x739
                  in
                  let #var"14" = externalCblasCopy x740 x742.arr 1 b14.arr 1 in
                  let #var"15" = externalCblasScal x740 x741 b14.arr 1 in
                  b14))
      m2
  with
    (st472, x743)
  in
  match p_apply st472 x743 n4 with (st473, x744)
  in
  match
    p_map
      st473
      (lam x745.
         lam x746.
           muli x745 x746)
      m2
  with
    (st474, x747)
  in
  match p_apply st474 x747 n4 with (st475, x748)
  in
  match p_apply st475 x744 x748 with (st476, x749)
  in
  match p_apply st476 x749 mu with (st477, x750)
  in
  match p_apply st477 x750 mtx5 with (st478, qMatrix2)
  in
  let ns = rec19 (length11 hostDistances) hostDistances hostDistances
  in
  match mtxGet st478 2 2 qMatrix2 with (st479, x751)
  in
  match p_map st479 (lam x752.
         negf x752) x751 with (st480, q2)
  in
  match mtxGet st480 1 1 qMatrix2 with (st481, x753)
  in
  match p_map st481 (lam x754.
         negf x754) x753 with (st482, x755)
  in
  match mtxGet st482 3 3 qMatrix2 with (st483, x756)
  in
  match p_map st483 (lam x757.
         negf x757) x756 with (st484, x758)
  in
  match mtxGet st484 2 1 qMatrix2 with (st485, x759)
  in
  match
    p_map
      st485
      (lam x760.
         lam x761.
           divf x760 x761)
      x759
  with
    (st486, x762)
  in
  match p_apply st486 x762 q2 with (st487, x763)
  in
  match mtxGet st487 2 3 qMatrix2 with (st488, x764)
  in
  match
    p_map
      st488
      (lam x765.
         lam x766.
           divf x765 x766)
      x764
  with
    (st489, x767)
  in
  match p_apply st489 x767 q2 with (st490, x768)
  in
  let modelParams2 =
    ModelParams1
      { beta = beta,
        hostMetric =
          mtxCreate (length11 ns) (length1 (get ns (subi 1 1))) (paste0 ns),
        embeddedQMatrix =
          EmbeddedMarkovChainMatrix1
            { totalRates =
                [ x755,
                  q2,
                  x758 ],
              transitionProbs =
                [ [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ],
                  [ x763,
                    p_pure 0.,
                    x768 ],
                  [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ] ],
              mat = qMatrix2 } }
  in
  match input1 with {interactions = #var"X12"}
  in
  match
    postorderTraverse st490 symbiontTree qMatrix2 #var"X12" nHosts1
  with
    (st491, postorderTree)
  in
  match input1 with {subrootLabel = #var"X13"}
  in
  let subrootLabel1 = #var"X13" in
  match mtxSclrMul st491 subrootLength qMatrix2 with (st492, x769)
  in
  match mtxExpRateSafe st492 x769 with (st493, subrootKernel)
  in
  match mtxTrans st493 subrootKernel with (st494, x770)
  in
  match
    mtxMul
      st494
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
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 83:32-83:52>:\nField \'outMsg\' not found\n[0m  let subrootInfo = subrootNode([31mpostorderTree.outMsg[0m[0m, subrootLength, subrootLabel, qMatrix, nHosts);\n"
         in
         p_pure (exit 1))
      x770
  with
    (st495, a32)
  in
  let b4 = mtxCreate nHosts1 3 (rep (muli 3 nHosts1) 1.) in
  match
    p_map
      st495
      (lam x771.
         match x771 with {m = #var"X15"}
         in
         match b4 with {m = #var"X16"}
         in
         eqi #var"X15" #var"X16")
      a32
  with
    (st496, x772)
  in
  match
    p_map
      st496
      (lam x773.
         match x773 with {n = #var"X17"}
         in
         match b4 with {n = #var"X18"}
         in
         eqi #var"X17" #var"X18")
      a32
  with
    (st497, x774)
  in
  match and1 st497 x772 x774 with (st498, x775)
  in
  match
    p_bind
      st498
      simpleStoreSubmodel
      (simpleInit {})
      (lam st499.
         lam x776.
           match
             match x776 with true
             then
               match
                 p_map
                   st499
                   (lam x777.
                      tmOpaque (let c210 = matMakeUninit (externalExtArrKind x777.arr) x777.m x777.n
                       in
                       let #var"16" = matElemMulNoAlloc x777 b4 c210 in
                       c210))
                   a32
               with
                 (st500, x778)
               in
               (st500, Right
                 x778)
             else
               (st499, Left
                 (DimensionMismatch
                    {}))
           with
             (st501, n3)
           in
           match n3 with Right x779
           then
             p_map
               st501
               (lam x780.
                  Right
                    x780)
               x779
           else match n3 with Left x781
           in
           (st501, p_pure (Left
                x781)))
      x775
  with
    (st502, x782)
  in
  match eitherEither st502 x782 with (st503, subrootSamplingProb)
  in
  match
    suggestNodeRep st503 subrootSamplingProb nHosts1 subrootLabel1
  with
    (st504, subrootRep)
  in
  match any1 st504 subrootRep with (st505, x783)
  in
  match bool2real st505 x783 with (st506, x784)
  in
  let st507 =
    p_weight
      st506
      simpleStoreWeight
      (lam x811.
         externalLog (addf x811 (mulf (int2float subrootLabel1) 0.)))
      x784
  in
  let foo6 = {} in
  match
    getRepertoireSamplingDensity st507 subrootRep subrootSamplingProb
  with
    (st508, x785)
  in
  let st509 =
    p_weight
      st508
      simpleStoreWeight
      (lam x810.
         addf
           (subf
              (negf
                 (log1
                    (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1)))))
              x810)
           (mulf (int2float subrootLabel1) 0.))
      x785
  in
  let foo7 = {} in
  match observationMessage1 st509 subrootRep with (st510, x786)
  in
  match mtxMul st510 x786 subrootKernel with (st511, x787)
  in
  let subrootInfo =
    SubrootInfo1
      { kernel = subrootKernel, rep = subrootRep, msg = x787 }
  in
  match
    mtxElemMul
      st511
      (match subrootInfo with SubrootInfo1 x1111
       then
         x1111.msg
       else
         let #var"290" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 85:36-85:51>:\nField \'msg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31msubrootInfo.msg[0m[0m, postorderTree.outMsg);\n"
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
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 85:53-85:73>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul(subrootInfo.msg, [31mpostorderTree.outMsg[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st512, rootSamplingProb)
  in
  match
    suggestNodeRep
      st512
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
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 86:57-86:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
         in
         exit 1)
  with
    (st513, rootRep)
  in
  match any1 st513 rootRep with (st514, x788)
  in
  match bool2real st514 x788 with (st515, x789)
  in
  let st516 =
    p_weight
      st515
      simpleStoreWeight
      (lam x809.
         externalLog
           (addf
              x809
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried70
                     then
                       carried70.label
                     else match postorderTree with MsgNode carried71
                     then
                       carried71.label
                     else
                       let #var"2111" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 87:45-87:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1))
                 0.)))
      x789
  in
  let foo3 = {} in
  let rootAge =
    match postorderTree with MsgLeaf carried68
    then
      carried68.age
    else match postorderTree with MsgNode carried69
    then
      carried69.age
    else
      let #var"2109" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 90:16-90:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    sampleBranch
      st516
      (match subrootInfo with SubrootInfo1 x1011
       then
         x1011.rep
       else
         let #var"293" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 92:4-92:19>:\nField \'rep\' not found\n[0m    [31msubrootInfo.rep[0m[0m,\n"
         in
         map (lam x790.
              p_pure x790) (exit 1))
      rootRep
      (addf rootAge subrootLength)
      rootAge
      nHosts1
      (match postorderTree with MsgLeaf carried58
       then
         carried58.label
       else match postorderTree with MsgNode carried59
       then
         carried59.label
       else
         let #var"294" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 97:4-97:23>:\nField \'label\' not found\n[0m    [31mpostorderTree.label[0m[0m,\n"
         in
         exit 1)
      modelParams2
      (match subrootInfo with SubrootInfo1 x1041
       then
         x1041.kernel
       else
         let #var"295" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 99:4-99:22>:\nField \'kernel\' not found\n[0m    [31msubrootInfo.kernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st517, subrootBranchSample)
  in
  match
    p_map
      st517
      (lam x791.
         lam x792.
           lam x793.
             subf
               (subf
                  (match x791 with CorrectedBranchSample1 x971
                   then
                     x971.logModelDensity
                   else
                     let #var"296" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 107:4-107:39>:\nField \'logModelDensity\' not found\n[0m    [31msubrootBranchSample.logModelDensity[0m\n"
                     in
                     exit 1)
                  x792)
               x793)
      subrootBranchSample
  with
    (st518, x794)
  in
  match
    p_map
      st518
      (lam x795.
         match x795 with CorrectedBranchSample1 x981
         then
           x981.logSamplingDensity
         else
           let #var"297" =
             print
               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 108:6-108:44>:\nField \'logSamplingDensity\' not found\n[0m    - [31msubrootBranchSample.logSamplingDensity[0m\n"
           in
           exit 1)
      subrootBranchSample
  with
    (st519, x796)
  in
  match p_apply st519 x794 x796 with (st520, x797)
  in
  match
    getRepertoireSamplingDensity st520 rootRep rootSamplingProb
  with
    (st521, x798)
  in
  match
    p_map
      st521
      (lam x799.
         mulf
           x799
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
                       let #var"298" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 109:40-109:59>:\nField \'label\' not found\n[0m    - rootLogSamplingDensity * exp(Real([31mpostorderTree.label[0m[0m) * 0.)\n"
                       in
                       exit 1))
                 0.)))
      x798
  with
    (st522, x800)
  in
  match p_apply st522 x797 x800 with (st523, x801)
  in
  let st524 =
    p_weight
      st523 simpleStoreWeight (/-temp-/lam x808.
         x808) x801
  in
  let foo4 = {} in
  match observationMessage1 st524 rootRep with (st525, newMsg1)
  in
  let rootAge1 =
    match postorderTree with MsgLeaf carried66
    then
      carried66.age
    else match postorderTree with MsgNode carried67
    then
      carried67.age
    else
      let #var"2108" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 117:16-117:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    mtxMul
      st525
      newMsg1
      (match postorderTree with MsgNode x961
       then
         x961.leftKernel
       else
         let #var"299" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 114:31-114:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st526, x802)
  in
  match
    sampleTreeHistory
      st526
      (match postorderTree with MsgNode x911
       then
         x911.left
       else
         let #var"2100" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 119:4-119:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
         in
         exit 1)
      nHosts1
      x802
      rootRep
      rootAge1
      modelParams2
      (match postorderTree with MsgNode x921
       then
         x921.leftKernel
       else
         let #var"2101" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 119:72-119:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st527, x803)
  in
  match
    mtxMul
      st527
      newMsg1
      (match postorderTree with MsgNode x951
       then
         x951.rightKernel
       else
         let #var"2102" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 115:32-115:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st528, x804)
  in
  match
    sampleTreeHistory
      st528
      (match postorderTree with MsgNode x891
       then
         x891.right
       else
         let #var"2103" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 123:4-123:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
         in
         exit 1)
      nHosts1
      x804
      rootRep
      rootAge1
      modelParams2
      (match postorderTree with MsgNode x901
       then
         x901.rightKernel
       else
         let #var"2104" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 123:74-123:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st529, x805)
  in
  match
    p_map
      st529
      (lam x806.
         match x806 with CorrectedBranchSample1 x881
         then
           x881.history
         else
           let #var"2105" =
             print
               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 130:36-130:63>:\nField \'history\' not found\n[0m    repertoire = rootRep, history = [31msubrootBranchSample.history[0m\n"
           in
           exit 1)
      subrootBranchSample
  with
    (st530, x807)
  in
  p_export
    st530
    simpleStoreExport
    (p_pure
       (dprint
          (ReturnType1
             { mu = mu,
               beta = beta,
               tree =
                 HistoryNode
                   { age =
                       match symbiontTree with Leaf carried62
                       then
                         carried62.age
                       else match symbiontTree with Node carried63
                       then
                         carried63.age
                       else
                         let #var"2106" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 128:10-128:26>:\nField \'age\' not found\n[0m    age = [31msymbiontTree.age[0m[0m, label = symbiontTree.label,\n"
                         in
                         exit 1,
                     label =
                       match symbiontTree with Leaf carried64
                       then
                         carried64.label
                       else match symbiontTree with Node carried65
                       then
                         carried65.label
                       else
                         let #var"2107" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 128:36-128:54>:\nField \'label\' not found\n[0m    age = symbiontTree.age, label = [31msymbiontTree.label[0m[0m,\n"
                         in
                         exit 1,
                     left = x803,
                     right = x805,
                     history = x807,
                     repertoire = rootRep },
               lambda = lambda })))
