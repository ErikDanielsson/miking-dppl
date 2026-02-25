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
    lam a881.
      lam b301.
        match a881 with true
        then
          b301
        else
          false
  in
  let and1 =
    lam st907.
      lam a88.
        lam b30.
          p_select
            st907
            (lam x1448.
               match x1448 with true
               then
                 b30
               else
                 p_pure false)
            a88
  in
  let pow = lam x1733.
      lam y2.
        externalPow x1733 y2
  in
  let pow1 =
    lam st906.
      lam x1732.
        lam y1.
          p_map
            st906 (lam x1447.
               externalPow x1732 x1447) y1
  in
  let pow2 =
    lam st904.
      lam x1731.
        lam y.
          match
            p_map
              st904
              (lam x1440.
                 lam x1445.
                   externalPow x1440 x1445)
              x1731
          with
            (st905, x1446)
          in
          p_apply st905 x1446 y
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
  let digit2char = lam d.
      int2char (addi d (char2int '0'))
  in
  recursive
    let int2string_rechelper =
      lam n.
        lam acc31.
          match lti n 10 with true
          then
            cons (digit2char n) acc31
          else
            int2string_rechelper (divi n 10) (cons (digit2char (modi n 10)) acc31)
    let int2string_rechelper1 =
      lam n1.
        lam acc32.
          match lti n1 10 with true
          then
            cons (digit2char n1) acc32
          else
            int2string_rechelper (divi n1 10) (cons (digit2char (modi n1 10)) acc32)
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
        lam n61.
          { arr = externalExtArrMakeUninit kind1 (muli m41 n61),
            n = n61,
            m = m41 }
  in
  let matMakeUninit1 =
    lam st902.
      lam kind.
        lam m4.
          lam n6.
            match
              p_map
                st902
                (lam x1438.
                   externalExtArrMakeUninit kind (muli m4 x1438))
                n6
            with
              (st903, x1439)
            in
            (st903, { arr = x1439, n = n6, m = m4 })
  in
  let matGetExn =
    lam a67.
      lam i161.
        lam j1.
          match a67 with {arr = #var"X65"}
          in
          match a67 with {n = #var"X66"}
          in
          externalExtArrGet #var"X65" (addi (muli i161 #var"X66") j1)
  in
  let matHasSameShape2 =
    lam a61.
      lam b21.
        match a61 with {m = #var"X61"}
        in
        match b21 with {m = #var"X62"}
        in
        match a61 with {n = #var"X63"}
        in
        match b21 with {n = #var"X64"}
        in
        and (eqi #var"X61" #var"X62") (eqi #var"X63" #var"X64")
  in
  let matTranposeNoAlloc =
    lam a58.
      lam b19.
        match a58 with {m = #var"X53"}
        in
        match b19 with {n = #var"X54"}
        in
        match a58 with {n = #var"X55"}
        in
        match b19 with {m = #var"X56"}
        in
        match and (eqi #var"X53" #var"X54") (eqi #var"X55" #var"X56") with true
        then
          match a58 with {m = #var"X57"}
          in
          match a58 with {n = #var"X58"}
          in
          match a58 with {arr = #var"X59"}
          in
          match b19 with {arr = #var"X60"}
          in
          let #var"1810" = externalMatTranspose #var"X57" #var"X58" #var"X59" #var"X60"
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
            match a57 with {m = #var"X48"}
            in
            match a57 with {n = #var"X49"}
            in
            match a57 with {arr = #var"X50"}
            in
            match b18 with {arr = #var"X51"}
            in
            match c410 with {arr = #var"X52"}
            in
            let #var"1710" =
              externalMatElemMul #var"X48" #var"X49" #var"X50" #var"X51" #var"X52"
            in
            Right
              {}
          else
            Left
              (DimensionMismatch
                 {})
  in
  let exp1 = lam x1611.
      externalExp x1611 in
  let log1 = lam x1602.
      externalLog x1602 in
  let log11 =
    lam st901.
      lam x1601.
        p_map st901 (lam x1437.
             externalLog x1437) x1601
  in
  let cons1 = lam e112.
      lam s83.
        cons e112 s83 in
  let cons11 =
    lam st897.
      lam e111.
        lam s82.
          match e111 with Event1 x1419
          in
          match x1419 with {toState = x1420}
          in
          match
            p_map
              st897
              (lam x1425.
                 lam x1426.
                   match x1419 with {host = x1427}
                   in
                   match x1419 with {eventTime = x1428}
                   in
                   Event1
                     { host = x1427,
                       toState = x1425,
                       eventTime = x1428,
                       fromState = x1426 })
              x1420
          with
            (st898, x1429)
          in
          match x1419 with {fromState = x1430}
          in
          match p_apply st898 x1429 x1430 with (st899, x1435)
          in
          match p_map st899 cons x1435 with (st900, x1436)
          in
          p_apply st900 x1436 s82
  in
  let cons12 = lam e110.
      lam s81.
        cons e110 s81 in
  let paste0 =
    lam st891.
      lam l52.
        match l52 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st891
              (lam st892.
                 lam x1409.
                   (st892, x1409))
              ""
          with
            (st893, x1410)
          in
          match p_map st893 concat x1410 with (st894, x1415)
          in
          match p_apply st894 x1415 (get l52 0) with (st895, x1416)
          in
          match splitAt l52 1 with {#label"1" = x1417}
          in
          rec22 st895 x1416 x1417
        else match l52 with ""
        in
        p_traverseSeq
          st891
          (lam st896.
             lam x1418.
               (st896, x1418))
          ""
  in
  let paste01 =
    lam st885.
      lam l51.
        match l51 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st885
              (lam st886.
                 lam x1399.
                   (st886, x1399))
              ""
          with
            (st887, x1400)
          in
          match p_map st887 concat x1400 with (st888, x1405)
          in
          match p_apply st888 x1405 (get l51 0) with (st889, x1406)
          in
          match splitAt l51 1 with {#label"1" = x1407}
          in
          rec23 st889 x1406 x1407
        else match l51 with ""
        in
        p_traverseSeq
          st885
          (lam st890.
             lam x1408.
               (st890, x1408))
          ""
  in
  let paste02 =
    lam st879.
      lam l5.
        match l5 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st879
              (lam st880.
                 lam x1389.
                   (st880, x1389))
              ""
          with
            (st881, x1390)
          in
          match p_map st881 concat x1390 with (st882, x1395)
          in
          match p_apply st882 x1395 (get l5 0) with (st883, x1396)
          in
          match splitAt l5 1 with {#label"1" = x1397}
          in
          rec24 st883 x1396 x1397
        else match l5 with ""
        in
        p_traverseSeq
          st879
          (lam st884.
             lam x1398.
               (st884, x1398))
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
  let length13 = lam st878.
      lam l31.
        p_map st878 length l31
  in
  let anon =
    lam x1386.
      lam x1387.
        lam x1388.
          match x1388 with true
          then
            snoc x1386 (addi x1387 1)
          else
            x1386
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
      lam st10.
        lam acc22.
          lam i21.
            lam s31.
              match s31 with [ e1 ] ++ rest1
              then
                match
                  p_bind
                    st10
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st11.
                       lam x11.
                         match x11 with true
                         then
                           p_map
                             st11
                             (lam x12.
                                snoc x12 (addi i21 1))
                             acc22
                         else
                           (st11, acc22))
                    e1
                with
                  (st12, x13)
                in
                work1 st12 x13 (addi i21 1) rest1
              else
                (st10, acc22)
  in
  let whichTrue =
    lam s63.
      match s63 with [ e19 ] ++ rest4
      then
        work (anon "" 0 e19) (addi 0 1) rest4
      else
        ""
  in
  let whichTrue1 =
    lam st875.
      lam s62.
        match s62 with [ e18 ] ++ rest3
        then
          match
            p_map
              st875
              (lam x1383.
                 match x1383 with true
                 then
                   snoc "" (addi 0 1)
                 else
                   "")
              e18
          with
            (st876, x1384)
          in
          work1 st876 x1384 (addi 0 1) rest3
        else
          p_traverseSeq
            st875
            (lam st877.
               lam x1385.
                 (st877, x1385))
            ""
  in
  let whichTrue2 =
    lam st874.
      lam s61.
        p_map
          st874
          (lam x1382.
             match x1382 with [ e17 ] ++ rest2
             then
               work (anon "" 0 e17) (addi 0 1) rest2
             else
               "")
          s61
  in
  let int2string1 =
    lam st873.
      lam v1.
        p_map
          st873
          (lam x1381.
             match lti x1381 0 with true
             then
               cons '-' (int2string_rechelper1 (negi x1381) "")
             else
               int2string_rechelper1 x1381 "")
          v1
  in
  let bool2real =
    lam st872.
      lam v.
        p_map
          st872
          (lam x1380.
             match x1380 with true
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
          match
            eqi
              (muli rows1 cols12)
              (externalExtArrLength
                 (tmOpaque (let len1 = length data1 in
                   let a701 = externalExtArrMakeUninit extArrKindFloat64 len1 in
                   recursive
                     let work31 =
                       lam i172.
                         match eqi i172 len1 with true
                         then
                           {}
                         else
                           let #var"1911" = externalExtArrSet a701 i172 (get data1 i172)
                           in
                           work31 (addi i172 1)
                   in
                   let #var"201" = work31 0 in
                   a701)))
          with
            true
          then
            { arr =
                tmOpaque (let len1 = length data1 in
                 let a701 = externalExtArrMakeUninit extArrKindFloat64 len1 in
                 recursive
                   let work31 =
                     lam i172.
                       match eqi i172 len1 with true
                       then
                         {}
                       else
                         let #var"1911" = externalExtArrSet a701 i172 (get data1 i172)
                         in
                         work31 (addi i172 1)
                 in
                 let #var"201" = work31 0 in
                 a701),
              n = cols12,
              m = rows1 }
          else
            error "matFromArrExn: dimensions mismatch"
  in
  let mtxCreate1 =
    lam st868.
      lam rows.
        lam cols11.
          lam data.
            match
              p_traverseSeq
                st868
                (lam st869.
                   lam x1375.
                     (st869, x1375))
                data
            with
              (st870, x1376)
            in
            match
              p_map
                st870
                (lam x1377.
                   tmOpaque (let len = length x1377 in
                    let a70 = externalExtArrMakeUninit extArrKindFloat64 len in
                    recursive
                      let work3 =
                        lam i171.
                          match eqi i171 len with true
                          then
                            {}
                          else
                            let #var"1910" = externalExtArrSet a70 i171 (get x1377 i171) in
                            work3 (addi i171 1)
                    in
                    let #var"20" = work3 0 in
                    a70))
                x1376
            with
              (st871, x1378)
            in
            p_map
              st871
              (lam x1379.
                 match eqi (muli rows cols11) (externalExtArrLength x1379) with true
                 then
                   { arr = x1379, n = cols11, m = rows }
                 else
                   error "matFromArrExn: dimensions mismatch")
              x1378
  in
  let mtxGet =
    lam st865.
      lam row13.
        lam col2.
          lam mtx62.
            match
              p_map
                st865
                (lam x1366.
                   lam x1367.
                     match x1366 with {arr = #var"X46"}
                     in
                     externalExtArrGet #var"X46" x1367)
                mtx62
            with
              (st866, x1368)
            in
            match
              p_map
                st866
                (lam x1369.
                   match x1369 with {n = #var"X47"}
                   in
                   addi (muli (subi row13 1) #var"X47") (subi col2 1))
                mtx62
            with
              (st867, x1370)
            in
            p_apply st867 x1368 x1370
  in
  let mtxGet1 =
    lam st859.
      lam row12.
        lam col1.
          lam mtx61.
            match
              p_map
                st859
                (lam x1351.
                   lam x1352.
                     match x1351 with {arr = #var"X45"}
                     in
                     externalExtArrGet #var"X45" x1352)
                mtx61
            with
              (st860, x1353)
            in
            match
              p_map st860 (lam x1354.
                   subi x1354 1) row12
            with
              (st861, x1355)
            in
            match
              p_map
                st861
                (lam x1356.
                   lam x1357.
                     addi (muli x1356 x1357) (subi col1 1))
                x1355
            with
              (st862, x1358)
            in
            match
              p_map st862 (lam x1359.
                   x1359.n) mtx61
            with
              (st863, x1360)
            in
            match p_apply st863 x1358 x1360 with (st864, x1365)
            in
            p_apply st864 x1353 x1365
  in
  let mtxGet2 =
    lam st851.
      lam row11.
        lam col.
          lam mtx6.
            match
              p_map
                st851
                (lam x1328.
                   lam x1329.
                     match x1328 with {arr = #var"X44"}
                     in
                     externalExtArrGet #var"X44" x1329)
                mtx6
            with
              (st852, x1330)
            in
            match
              p_map st852 (lam x1335.
                   subi x1335 1) row11
            with
              (st853, x1336)
            in
            match
              p_map
                st853
                (lam x1337.
                   lam x1338.
                     lam x1339.
                       addi (muli x1337 x1338) x1339)
                x1336
            with
              (st854, x1340)
            in
            match
              p_map st854 (lam x1345.
                   x1345.n) mtx6
            with
              (st855, x1346)
            in
            match p_apply st855 x1340 x1346 with (st856, x1347)
            in
            match
              p_map st856 (lam x1348.
                   subi x1348 1) col
            with
              (st857, x1349)
            in
            match p_apply st857 x1347 x1349 with (st858, x1350)
            in
            p_apply st858 x1330 x1350
  in
  let anon1 =
    lam new5.
      lam mtx55.
        lam row5.
          lam x1326.
            lam x1327.
              match new5 with {arr = #var"X42"}
              in
              match new5 with {n = #var"X43"}
              in
              externalExtArrSet
                #var"X42"
                (addi (muli 0 #var"X43") x1326)
                (matGetExn mtx55 (subi row5 1) (subi x1327 1))
  in
  let anon2 =
    lam st848.
      lam new4.
        lam mtx54.
          lam row4.
            lam x1315.
              lam x1316.
                match new4 with {arr = #var"X40"}
                in
                match
                  p_map
                    st848
                    (lam x1317.
                       lam x1318.
                         externalExtArrSet x1317 x1318 (matGetExn mtx54 (subi row4 1) (subi x1316 1)))
                    #var"X40"
                with
                  (st849, x1319)
                in
                match new4 with {n = #var"X41"}
                in
                match
                  p_map
                    st849
                    (lam x1320.
                       addi (muli 0 x1320) x1315)
                    #var"X41"
                with
                  (st850, x1325)
                in
                p_apply st850 x1319 x1325
  in
  let anon3 =
    lam st842.
      lam new3.
        lam mtx53.
          lam row3.
            lam x1294.
              lam x1295.
                match new3 with {arr = #var"X36"}
                in
                match
                  p_map
                    st842
                    (lam x1296.
                       lam x1297.
                         lam x1298.
                           externalExtArrSet x1296 x1297 x1298)
                    #var"X36"
                with
                  (st843, x1299)
                in
                match new3 with {n = #var"X37"}
                in
                match
                  p_map
                    st843
                    (lam x1300.
                       addi (muli 0 x1300) x1294)
                    #var"X37"
                with
                  (st844, x1305)
                in
                match p_apply st844 x1299 x1305 with (st845, x1306)
                in
                match
                  p_map st845 (lam x1307.
                       subi x1307 1) row3
                with
                  (st846, x1308)
                in
                match
                  p_map
                    st846
                    (lam x1309.
                       match mtx53 with {arr = #var"X38"}
                       in
                       match mtx53 with {n = #var"X39"}
                       in
                       externalExtArrGet #var"X38" (addi (muli x1309 #var"X39") (subi x1295 1)))
                    x1308
                with
                  (st847, x1310)
                in
                p_apply st847 x1306 x1310
  in
  recursive
    let rec1 =
      lam c.
        lam c1.
          lam c2.
            lam i.
              lam s1.
                match s1 with [ _,
                    _ ] ++ _
                then
                  match splitAt s1 1 with {#label"1" = x14}
                  in
                  cons (anon1 c c1 c2 i (get s1 0)) (rec1 c c1 c2 (addi i 1) x14)
                else match s1 with [ e2 ]
                then
                  match splitAt s1 1 with {#label"1" = x15}
                  in
                  let slice1 = x15 in
                  [ anon1 c c1 c2 i e2 ]
                else match s1 with ""
                in
                ""
    let rec11 =
      lam st13.
        lam c3.
          lam c4.
            lam c5.
              lam i1.
                lam s11.
                  match s11 with [ _,
                      _ ] ++ _
                  then
                    match anon2 st13 c3 c4 c5 i1 (get s11 0) with (st14, x16)
                    in
                    match splitAt s11 1 with {#label"1" = x17}
                    in
                    match rec11 st14 c3 c4 c5 (addi i1 1) x17 with (st15, x18)
                    in
                    (st15, cons x16 x18)
                  else match s11 with [ e3 ]
                  then
                    match splitAt s11 1 with {#label"1" = x19}
                    in
                    let slice2 = x19 in
                    match anon2 st13 c3 c4 c5 i1 e3 with (st16, x20)
                    in
                    (st16, [ x20 ])
                  else match s11 with ""
                  in
                  (st13, "")
    let rec12 =
      lam st17.
        lam c6.
          lam c7.
            lam c8.
              lam i3.
                lam s12.
                  match s12 with [ _,
                      _ ] ++ _
                  then
                    match anon3 st17 c6 c7 c8 i3 (get s12 0) with (st18, x21)
                    in
                    match splitAt s12 1 with {#label"1" = x22}
                    in
                    match rec12 st18 c6 c7 c8 (addi i3 1) x22 with (st19, x23)
                    in
                    (st19, cons x21 x23)
                  else match s12 with [ e4 ]
                  then
                    match splitAt s12 1 with {#label"1" = x24}
                    in
                    let slice3 = x24 in
                    match anon3 st17 c6 c7 c8 i3 e4 with (st20, x25)
                    in
                    (st20, [ x25 ])
                  else match s12 with ""
                  in
                  (st17, "")
  in
  let mtxRowCols =
    lam mtx52.
      lam row2.
        lam cols2.
          match mtx52 with {arr = #var"X35"}
          in
          let new2 =
            matMakeUninit (externalExtArrKind #var"X35") 1 (length cols2)
          in
          let #var"232" = rec1 new2 mtx52 row2 0 cols2 in
          let #var"1172" = {} in
          new2
  in
  let mtxRowCols1 =
    lam st832.
      lam mtx51.
        lam row1.
          lam cols1.
            match mtx51 with {arr = #var"X34"}
            in
            match p_map st832 length cols1 with (st833, x1285)
            in
            match
              matMakeUninit1 st833 (externalExtArrKind #var"X34") 1 x1285
            with
              (st834, new1)
            in
            match
              p_bind
                st834
                simpleStoreSubmodel
                (simpleInit {})
                (lam st835.
                   lam x1286.
                     match
                       match x1286 with [ _,
                           _ ] ++ _
                       then
                         match anon2 st835 new1 mtx51 row1 0 (get x1286 0) with (st836, x1287)
                         in
                         match splitAt x1286 1 with {#label"1" = x1288}
                         in
                         match rec11 st836 new1 mtx51 row1 (addi 0 1) x1288 with (st837, x1289)
                         in
                         (st837, cons x1287 x1289)
                       else match x1286 with [ e16 ]
                       then
                         match splitAt x1286 1 with {#label"1" = x1290}
                         in
                         let slice15 = x1290 in
                         match anon2 st835 new1 mtx51 row1 0 e16 with (st838, x1291)
                         in
                         (st838, [ x1291 ])
                       else match x1286 with ""
                       in
                       (st835, "")
                     with
                       (st839, x1292)
                     in
                     p_traverseSeq
                       st839
                       (lam st840.
                          lam x1293.
                            (st840, x1293))
                       x1292)
                cols1
            with
              (st841, #var"231")
            in
            let #var"1171" = {} in
            (st841, new1)
  in
  let mtxRowCols2 =
    lam st822.
      lam mtx5.
        lam row.
          lam cols.
            match mtx5 with {arr = #var"X33"}
            in
            match p_map st822 length cols with (st823, x1276)
            in
            match
              matMakeUninit1 st823 (externalExtArrKind #var"X33") 1 x1276
            with
              (st824, new)
            in
            match
              p_bind
                st824
                simpleStoreSubmodel
                (simpleInit {})
                (lam st825.
                   lam x1277.
                     match
                       match x1277 with [ _,
                           _ ] ++ _
                       then
                         match anon3 st825 new mtx5 row 0 (get x1277 0) with (st826, x1278)
                         in
                         match splitAt x1277 1 with {#label"1" = x1279}
                         in
                         match rec12 st826 new mtx5 row (addi 0 1) x1279 with (st827, x1280)
                         in
                         (st827, cons x1278 x1280)
                       else match x1277 with [ e15 ]
                       then
                         match splitAt x1277 1 with {#label"1" = x1281}
                         in
                         let slice14 = x1281 in
                         match anon3 st825 new mtx5 row 0 e15 with (st828, x1282)
                         in
                         (st828, [ x1282 ])
                       else match x1277 with ""
                       in
                       (st825, "")
                     with
                       (st829, x1283)
                     in
                     p_traverseSeq
                       st829
                       (lam st830.
                          lam x1284.
                            (st830, x1284))
                       x1283)
                cols
            with
              (st831, #var"23")
            in
            let #var"1170" = {} in
            (st831, new)
  in
  let mtxSclrMul =
    lam st814.
      lam scalar.
        lam mtx41.
          match
            p_map st814 (lam x1263.
                 x1263.m) mtx41
          with
            (st815, m21)
          in
          match
            p_map st815 (lam x1264.
                 x1264.n) mtx41
          with
            (st816, n41)
          in
          match
            p_map
              st816
              (lam x1265.
                 lam x1266.
                   lam x1267.
                     lam x1268.
                       tmOpaque (let b141 = matMakeUninit (externalExtArrKind x1268.arr) x1265 x1266
                        in
                        let #var"1311" = externalCblasCopy x1267 x1268.arr 1 b141.arr 1
                        in
                        let #var"1411" = externalCblasScal x1267 scalar b141.arr 1 in
                        b141))
              m21
          with
            (st817, x1269)
          in
          match p_apply st817 x1269 n41 with (st818, x1270)
          in
          match
            p_map
              st818
              (lam x1271.
                 lam x1272.
                   muli x1271 x1272)
              m21
          with
            (st819, x1273)
          in
          match p_apply st819 x1273 n41 with (st820, x1274)
          in
          match p_apply st820 x1270 x1274 with (st821, x1275)
          in
          p_apply st821 x1275 mtx41
  in
  let mtxTrans =
    lam st813.
      lam mtx3.
        p_map
          st813
          (lam x1262.
             tmOpaque (let b17 = matMakeUninit (externalExtArrKind x1262.arr) x1262.n x1262.m
              in
              let #var"1610" = matTranposeNoAlloc x1262 b17 in
              b17))
          mtx3
  in
  let mtxExp =
    lam st809.
      lam mtx2.
        match
          p_map
            st809
            (lam x1255.
               lam x1256.
                 match x1255 with {m = #var"X29"}
                 in
                 match eqi #var"X29" x1256 with true
                 then
                   match x1255 with {m = #var"X30"}
                   in
                   match x1255 with {n = #var"X31"}
                   in
                   match x1255 with {arr = #var"X32"}
                   in
                   Right
                     { x1255 with arr = externalMatExp #var"X30" #var"X31" #var"X32" }
                 else
                   Left
                     (NotSquare
                        {}))
            mtx2
        with
          (st810, x1257)
        in
        match
          p_map st810 (lam x1258.
               x1258.n) mtx2
        with
          (st811, x1259)
        in
        match p_apply st811 x1257 x1259 with (st812, x1260)
        in
        p_map
          st812
          (lam x1261.
             match x1261 with Left carried72
             then
               match carried72 with NotSquare carried73
               in
               error "Not square"
             else match x1261 with Right carried74
             in
             carried74)
          x1260
  in
  let mtxMul =
    lam st795.
      lam a37.
        lam b5.
          match
            p_map st795 (lam x1230.
                 x1230.n) a37
          with
            (st796, x1231)
          in
          match
            p_map
              st796
              (lam x1232.
                 lam x1233.
                   lam st797.
                     match
                       match eqi x1232 x1233 with true
                       then
                         match
                           p_map
                             st797
                             (lam x1234.
                                x1234.m)
                             a37
                         with
                           (st798, x1235)
                         in
                         match
                           p_map
                             st798
                             (lam x1236.
                                lam x1237.
                                  lam x1238.
                                    lam x1239.
                                      tmOpaque (let c210 = matMakeUninit (externalExtArrKind x1239.arr) x1236 x1237
                                       in
                                       let #var"1210" =
                                         externalCblasGemm
                                           cblasRowMajor
                                           cblasNoTrans
                                           cblasNoTrans
                                           x1236
                                           x1237
                                           x1232
                                           1.
                                           x1238.arr
                                           x1232
                                           x1239.arr
                                           x1237
                                           0.
                                           c210.arr
                                           x1237
                                       in
                                       c210))
                             x1235
                         with
                           (st799, x1240)
                         in
                         match
                           p_map
                             st799 (lam x1241.
                                x1241.n) b5
                         with
                           (st800, x1242)
                         in
                         match p_apply st800 x1240 x1242 with (st801, x1243)
                         in
                         match p_apply st801 x1243 a37 with (st802, x1244)
                         in
                         match p_apply st802 x1244 b5 with (st803, x1245)
                         in
                         (st803, Right
                           x1245)
                       else
                         (st797, Left
                           (DimensionMismatch
                              {}))
                     with
                       (st804, n5)
                     in
                     match n5 with Right x1246
                     then
                       p_map
                         st804
                         (lam x1247.
                            Right
                              x1247)
                         x1246
                     else match n5 with Left x1248
                     in
                     (st804, p_pure (Left
                          x1248)))
              x1231
          with
            (st805, x1249)
          in
          match
            p_map st805 (lam x1250.
                 x1250.m) b5
          with
            (st806, x1251)
          in
          match
            p_subApply st806 simpleStoreSubmodel (simpleInit {}) x1249 x1251
          with
            (st807, x1252)
          in
          match p_join st807 x1252 with (st808, x1253)
          in
          p_map
            st808
            (lam x1254.
               match x1254 with Left carried70
               then
                 error (matErrorToString carried70)
               else match x1254 with Right carried71
               in
               carried71)
            x1253
  in
  let eitherEither =
    lam st794.
      lam e21.
        p_map
          st794
          (lam x1229.
             match x1229 with Left carried68
             then
               error (matErrorToString carried68)
             else match x1229 with Right carried69
             in
             carried69)
          e21
  in
  let mtxElemMul =
    lam st781.
      lam a361.
        lam b41.
          match
            p_map
              st781
              (lam x1207.
                 lam x1208.
                   match x1207 with {m = #var"X27"}
                   in
                   eqi #var"X27" x1208)
              a361
          with
            (st782, x1209)
          in
          match
            p_map st782 (lam x1210.
                 x1210.m) b41
          with
            (st783, x1211)
          in
          match p_apply st783 x1209 x1211 with (st784, x1212)
          in
          match
            p_map
              st784
              (lam x1213.
                 lam x1214.
                   match x1213 with {n = #var"X28"}
                   in
                   eqi #var"X28" x1214)
              a361
          with
            (st785, x1215)
          in
          match
            p_map st785 (lam x1216.
                 x1216.n) b41
          with
            (st786, x1217)
          in
          match p_apply st786 x1215 x1217 with (st787, x1218)
          in
          match and1 st787 x1212 x1218 with (st788, x1219)
          in
          match
            p_bind
              st788
              simpleStoreSubmodel
              (simpleInit {})
              (lam st789.
                 lam x1220.
                   match
                     match x1220 with true
                     then
                       match
                         p_map
                           st789
                           (lam x1221.
                              lam x1222.
                                tmOpaque (let c311 = matMakeUninit (externalExtArrKind x1221.arr) x1221.m x1221.n
                                 in
                                 let #var"1511" = matElemMulNoAlloc x1221 x1222 c311 in
                                 c311))
                           a361
                       with
                         (st790, x1223)
                       in
                       match p_apply st790 x1223 b41 with (st791, x1224)
                       in
                       (st791, Right
                         x1224)
                     else
                       (st789, Left
                         (DimensionMismatch
                            {}))
                   with
                     (st792, n3)
                   in
                   match n3 with Right x1225
                   then
                     p_map
                       st792
                       (lam x1226.
                          Right
                            x1226)
                       x1225
                   else match n3 with Left x1227
                   in
                   (st792, p_pure (Left
                        x1227)))
              x1219
          with
            (st793, x1228)
          in
          eitherEither st793 x1228
  in
  recursive
    let work2 =
      lam bound.
        lam c9.
          lam i31.
            lam acc41.
              match lti i31 bound with true
              then
                match c9 with {arr = #var"X"}
                in
                work2
                  bound
                  c9
                  (addi i31 1)
                  (addf acc41 (externalExtArrGet #var"X" i31))
              else
                acc41
    let work21 =
      lam st21.
        lam bound1.
          lam c10.
            lam i32.
              lam acc42.
                match lti i32 bound1 with true
                then
                  match
                    p_map
                      st21
                      (lam x26.
                         lam x27.
                           addf x26 x27)
                      acc42
                  with
                    (st22, x28)
                  in
                  match c10 with {arr = #var"X1"}
                  in
                  match
                    p_map
                      st22
                      (lam x29.
                         externalExtArrGet x29 i32)
                      #var"X1"
                  with
                    (st23, x30)
                  in
                  match p_apply st23 x28 x30 with (st24, x31)
                  in
                  work21 st24 bound1 c10 (addi i32 1) x31
                else
                  (st21, acc42)
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
    lam st774.
      lam mtx1.
        match mtx1 with {n = #var"X18"}
        in
        match
          p_map
            st774
            (lam x1196.
               match mtx1 with {m = #var"X19"}
               in
               muli #var"X19" x1196)
            #var"X18"
        with
          (st775, x1197)
        in
        match
          p_bind
            st775
            simpleStoreSubmodel
            (simpleInit {})
            (lam st776.
               lam x1198.
                 match lti 0 x1198 with true
                 then
                   match mtx1 with {arr = #var"X20"}
                   in
                   match
                     p_map
                       st776
                       (lam x1199.
                          addf 0. (externalExtArrGet x1199 0))
                       #var"X20"
                   with
                     (st777, x1200)
                   in
                   work21 st777 x1198 mtx1 (addi 0 1) x1200
                 else
                   (st776, p_pure 0.))
            x1197
        with
          (st778, x1201)
        in
        match
          p_map
            st778
            (lam x1202.
               lam x1203.
                 divf x1202 x1203)
            x1201
        with
          (st779, x1204)
        in
        match mtx1 with {n = #var"X21"}
        in
        match
          p_map
            st779
            (lam x1205.
               match mtx1 with {m = #var"X22"}
               in
               int2float (muli #var"X22" x1205))
            #var"X21"
        with
          (st780, x1206)
        in
        p_apply st780 x1204 x1206
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
      lam st25.
        lam seq.
          match null seq with true
          then
            (st25, p_pure false)
          else match
            p_map st25 (lam x32.
                 eqi x32 2) (head seq)
          with
            (st26, x33)
          in
          p_bind
            st26
            simpleStoreSubmodel
            (simpleInit {})
            (lam st27.
               lam x34.
                 match x34 with true
                 then
                   (st27, p_pure true)
                 else
                   any st27 (tail seq))
            x33
  in
  let any1 = lam st773.
      lam l21.
        any st773 l21 in
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
    lam st755.
      lam currRep81.
        lam event31.
          lam nhosts81.
            match
              p_map
                st755
                (lam x1170.
                   match x1170 with Event1 x1552
                   then
                     x1552.host
                   else
                     let #var"1168" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
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
                   lam x1171.
                     (st757, x1171))
                currRep81
            with
              (st758, x1172)
            in
            match
              p_map
                st758
                (lam x1173.
                   subsequence x1173 (subi 1 1))
                x1172
            with
              (st759, x1174)
            in
            match
              p_map
                st759
                (lam x1175.
                   subi x1175 1)
                hostIndex42
            with
              (st760, x1176)
            in
            match p_apply st760 x1174 x1176 with (st761, x1177)
            in
            match
              p_map
                st761
                (lam x1178.
                   match x1178 with Event1 x1542
                   then
                     x1542.toState
                   else
                     let #var"1169" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event31
            with
              (st762, x1179)
            in
            match
              p_traverseSeq
                st762
                (lam st763.
                   lam x1180.
                     (st763, x1180))
                [ x1179 ]
            with
              (st764, x1181)
            in
            match
              p_map
                st764
                (lam x1182.
                   addi x1182 1)
                hostIndex42
            with
              (st765, first1)
            in
            match
              p_traverseSeq
                st765
                (lam st766.
                   lam x1183.
                     (st766, x1183))
                currRep81
            with
              (st767, x1184)
            in
            match p_map st767 subsequence x1184 with (st768, x1185)
            in
            match
              p_map st768 (lam x1186.
                   subi x1186 1) first1
            with
              (st769, x1187)
            in
            match p_apply st769 x1185 x1187 with (st770, x1188)
            in
            match
              p_map
                st770
                (lam x1189.
                   subi (addi nhosts81 1) x1189)
                first1
            with
              (st771, x1190)
            in
            match p_apply st771 x1188 x1190 with (st772, x1195)
            in
            paste02
              st772
              [ x1177,
                x1181,
                x1195 ]
  in
  let updateRepertoire1 =
    lam st741.
      lam currRep8.
        lam event3.
          lam nhosts8.
            match
              p_map
                st741
                (lam x1152.
                   match x1152 with Event1 x1551
                   then
                     x1551.host
                   else
                     let #var"1166" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event3
            with
              (st742, hostIndex41)
            in
            match
              p_map
                st742
                (lam x1153.
                   subsequence x1153 (subi 1 1))
                currRep8
            with
              (st743, x1154)
            in
            match
              p_map
                st743
                (lam x1155.
                   subi x1155 1)
                hostIndex41
            with
              (st744, x1156)
            in
            match p_apply st744 x1154 x1156 with (st745, x1157)
            in
            match
              p_map
                st745
                (lam x1158.
                   match x1158 with Event1 x1541
                   then
                     x1541.toState
                   else
                     let #var"1167" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event3
            with
              (st746, x1159)
            in
            match
              p_traverseSeq
                st746
                (lam st747.
                   lam x1160.
                     (st747, x1160))
                [ x1159 ]
            with
              (st748, x1161)
            in
            match
              p_map
                st748
                (lam x1162.
                   addi x1162 1)
                hostIndex41
            with
              (st749, first)
            in
            match p_map st749 subsequence currRep8 with (st750, x1163)
            in
            match
              p_map st750 (lam x1164.
                   subi x1164 1) first
            with
              (st751, x1165)
            in
            match p_apply st751 x1163 x1165 with (st752, x1166)
            in
            match
              p_map
                st752
                (lam x1167.
                   subi (addi nhosts8 1) x1167)
                first
            with
              (st753, x1168)
            in
            match p_apply st753 x1166 x1168 with (st754, x1169)
            in
            paste02
              st754
              [ x1157,
                x1161,
                x1169 ]
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
      lam c11.
        lam s.
          match s with [ _,
              _ ] ++ _
          then
            match splitAt s 1 with {#label"1" = x35}
            in
            cons (anon4 c11 (get s 0)) (rec c11 x35)
          else match s with [ e5 ]
          then
            match splitAt s 1 with {#label"1" = x36}
            in
            let slice4 = x36 in
            [ anon4 c11 e5 ]
          else match s with ""
          in
          ""
    let map1 = lam c12.
        lam s15.
          rec c12 s15
    let rec3 =
      lam i11.
        lam acc11.
          match geqi i11 0 with true
          then
            rec3 (subi i11 1) (cons (anon5 i11) acc11)
          else
            acc11
    let create1 =
      lam l6.
        let i12 = subi l6 1 in
        match geqi i12 0 with true
        then
          rec3 (subi i12 1) (cons (anon5 i12) "")
        else
          ""
    let anon4 =
      lam interaction.
        lam x37.
          match eqi (subi (addi interaction 1) 1) x37 with true
          then
            1.
          else
            0.
    let anon5 = lam x38.
        1.
    let observationMessage =
      lam obsRepertoire.
        lam i4.
          lam max.
            match leqi i4 max with true
            then
              let interaction1 = get obsRepertoire (subi i4 1) in
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
                  create1 3
              in
              cons1
                (get stateMsg (subi 1 1))
                (cons1
                   (get stateMsg (subi 2 1))
                   (cons1
                      (get stateMsg (subi 3 1))
                      (observationMessage obsRepertoire (addi i4 1) max)))
            else
              ""
    let observationMessage1 =
      lam st28.
        lam obsRepertoire1.
          lam i41.
            lam max1.
              match leqi i41 max1 with true
              then
                match
                  p_map
                    st28
                    (lam x39.
                       match
                         match geqi x39 0 with true
                         then
                           leqi x39 2
                         else
                           false
                       with
                         true
                       then
                         map1 x39 (unfoldr 0)
                       else
                         create1 3)
                    (get obsRepertoire1 (subi i41 1))
                with
                  (st29, stateMsg1)
                in
                match
                  p_map
                    st29
                    (lam x40.
                       get x40 (subi 1 1))
                    stateMsg1
                with
                  (st30, x41)
                in
                match
                  p_map
                    st30
                    (lam x42.
                       get x42 (subi 2 1))
                    stateMsg1
                with
                  (st31, x43)
                in
                match
                  p_map
                    st31
                    (lam x44.
                       get x44 (subi 3 1))
                    stateMsg1
                with
                  (st32, x45)
                in
                match
                  observationMessage1 st32 obsRepertoire1 (addi i41 1) max1
                with
                  (st33, x46)
                in
                (st33, cons12 x41 (cons12 x43 (cons12 x45 x46)))
              else
                (st28, "")
  in
  recursive
    let postorderTraverse =
      lam st34.
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
                                  let #var"12" =
                                    print
                                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 9:70-9:80>:\nField \'label\' not found\n[0m    let outmsg = mtxCreate(nhosts, 3, observationMessage(interactions[[31mtree.label[0m[0m], 1, nhosts));\n"
                                  in
                                  exit 1)
                               1))
                         1
                         nhosts1)
                  in
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
                            let #var"11" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 10:32-10:42>:\nField \'label\' not found\n[0m    let leafInts = interactions[[31mtree.label[0m[0m];\n"
                            in
                            exit 1)
                         1)
                  in
                  (st34, MsgLeaf
                    { age = 0.,
                      label =
                        match tree1 with Leaf carried2
                        then
                          carried2.label
                        else match tree1 with Node carried3
                        then
                          carried3.label
                        else
                          let #var"1" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 13:14-13:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                          in
                          exit 1,
                      interactions = leafInts,
                      outMsg =
                        mtxCreate nhosts1 3 (observationMessage leafInts 1 nhosts1) })
                else match
                  postorderTraverse
                    st34
                    (match tree1 with Node x231
                     then
                       x231.left
                     else
                       let #var"13" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 19:31-19:40>:\nField \'left\' not found\n[0m  let left = postorderTraverse([31mtree.left[0m[0m, qMatrix, interactions, nhosts);\n"
                       in
                       exit 1)
                    qMatrix1
                    interactions1
                    nhosts1
                with
                  (st35, left)
                in
                match
                  postorderTraverse
                    st35
                    (match tree1 with Node x221
                     then
                       x221.right
                     else
                       let #var"14" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 20:32-20:42>:\nField \'right\' not found\n[0m  let right = postorderTraverse([31mtree.right[0m[0m, qMatrix, interactions, nhosts);\n"
                       in
                       exit 1)
                    qMatrix1
                    interactions1
                    nhosts1
                with
                  (st36, right)
                in
                match
                  mtxSclrMul
                    st36
                    (subf
                       (match tree1 with Leaf carried8
                        then
                          carried8.age
                        else match tree1 with Node carried9
                        then
                          carried9.age
                        else
                          let #var"15" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:37-23:45>:\nField \'age\' not found\n[0m  let leftKernel = mtxExp(mtxSclrMul([31mtree.age[0m[0m-left.age, qMatrix));\n"
                          in
                          exit 1)
                       (match left with MsgLeaf carried10
                        then
                          carried10.age
                        else match left with MsgNode carried11
                        then
                          carried11.age
                        else
                          let #var"16" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:46-23:54>:\nField \'age\' not found\n[0m  let leftKernel = mtxExp(mtxSclrMul(tree.age-[31mleft.age[0m[0m, qMatrix));\n"
                          in
                          exit 1))
                    qMatrix1
                with
                  (st37, x47)
                in
                match mtxExp st37 x47 with (st38, leftKernel)
                in
                match
                  mtxSclrMul
                    st38
                    (subf
                       (match tree1 with Leaf carried12
                        then
                          carried12.age
                        else match tree1 with Node carried13
                        then
                          carried13.age
                        else
                          let #var"17" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:38-24:46>:\nField \'age\' not found\n[0m  let rightKernel = mtxExp(mtxSclrMul([31mtree.age[0m[0m-right.age, qMatrix));\n"
                          in
                          exit 1)
                       (match right with MsgLeaf carried14
                        then
                          carried14.age
                        else match right with MsgNode carried15
                        then
                          carried15.age
                        else
                          let #var"18" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:47-24:56>:\nField \'age\' not found\n[0m  let rightKernel = mtxExp(mtxSclrMul(tree.age-[31mright.age[0m[0m, qMatrix));\n"
                          in
                          exit 1))
                    qMatrix1
                with
                  (st39, x48)
                in
                match mtxExp st39 x48 with (st40, rightKernel)
                in
                match mtxTrans st40 leftKernel with (st41, x49)
                in
                match
                  mtxMul
                    st41
                    (match left with MsgLeaf carried16
                     then
                       match carried16 with {outMsg = #var"X2"}
                       in
                       p_pure #var"X2"
                     else match left with MsgNode carried17
                     then
                       carried17.outMsg
                     else
                       let #var"19" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:25-30:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n"
                       in
                       p_pure (exit 1))
                    x49
                with
                  (st42, leftInMsg)
                in
                match mtxTrans st42 rightKernel with (st43, x50)
                in
                match
                  mtxMul
                    st43
                    (match right with MsgLeaf carried18
                     then
                       match carried18 with {outMsg = #var"X3"}
                       in
                       p_pure #var"X3"
                     else match right with MsgNode carried19
                     then
                       carried19.outMsg
                     else
                       let #var"110" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 31:26-31:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n"
                       in
                       p_pure (exit 1))
                    x50
                with
                  (st44, rightInMsg)
                in
                match mtxElemMul st44 leftInMsg rightInMsg with (st45, x51)
                in
                (st45, MsgNode
                  { age =
                      match tree1 with Leaf carried20
                      then
                        carried20.age
                      else match tree1 with Node carried21
                      then
                        carried21.age
                      else
                        let #var"111" =
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
                        let #var"112" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:28-36:38>:\nField \'label\' not found\n[0m    age = tree.age, label = [31mtree.label[0m[0m,\n"
                        in
                        exit 1,
                    left = left,
                    right = right,
                    rightKernel = rightKernel,
                    leftKernel = leftKernel,
                    outMsg = x51,
                    leftInMsg = leftInMsg,
                    rightInMsg = rightInMsg })
  in
  let mtx3ToSeq =
    lam st728.
      lam mtx.
        lam i115.
          match mtxGet st728 i115 1 mtx with (st729, p111)
          in
          match mtxGet st729 i115 2 mtx with (st730, p210)
          in
          match mtxGet st730 i115 3 mtx with (st731, p310)
          in
          match
            p_map
              st731
              (lam x1133.
                 lam x1134.
                   lam x1135.
                     addf (addf x1133 x1134) x1135)
              p111
          with
            (st732, x1136)
          in
          match p_apply st732 x1136 p210 with (st733, x1137)
          in
          match p_apply st733 x1137 p310 with (st734, s51)
          in
          match
            p_map
              st734
              (lam x1138.
                 lam x1139.
                   divf x1138 x1139)
              p111
          with
            (st735, x1140)
          in
          match p_apply st735 x1140 s51 with (st736, x1142)
          in
          match
            p_map
              st736
              (lam x1143.
                 lam x1144.
                   divf x1143 x1144)
              p210
          with
            (st737, x1145)
          in
          match p_apply st737 x1145 s51 with (st738, x1146)
          in
          match
            p_map
              st738
              (lam x1147.
                 lam x1148.
                   divf x1147 x1148)
              p310
          with
            (st739, x1149)
          in
          match p_apply st739 x1149 s51 with (st740, x1150)
          in
          (st740, [ x1142,
            x1146,
            x1150 ])
  in
  recursive
    let rec25 =
      lam st46.
        lam c13.
          lam c14.
            lam acc5.
              lam s25.
                match s25 with [ _ ] ++ _
                then
                  let x52 = get s25 0 in
                  match
                    p_map
                      st46
                      (lam x53.
                         lam x54.
                           addf x53 x54)
                      acc5
                  with
                    (st47, x55)
                  in
                  match mtx3ToSeq st47 c14 x52 with (st48, params)
                  in
                  match
                    p_bind
                      st48
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st49.
                         lam x56.
                           match
                             match geqi x56 0 with true
                             then
                               lti x56 (length12 params)
                             else
                               false
                           with
                             true
                           then
                             log11 st49 (get params (subi (addi x56 1) 1))
                           else
                             (st49, p_pure (log1 0.)))
                      (get c13 (subi x52 1))
                  with
                    (st50, x57)
                  in
                  match p_apply st50 x55 x57 with (st51, x58)
                  in
                  match splitAt s25 1 with {#label"1" = x59}
                  in
                  rec25 st51 c13 c14 x58 x59
                else match s25 with ""
                in
                (st46, acc5)
  in
  let anon6 = lam x1132.
      addi x1132 1 in
  recursive
    let rec31 =
      lam i13.
        lam acc12.
          match geqi i13 0 with true
          then
            rec31 (subi i13 1) (cons (anon6 i13) acc12)
          else
            acc12
  in
  let getRepertoireSamplingDensity =
    lam st723.
      lam x1501.
        lam samplingProb1.
          lam nhosts7.
            let i114 = subi (addi (subi nhosts7 1) 1) 1 in
            let s227 =
              match geqi i114 0 with true
              then
                rec31 (subi i114 1) (cons (anon6 i114) "")
              else
                ""
            in
            match s227 with [ _ ] ++ _
            then
              let x1125 = get s227 0 in
              match mtx3ToSeq st723 samplingProb1 x1125 with (st724, params1)
              in
              match
                p_bind
                  st724
                  simpleStoreSubmodel
                  (simpleInit {})
                  (lam st725.
                     lam x1126.
                       match
                         match geqi x1126 0 with true
                         then
                           lti x1126 (length12 params1)
                         else
                           false
                       with
                         true
                       then
                         log11 st725 (get params1 (subi (addi x1126 1) 1))
                       else
                         (st725, p_pure (log1 0.)))
                  (get x1501 (subi x1125 1))
              with
                (st726, x1127)
              in
              match
                p_map st726 (lam x1128.
                     addf 0. x1128) x1127
              with
                (st727, x1129)
              in
              match splitAt s227 1 with {#label"1" = x1130}
              in
              rec25 st727 x1501 samplingProb1 x1129 x1130
            else match s227 with ""
            in
            (st723, p_pure 0.)
  in
  recursive
    let rec26 =
      lam st52.
        lam acc6.
          lam s26.
            match s26 with [ _ ] ++ _
            then
              match
                p_bind
                  st52
                  simpleStoreSubmodel
                  (simpleInit {})
                  (lam st53.
                     lam x60.
                       match eqi x60 2 with true
                       then
                         p_map
                           st53 (lam x61.
                              addi x61 1) acc6
                       else
                         (st53, acc6))
                  (get s26 0)
              with
                (st54, x62)
              in
              match splitAt s26 1 with {#label"1" = x63}
              in
              rec26 st54 x62 x63
            else match s26 with ""
            in
            (st52, acc6)
    let fold =
      lam st55.
        lam init1.
          lam seq5.
            match seq5 with [ _ ] ++ _
            then
              match
                p_map
                  st55
                  (lam x64.
                     match eqi x64 2 with true
                     then
                       addi init1 1
                     else
                       init1)
                  (get seq5 0)
              with
                (st56, x65)
              in
              match splitAt seq5 1 with {#label"1" = x66}
              in
              rec26 st56 x65 x66
            else match seq5 with ""
            in
            (st55, p_pure init1)
    let ifCont3 =
      lam st57.
        lam currRep.
          lam eventSeq.
            lam eventIndex.
              lam nEvents.
                lam nhosts2.
                  lam event.
                    lam #var"2".
                      let hostIndex4 =
                        match event with Event1 x155
                        then
                          x155.host
                        else
                          let #var"115" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                          in
                          exit 1
                      in
                      let s27 =
                        [ slice currRep 1 hostIndex4,
                          [ p_pure
                              (match event with Event1 x154
                               then
                                 x154.toState
                               else
                                 let #var"114" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                                 in
                                 exit 1) ],
                          slice currRep (addi hostIndex4 1) (addi nhosts2 1) ]
                      in
                      let currRep1 =
                        match s27 with [ _ ] ++ _
                        then
                          match splitAt s27 1 with {#label"1" = x72}
                          in
                          rec21 (concat "" (get s27 0)) x72
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
                          (lam x67.
                             get x67 (subi eventIndex1 1))
                          eventSeq
                      with
                        (st58, x68)
                      in
                      p_bind
                        st58
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st59.
                           lam x69.
                             match
                               eqi
                                 (match x69 with Event1 x301
                                  then
                                    x301.fromState
                                  else
                                    let #var"113" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 147:7-147:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                                    in
                                    exit 1)
                                 2
                             with
                               true
                             then
                               match fold st59 0 currRep1 with (st60, x70)
                               in
                               p_bind
                                 st60
                                 simpleStoreSubmodel
                                 (simpleInit {})
                                 (lam st61.
                                    lam x71.
                                      match eqi x71 1 with true
                                      then
                                        (st61, p_pure false)
                                      else
                                        ifCont3 st61 currRep1 eventSeq eventIndex1 nEvents nhosts2 x69 0)
                                 x70
                             else
                               ifCont3 st59 currRep1 eventSeq eventIndex1 nEvents nhosts2 x69 0)
                        x68
    let allTimesValidBranch =
      lam st62.
        lam currRep11.
          lam eventSeq1.
            lam eventIndex11.
              lam nEvents1.
                lam nhosts3.
                  p_bind
                    st62
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st63.
                       lam x73.
                         match gti eventIndex11 x73 with true
                         then
                           (st63, p_pure true)
                         else match
                           p_map
                             st63
                             (lam x74.
                                get x74 (subi eventIndex11 1))
                             eventSeq1
                         with
                           (st64, x75)
                         in
                         p_bind
                           st64
                           simpleStoreSubmodel
                           (simpleInit {})
                           (lam st65.
                              lam x76.
                                match
                                  eqi
                                    (match x76 with Event1 x302
                                     then
                                       x302.fromState
                                     else
                                       let #var"116" =
                                         print
                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 147:7-147:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                                       in
                                       exit 1)
                                    2
                                with
                                  true
                                then
                                  match fold st65 0 currRep11 with (st66, x77)
                                  in
                                  p_bind
                                    st66
                                    simpleStoreSubmodel
                                    (simpleInit {})
                                    (lam st67.
                                       lam x78.
                                         match eqi x78 1 with true
                                         then
                                           (st67, p_pure false)
                                         else
                                           ifCont3 st67 currRep11 eventSeq1 eventIndex11 x73 nhosts3 x76 0)
                                    x77
                                else
                                  ifCont3 st65 currRep11 eventSeq1 eventIndex11 x73 nhosts3 x76 0)
                           x75)
                    nEvents1
  in
  let anon7 =
    lam x1124.
      match eqi x1124 2 with true
      then
        true
      else
        eqi x1124 1
  in
  let anon8 =
    lam st722.
      lam x1122.
        p_map
          st722
          (lam x1123.
             match eqi x1123 2 with true
             then
               true
             else
               eqi x1123 1)
          x1122
  in
  recursive
    let rec4 =
      lam s4.
        match s4 with [ _,
            _ ] ++ _
        then
          match splitAt s4 1 with {#label"1" = x79}
          in
          cons (anon7 (get s4 0)) (rec4 x79)
        else match s4 with [ e6 ]
        then
          match splitAt s4 1 with {#label"1" = x80}
          in
          let slice5 = x80 in
          [ anon7 e6 ]
        else match s4 with ""
        in
        ""
    let rec5 =
      lam st68.
        lam s5.
          match s5 with [ _,
              _ ] ++ _
          then
            match anon8 st68 (get s5 0) with (st69, x81)
            in
            match splitAt s5 1 with {#label"1" = x82}
            in
            match rec5 st69 x82 with (st70, x83)
            in
            (st70, cons x81 x83)
          else match s5 with [ e7 ]
          then
            match splitAt s5 1 with {#label"1" = x84}
            in
            let slice6 = x84 in
            match anon8 st68 e7 with (st71, x85)
            in
            (st71, [ x85 ])
          else match s5 with ""
          in
          (st68, "")
  in
  let sapply = lam st721.
      lam s72.
        rec5 st721 s72
  in
  let anon9 = lam x1121.
      eqi x1121 2 in
  let anon10 =
    lam st720.
      lam x1119.
        p_map st720 (lam x1120.
             eqi x1120 2) x1119
  in
  recursive
    let rec6 =
      lam s6.
        match s6 with [ _,
            _ ] ++ _
        then
          match splitAt s6 1 with {#label"1" = x86}
          in
          cons (anon9 (get s6 0)) (rec6 x86)
        else match s6 with [ e8 ]
        then
          match splitAt s6 1 with {#label"1" = x87}
          in
          let slice7 = x87 in
          [ anon9 e8 ]
        else match s6 with ""
        in
        ""
    let rec7 =
      lam st72.
        lam s7.
          match s7 with [ _,
              _ ] ++ _
          then
            match anon10 st72 (get s7 0) with (st73, x88)
            in
            match splitAt s7 1 with {#label"1" = x89}
            in
            match rec7 st73 x89 with (st74, x90)
            in
            (st74, cons x88 x90)
          else match s7 with [ e9 ]
          then
            match splitAt s7 1 with {#label"1" = x91}
            in
            let slice8 = x91 in
            match anon10 st72 e9 with (st75, x92)
            in
            (st75, [ x92 ])
          else match s7 with ""
          in
          (st72, "")
  in
  let sapply1 = lam st719.
      lam s71.
        rec7 st719 s71
  in
  let getGainRate =
    lam st711.
      lam repertoire14.
        lam hostIndex33.
          lam modelParams123.
            let fromState53 = get repertoire14 (subi hostIndex33 1) in
            match
              mtxGet
                st711
                (addi fromState53 1)
                (addi (addi fromState53 1) 1)
                (match
                   match modelParams123 with ModelParams1 x1464
                   then
                     x1464.embeddedQMatrix
                   else
                     let #var"1158" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 113:52-113:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1454
                 then
                   x1454.mat
                 else
                   let #var"1159" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 113:52-113:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st712, baseRate13)
            in
            match eqi fromState53 0 with true
            then
              match
                p_map
                  st712
                  (lam x1107.
                     lam x1108.
                       mulf x1107 x1108)
                  baseRate13
              with
                (st713, x1109)
              in
              match
                p_map
                  st713
                  (lam x1110.
                     negf x1110)
                  (match modelParams123 with ModelParams1 x1404
                   then
                     x1404.beta
                   else
                     let #var"1160" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:38-123:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                     in
                     p_pure (exit 1))
              with
                (st714, x1111)
              in
              match
                pow1
                  st714
                  (divf
                     (mtxMean
                        (mtxRowCols
                           (match modelParams123 with ModelParams1 x1414
                            then
                              x1414.hostMetric
                            else
                              let #var"1161" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                              in
                              exit 1)
                           hostIndex33
                           (whichTrue (rec4 repertoire14))))
                     (match modelParams123 with ModelParams1 x1394
                      then
                        x1394.meanDist
                      else
                        let #var"1162" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:14-123:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                        in
                        exit 1))
                  x1111
              with
                (st715, x1112)
              in
              p_apply st715 x1109 x1112
            else match
              p_map
                st712
                (lam x1113.
                   lam x1114.
                     mulf x1113 x1114)
                baseRate13
            with
              (st716, x1115)
            in
            match
              p_map
                st716
                (lam x1116.
                   negf x1116)
                (match modelParams123 with ModelParams1 x1434
                 then
                   x1434.beta
                 else
                   let #var"1163" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:38-132:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                   in
                   p_pure (exit 1))
            with
              (st717, x1117)
            in
            match
              pow1
                st717
                (divf
                   (mtxMean
                      (mtxRowCols
                         (match modelParams123 with ModelParams1 x1444
                          then
                            x1444.hostMetric
                          else
                            let #var"1164" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex33
                         (whichTrue (rec6 repertoire14))))
                   (match modelParams123 with ModelParams1 x1424
                    then
                      x1424.meanDist
                    else
                      let #var"1165" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:14-132:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                      in
                      exit 1))
                x1117
            with
              (st718, x1118)
            in
            p_apply st718 x1115 x1118
  in
  let getGainRate1 =
    lam st690.
      lam repertoire13.
        lam hostIndex32.
          lam modelParams122.
            let fromState52 = get repertoire13 (subi hostIndex32 1) in
            match
              p_map
                st690
                (lam x1075.
                   addi x1075 1)
                fromState52
            with
              (st691, x1076)
            in
            match
              p_map
                st691
                (lam x1077.
                   addi (addi x1077 1) 1)
                fromState52
            with
              (st692, x1078)
            in
            match
              mtxGet2
                st692
                x1076
                x1078
                (match
                   match modelParams122 with ModelParams1 x1463
                   then
                     x1463.embeddedQMatrix
                   else
                     let #var"1150" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 113:52-113:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1453
                 then
                   x1453.mat
                 else
                   let #var"1151" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 113:52-113:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st693, baseRate12)
            in
            p_bind
              st693
              simpleStoreSubmodel
              (simpleInit {})
              (lam st694.
                 lam x1079.
                   match eqi x1079 0 with true
                   then
                     match
                       p_map
                         st694
                         (lam x1080.
                            lam x1083.
                              mulf x1080 x1083)
                         baseRate12
                     with
                       (st695, x1084)
                     in
                     match sapply st695 repertoire13 with (st696, x1085)
                     in
                     match whichTrue1 st696 x1085 with (st697, x1086)
                     in
                     match
                       mtxRowCols1
                         st697
                         (match modelParams122 with ModelParams1 x1413
                          then
                            x1413.hostMetric
                          else
                            let #var"1152" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex32
                         x1086
                     with
                       (st698, x1087)
                     in
                     match mtxMean1 st698 x1087 with (st699, x1088)
                     in
                     match
                       p_map
                         st699
                         (lam x1089.
                            divf
                              x1089
                              (match modelParams122 with ModelParams1 x1393
                               then
                                 x1393.meanDist
                               else
                                 let #var"1153" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:14-123:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x1088
                     with
                       (st700, x1090)
                     in
                     match
                       p_map
                         st700
                         (lam x1092.
                            negf x1092)
                         (match modelParams122 with ModelParams1 x1403
                          then
                            x1403.beta
                          else
                            let #var"1154" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:38-123:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st701, x1093)
                     in
                     match pow2 st701 x1090 x1093 with (st702, x1094)
                     in
                     p_apply st702 x1084 x1094
                   else match
                     p_map
                       st694
                       (lam x1095.
                          lam x1096.
                            mulf x1095 x1096)
                       baseRate12
                   with
                     (st703, x1097)
                   in
                   match sapply1 st703 repertoire13 with (st704, x1098)
                   in
                   match whichTrue1 st704 x1098 with (st705, x1099)
                   in
                   match
                     mtxRowCols1
                       st705
                       (match modelParams122 with ModelParams1 x1443
                        then
                          x1443.hostMetric
                        else
                          let #var"1155" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex32
                       x1099
                   with
                     (st706, x1100)
                   in
                   match mtxMean1 st706 x1100 with (st707, x1101)
                   in
                   match
                     p_map
                       st707
                       (lam x1102.
                          divf
                            x1102
                            (match modelParams122 with ModelParams1 x1423
                             then
                               x1423.meanDist
                             else
                               let #var"1156" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:14-132:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1101
                   with
                     (st708, x1103)
                   in
                   match
                     p_map
                       st708
                       (lam x1104.
                          negf x1104)
                       (match modelParams122 with ModelParams1 x1433
                        then
                          x1433.beta
                        else
                          let #var"1157" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:38-132:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st709, x1105)
                   in
                   match pow2 st709 x1103 x1105 with (st710, x1106)
                   in
                   p_apply st710 x1097 x1106)
              fromState52
  in
  let getGainRate2 =
    lam st664.
      lam repertoire12.
        lam hostIndex31.
          lam modelParams121.
            match
              p_traverseSeq
                st664
                (lam st665.
                   lam x1035.
                     (st665, x1035))
                repertoire12
            with
              (st666, x1036)
            in
            match p_map st666 get x1036 with (st667, x1037)
            in
            match
              p_map
                st667
                (lam x1038.
                   subi x1038 1)
                hostIndex31
            with
              (st668, x1039)
            in
            match p_apply st668 x1037 x1039 with (st669, fromState51)
            in
            match
              p_map
                st669
                (lam x1040.
                   addi x1040 1)
                fromState51
            with
              (st670, x1043)
            in
            match
              p_map
                st670
                (lam x1044.
                   addi (addi x1044 1) 1)
                fromState51
            with
              (st671, x1045)
            in
            match
              mtxGet2
                st671
                x1043
                x1045
                (match
                   match modelParams121 with ModelParams1 x1462
                   then
                     x1462.embeddedQMatrix
                   else
                     let #var"1142" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 113:52-113:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1452
                 then
                   x1452.mat
                 else
                   let #var"1143" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 113:52-113:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st672, baseRate11)
            in
            p_bind
              st672
              simpleStoreSubmodel
              (simpleInit {})
              (lam st673.
                 lam x1046.
                   match eqi x1046 0 with true
                   then
                     match
                       p_map
                         st673
                         (lam x1047.
                            lam x1048.
                              mulf x1047 x1048)
                         baseRate11
                     with
                       (st674, x1049)
                     in
                     match sapply st674 repertoire12 with (st675, x1050)
                     in
                     match whichTrue1 st675 x1050 with (st676, x1051)
                     in
                     match
                       mtxRowCols2
                         st676
                         (match modelParams121 with ModelParams1 x1412
                          then
                            x1412.hostMetric
                          else
                            let #var"1144" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex31
                         x1051
                     with
                       (st677, x1052)
                     in
                     match mtxMean1 st677 x1052 with (st678, x1053)
                     in
                     match
                       p_map
                         st678
                         (lam x1054.
                            divf
                              x1054
                              (match modelParams121 with ModelParams1 x1392
                               then
                                 x1392.meanDist
                               else
                                 let #var"1145" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:14-123:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x1053
                     with
                       (st679, x1055)
                     in
                     match
                       p_map
                         st679
                         (lam x1056.
                            negf x1056)
                         (match modelParams121 with ModelParams1 x1402
                          then
                            x1402.beta
                          else
                            let #var"1146" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:38-123:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st680, x1057)
                     in
                     match pow2 st680 x1055 x1057 with (st681, x1058)
                     in
                     p_apply st681 x1049 x1058
                   else match
                     p_map
                       st673
                       (lam x1059.
                          lam x1060.
                            mulf x1059 x1060)
                       baseRate11
                   with
                     (st682, x1063)
                   in
                   match sapply1 st682 repertoire12 with (st683, x1064)
                   in
                   match whichTrue1 st683 x1064 with (st684, x1065)
                   in
                   match
                     mtxRowCols2
                       st684
                       (match modelParams121 with ModelParams1 x1442
                        then
                          x1442.hostMetric
                        else
                          let #var"1147" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex31
                       x1065
                   with
                     (st685, x1066)
                   in
                   match mtxMean1 st685 x1066 with (st686, x1067)
                   in
                   match
                     p_map
                       st686
                       (lam x1068.
                          divf
                            x1068
                            (match modelParams121 with ModelParams1 x1422
                             then
                               x1422.meanDist
                             else
                               let #var"1148" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:14-132:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1067
                   with
                     (st687, x1069)
                   in
                   match
                     p_map
                       st687
                       (lam x1070.
                          negf x1070)
                       (match modelParams121 with ModelParams1 x1432
                        then
                          x1432.beta
                        else
                          let #var"1149" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:38-132:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st688, x1073)
                   in
                   match pow2 st688 x1069 x1073 with (st689, x1074)
                   in
                   p_apply st689 x1063 x1074)
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
                   match modelParams12 with ModelParams1 x1461
                   then
                     x1461.embeddedQMatrix
                   else
                     let #var"1134" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 113:52-113:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1451
                 then
                   x1451.mat
                 else
                   let #var"1135" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 113:52-113:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
            with
              (st646, baseRate1)
            in
            p_bind
              st646
              simpleStoreSubmodel
              (simpleInit {})
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
                              cons (anon7 (get x1008 0)) (rec4 x1009)
                            else match x1008 with [ e13 ]
                            then
                              match splitAt x1008 1 with {#label"1" = x1010}
                              in
                              let slice12 = x1010 in
                              [ anon7 e13 ]
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
                         (match modelParams12 with ModelParams1 x1411
                          then
                            x1411.hostMetric
                          else
                            let #var"1136" =
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
                            divf
                              x1015
                              (match modelParams12 with ModelParams1 x1391
                               then
                                 x1391.meanDist
                               else
                                 let #var"1137" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:14-123:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x1014
                     with
                       (st653, x1016)
                     in
                     match
                       p_map
                         st653
                         (lam x1017.
                            negf x1017)
                         (match modelParams12 with ModelParams1 x1401
                          then
                            x1401.beta
                          else
                            let #var"1138" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 123:38-123:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st654, x1018)
                     in
                     match pow2 st654 x1016 x1018 with (st655, x1019)
                     in
                     p_apply st655 x1007 x1019
                   else match
                     p_map
                       st647
                       (lam x1020.
                          lam x1021.
                            mulf x1020 x1021)
                       baseRate1
                   with
                     (st656, x1022)
                   in
                   match
                     p_map
                       st656
                       (lam x1023.
                          match x1023 with [ _,
                              _ ] ++ _
                          then
                            match splitAt x1023 1 with {#label"1" = x1024}
                            in
                            cons (anon9 (get x1023 0)) (rec6 x1024)
                          else match x1023 with [ e14 ]
                          then
                            match splitAt x1023 1 with {#label"1" = x1025}
                            in
                            let slice13 = x1025 in
                            [ anon9 e14 ]
                          else match x1023 with ""
                          in
                          "")
                       repertoire11
                   with
                     (st657, x1026)
                   in
                   match whichTrue2 st657 x1026 with (st658, x1027)
                   in
                   match
                     mtxRowCols2
                       st658
                       (match modelParams12 with ModelParams1 x1441
                        then
                          x1441.hostMetric
                        else
                          let #var"1139" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex3
                       x1027
                   with
                     (st659, x1028)
                   in
                   match mtxMean1 st659 x1028 with (st660, x1029)
                   in
                   match
                     p_map
                       st660
                       (lam x1030.
                          divf
                            x1030
                            (match modelParams12 with ModelParams1 x1421
                             then
                               x1421.meanDist
                             else
                               let #var"1140" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:14-132:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1029
                   with
                     (st661, x1031)
                   in
                   match
                     p_map
                       st661
                       (lam x1032.
                          negf x1032)
                       (match modelParams12 with ModelParams1 x1431
                        then
                          x1431.beta
                        else
                          let #var"1141" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 132:38-132:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st662, x1033)
                   in
                   match pow2 st662 x1031 x1033 with (st663, x1034)
                   in
                   p_apply st663 x1022 x1034)
              fromState5
  in
  let anon11 =
    lam x995.
      lam x996.
        match eqi x996 2 with true
        then
          addi x995 1
        else
          x995
  in
  recursive
    let rec27 =
      lam acc7.
        lam s28.
          match s28 with [ _ ] ++ _
          then
            match splitAt s28 1 with {#label"1" = x93}
            in
            rec27 (anon11 acc7 (get s28 0)) x93
          else match s28 with ""
          in
          acc7
    let rec28 =
      lam st76.
        lam acc8.
          lam s29.
            match s29 with [ _ ] ++ _
            then
              match
                p_bind
                  st76
                  simpleStoreSubmodel
                  (simpleInit {})
                  (lam st77.
                     lam x94.
                       match eqi x94 2 with true
                       then
                         p_map
                           st77 (lam x95.
                              addi x95 1) acc8
                       else
                         (st77, acc8))
                  (get s29 0)
              with
                (st78, x96)
              in
              match splitAt s29 1 with {#label"1" = x97}
              in
              rec28 st78 x96 x97
            else match s29 with ""
            in
            (st76, acc8)
  in
  let fold1 =
    lam st638.
      lam init12.
        lam seq52.
          match seq52 with [ _ ] ++ _
          then
            match
              p_map
                st638
                (lam x992.
                   match eqi x992 2 with true
                   then
                     addi init12 1
                   else
                     init12)
                (get seq52 0)
            with
              (st639, x993)
            in
            match splitAt seq52 1 with {#label"1" = x994}
            in
            rec28 st639 x993 x994
          else match seq52 with ""
          in
          (st638, p_pure init12)
  in
  let getLossRate =
    lam st637.
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
              (st637, p_pure 0.)
            else
              mtxGet
                st637
                (addi fromState33 1)
                (addi (subi fromState33 1) 1)
                (match
                   match modelParams103 with ModelParams1 x1374
                   then
                     x1374.embeddedQMatrix
                   else
                     let #var"1132" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 101:54-101:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1364
                 then
                   x1364.mat
                 else
                   let #var"1133" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 101:54-101:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   p_pure (exit 1))
  in
  let getLossRate1 =
    lam st630.
      lam repertoire2.
        lam hostIndex22.
          lam modelParams102.
            let fromState32 = get repertoire2 (subi hostIndex22 1) in
            match
              p_bind
                st630
                simpleStoreSubmodel
                (simpleInit {})
                (lam st631.
                   lam x983.
                     match eqi x983 2 with true
                     then
                       match fold1 st631 0 repertoire2 with (st632, x984)
                       in
                       p_map
                         st632 (lam x985.
                            eqi x985 1) x984
                     else
                       (st631, p_pure false))
                fromState32
            with
              (st633, x986)
            in
            p_bind
              st633
              simpleStoreSubmodel
              (simpleInit {})
              (lam st634.
                 lam x987.
                   match x987 with true
                   then
                     (st634, p_pure 0.)
                   else match
                     p_map
                       st634
                       (lam x988.
                          addi x988 1)
                       fromState32
                   with
                     (st635, x989)
                   in
                   match
                     p_map
                       st635
                       (lam x990.
                          addi (subi x990 1) 1)
                       fromState32
                   with
                     (st636, x991)
                   in
                   mtxGet2
                     st636
                     x989
                     x991
                     (match
                        match modelParams102 with ModelParams1 x1373
                        then
                          x1373.embeddedQMatrix
                        else
                          let #var"1130" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 101:54-101:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1363
                      then
                        x1363.mat
                      else
                        let #var"1131" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 101:54-101:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x986
  in
  let getLossRate2 =
    lam st618.
      lam repertoire1.
        lam hostIndex21.
          lam modelParams101.
            match
              p_traverseSeq
                st618
                (lam st619.
                   lam x969.
                     (st619, x969))
                repertoire1
            with
              (st620, x970)
            in
            match p_map st620 get x970 with (st621, x971)
            in
            match
              p_map
                st621 (lam x972.
                   subi x972 1) hostIndex21
            with
              (st622, x973)
            in
            match p_apply st622 x971 x973 with (st623, fromState31)
            in
            match
              p_bind
                st623
                simpleStoreSubmodel
                (simpleInit {})
                (lam st624.
                   lam x974.
                     match eqi x974 2 with true
                     then
                       match fold1 st624 0 repertoire1 with (st625, x975)
                       in
                       p_map
                         st625 (lam x976.
                            eqi x976 1) x975
                     else
                       (st624, p_pure false))
                fromState31
            with
              (st626, x977)
            in
            p_bind
              st626
              simpleStoreSubmodel
              (simpleInit {})
              (lam st627.
                 lam x978.
                   match x978 with true
                   then
                     (st627, p_pure 0.)
                   else match
                     p_map
                       st627
                       (lam x979.
                          addi x979 1)
                       fromState31
                   with
                     (st628, x980)
                   in
                   match
                     p_map
                       st628
                       (lam x981.
                          addi (subi x981 1) 1)
                       fromState31
                   with
                     (st629, x982)
                   in
                   mtxGet2
                     st629
                     x980
                     x982
                     (match
                        match modelParams101 with ModelParams1 x1372
                        then
                          x1372.embeddedQMatrix
                        else
                          let #var"1128" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 101:54-101:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1362
                      then
                        x1362.mat
                      else
                        let #var"1129" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 101:54-101:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x977
  in
  let getLossRate3 =
    lam st608.
      lam repertoire.
        lam hostIndex2.
          lam modelParams10.
            match p_map st608 get repertoire with (st609, x955)
            in
            match
              p_map st609 (lam x956.
                   subi x956 1) hostIndex2
            with
              (st610, x957)
            in
            match p_apply st610 x955 x957 with (st611, fromState3)
            in
            match
              p_bind
                st611
                simpleStoreSubmodel
                (simpleInit {})
                (lam st612.
                   lam x958.
                     match eqi x958 2 with true
                     then
                       match
                         p_map
                           st612
                           (lam x959.
                              match x959 with [ _ ] ++ _
                              then
                                match splitAt x959 1 with {#label"1" = x960}
                                in
                                rec27 (anon11 0 (get x959 0)) x960
                              else match x959 with ""
                              in
                              0)
                           repertoire
                       with
                         (st613, x961)
                       in
                       p_map
                         st613 (lam x962.
                            eqi x962 1) x961
                     else
                       (st612, p_pure false))
                fromState3
            with
              (st614, x963)
            in
            p_bind
              st614
              simpleStoreSubmodel
              (simpleInit {})
              (lam st615.
                 lam x964.
                   match x964 with true
                   then
                     (st615, p_pure 0.)
                   else match
                     p_map
                       st615
                       (lam x965.
                          addi x965 1)
                       fromState3
                   with
                     (st616, x966)
                   in
                   match
                     p_map
                       st616
                       (lam x967.
                          addi (subi x967 1) 1)
                       fromState3
                   with
                     (st617, x968)
                   in
                   mtxGet2
                     st617
                     x966
                     x968
                     (match
                        match modelParams10 with ModelParams1 x1371
                        then
                          x1371.embeddedQMatrix
                        else
                          let #var"1126" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 101:54-101:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1361
                      then
                        x1361.mat
                      else
                        let #var"1127" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 101:54-101:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        p_pure (exit 1)))
              x963
  in
  recursive
    let rec29 =
      lam st79.
        lam c15.
          lam c16.
            lam acc9.
              lam s210.
                match s210 with [ _ ] ++ _
                then
                  let x98 = get s210 0 in
                  match
                    p_bind
                      st79
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st80.
                         lam x99.
                           match eqi x99 2 with true
                           then
                             (st80, acc9)
                           else match
                             p_map
                               st80
                               (lam x100.
                                  lam x101.
                                    addf x100 x101)
                               acc9
                           with
                             (st81, x102)
                           in
                           match getGainRate1 st81 c15 x98 c16 with (st82, x103)
                           in
                           p_apply st82 x102 x103)
                      (get c15 (subi x98 1))
                  with
                    (st83, x104)
                  in
                  match splitAt s210 1 with {#label"1" = x105}
                  in
                  rec29 st83 c15 c16 x104 x105
                else match s210 with ""
                in
                (st79, acc9)
    let rec210 =
      lam st84.
        lam c17.
          lam c18.
            lam acc10.
              lam s211.
                match s211 with [ _ ] ++ _
                then
                  let x106 = get s211 0 in
                  match
                    p_bind
                      st84
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st85.
                         lam x107.
                           match eqi (get x107 (subi x106 1)) 2 with true
                           then
                             (st85, acc10)
                           else match
                             p_map
                               st85
                               (lam x108.
                                  lam x109.
                                    addf x108 x109)
                               acc10
                           with
                             (st86, x110)
                           in
                           match getGainRate st86 x107 x106 c18 with (st87, x111)
                           in
                           p_apply st87 x110 x111)
                      c17
                  with
                    (st88, x112)
                  in
                  match splitAt s211 1 with {#label"1" = x113}
                  in
                  rec210 st88 c17 c18 x112 x113
                else match s211 with ""
                in
                (st84, acc10)
  in
  let anon12 = lam x954.
      addi x954 1 in
  recursive
    let rec32 =
      lam i14.
        lam acc13.
          match geqi i14 0 with true
          then
            rec32 (subi i14 1) (cons (anon12 i14) acc13)
          else
            acc13
  in
  let create11 =
    lam l64.
      let i113 = subi l64 1 in
      match geqi i113 0 with true
      then
        rec32 (subi i113 1) (cons (anon12 i113) "")
      else
        ""
  in
  recursive
    let rec211 =
      lam st89.
        lam c19.
          lam c20.
            lam acc14.
              lam s212.
                match s212 with [ _ ] ++ _
                then
                  let x114 = get s212 0 in
                  match
                    p_bind
                      st89
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st90.
                         lam x115.
                           match eqi x115 0 with true
                           then
                             (st90, acc14)
                           else match
                             p_map
                               st90
                               (lam x116.
                                  lam x117.
                                    addf x116 x117)
                               acc14
                           with
                             (st91, x118)
                           in
                           match getLossRate1 st91 c19 x114 c20 with (st92, x119)
                           in
                           p_apply st92 x118 x119)
                      (get c19 (subi x114 1))
                  with
                    (st93, x120)
                  in
                  match splitAt s212 1 with {#label"1" = x121}
                  in
                  rec211 st93 c19 c20 x120 x121
                else match s212 with ""
                in
                (st89, acc14)
    let rec212 =
      lam st94.
        lam c21.
          lam c22.
            lam acc15.
              lam s213.
                match s213 with [ _ ] ++ _
                then
                  let x122 = get s213 0 in
                  match
                    p_bind
                      st94
                      simpleStoreSubmodel
                      (simpleInit {})
                      (lam st95.
                         lam x123.
                           match eqi (get x123 (subi x122 1)) 0 with true
                           then
                             (st95, acc15)
                           else match
                             p_map
                               st95
                               (lam x124.
                                  lam x125.
                                    addf x124 x125)
                               acc15
                           with
                             (st96, x126)
                           in
                           match getLossRate st96 x123 x122 c22 with (st97, x127)
                           in
                           p_apply st97 x126 x127)
                      c21
                  with
                    (st98, x128)
                  in
                  match splitAt s213 1 with {#label"1" = x129}
                  in
                  rec212 st98 c21 c22 x128 x129
                else match s213 with ""
                in
                (st94, acc15)
  in
  let anon13 = lam x953.
      addi x953 1 in
  recursive
    let rec33 =
      lam i15.
        lam acc16.
          match geqi i15 0 with true
          then
            rec33 (subi i15 1) (cons (anon13 i15) acc16)
          else
            acc16
  in
  let create12 =
    lam l63.
      let i112 = subi l63 1 in
      match geqi i112 0 with true
      then
        rec33 (subi i112 1) (cons (anon13 i112) "")
      else
        ""
  in
  let getTotalRate =
    lam st598.
      lam currRep51.
        lam modelParams81.
          lam nhosts61.
            let s225 = create11 (addi (subi nhosts61 1) 1) in
            match
              match s225 with [ _ ] ++ _
              then
                let x934 = get s225 0 in
                match
                  p_bind
                    st598
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st599.
                       lam x935.
                         match eqi x935 2 with true
                         then
                           (st599, p_pure 0.)
                         else match getGainRate1 st599 currRep51 x934 modelParams81 with (st600, x936)
                         in
                         p_map
                           st600
                           (lam x937.
                              addf 0. x937)
                           x936)
                    (get currRep51 (subi x934 1))
                with
                  (st601, x938)
                in
                match splitAt s225 1 with {#label"1" = x939}
                in
                rec29 st601 currRep51 modelParams81 x938 x939
              else match s225 with ""
              in
              (st598, p_pure 0.)
            with
              (st602, x940)
            in
            match
              p_map
                st602
                (lam x942.
                   lam x943.
                     addf x942 x943)
                x940
            with
              (st603, x944)
            in
            let s226 = create12 (addi (subi nhosts61 1) 1) in
            match
              match s226 with [ _ ] ++ _
              then
                let x945 = get s226 0 in
                match
                  p_bind
                    st603
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st604.
                       lam x946.
                         match eqi x946 0 with true
                         then
                           (st604, p_pure 0.)
                         else match getLossRate1 st604 currRep51 x945 modelParams81 with (st605, x947)
                         in
                         p_map
                           st605
                           (lam x948.
                              addf 0. x948)
                           x947)
                    (get currRep51 (subi x945 1))
                with
                  (st606, x949)
                in
                match splitAt s226 1 with {#label"1" = x950}
                in
                rec211 st606 currRep51 modelParams81 x949 x950
              else match s226 with ""
              in
              (st603, p_pure 0.)
            with
              (st607, x952)
            in
            p_apply st607 x944 x952
  in
  let getTotalRate1 =
    lam st588.
      lam currRep5.
        lam modelParams8.
          lam nhosts6.
            let s223 = create11 (addi (subi nhosts6 1) 1) in
            match
              match s223 with [ _ ] ++ _
              then
                let x917 = get s223 0 in
                match
                  p_bind
                    st588
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st589.
                       lam x918.
                         match eqi (get x918 (subi x917 1)) 2 with true
                         then
                           (st589, p_pure 0.)
                         else match getGainRate st589 x918 x917 modelParams8 with (st590, x919)
                         in
                         p_map
                           st590
                           (lam x920.
                              addf 0. x920)
                           x919)
                    currRep5
                with
                  (st591, x921)
                in
                match splitAt s223 1 with {#label"1" = x922}
                in
                rec210 st591 currRep5 modelParams8 x921 x922
              else match s223 with ""
              in
              (st588, p_pure 0.)
            with
              (st592, x923)
            in
            match
              p_map
                st592
                (lam x924.
                   lam x925.
                     addf x924 x925)
                x923
            with
              (st593, x926)
            in
            let s224 = create12 (addi (subi nhosts6 1) 1) in
            match
              match s224 with [ _ ] ++ _
              then
                let x927 = get s224 0 in
                match
                  p_bind
                    st593
                    simpleStoreSubmodel
                    (simpleInit {})
                    (lam st594.
                       lam x928.
                         match eqi (get x928 (subi x927 1)) 0 with true
                         then
                           (st594, p_pure 0.)
                         else match getLossRate st594 x928 x927 modelParams8 with (st595, x929)
                         in
                         p_map
                           st595
                           (lam x930.
                              addf 0. x930)
                           x929)
                    currRep5
                with
                  (st596, x931)
                in
                match splitAt s224 1 with {#label"1" = x932}
                in
                rec212 st596 currRep5 modelParams8 x931 x932
              else match s224 with ""
              in
              (st593, p_pure 0.)
            with
              (st597, x933)
            in
            p_apply st597 x926 x933
  in
  recursive
    let fullModelWeight =
      lam st99.
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
                                st99
                                (lam x130.
                                   lam x131.
                                     mulf (negf (subf x130 finalAge)) x131)
                                currAge
                            with
                              (st100, x132)
                            in
                            match
                              getTotalRate1 st100 currRep3 modelParams nhosts5
                            with
                              (st101, x133)
                            in
                            p_apply st101 x132 x133
                          else match
                            p_map
                              st99
                              (lam x134.
                                 get x134 (subi nextIndex 1))
                              eventSeq3
                          with
                            (st102, nextEvent)
                          in
                          match
                            p_map
                              st102
                              (lam x135.
                                 match x135 with Event1 x311
                                 then
                                   x311.eventTime
                                 else
                                   let #var"117" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st103, newAge)
                          in
                          match
                            getTotalRate1 st103 currRep3 modelParams nhosts5
                          with
                            (st104, totalLeavingRate1)
                          in
                          match
                            p_map
                              st104
                              (lam x136.
                                 match x136 with Event1 x1341
                                 then
                                   x1341.host
                                 else
                                   let #var"118" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st105, hostIndex1)
                          in
                          match
                            p_map
                              st105
                              (lam x137.
                                 match x137 with Event1 x1321
                                 then
                                   x1321.fromState
                                 else
                                   let #var"119" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:45-84:64>:\nField \'fromState\' not found\n[0m  printLn(paste0([\"From state: \", int2string([31mnextEvent.fromState[0m[0m), \", to state: \", int2string(nextEvent.toState)]));\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st106, x138)
                          in
                          match int2string1 st106 x138 with (st107, x139)
                          in
                          match
                            p_map
                              st107
                              (lam x140.
                                 match x140 with Event1 x1331
                                 then
                                   x1331.toState
                                 else
                                   let #var"120" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:94-84:111>:\nField \'toState\' not found\n[0m  printLn(paste0([\"From state: \", int2string(nextEvent.fromState), \", to state: \", int2string([31mnextEvent.toState[0m[0m)]));\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st108, x141)
                          in
                          match int2string1 st108 x141 with (st109, x142)
                          in
                          match
                            paste01
                              st109
                              [ p_pure "From state: ",
                                x139,
                                p_pure ", to state: ",
                                x142 ]
                          with
                            (st110, x143)
                          in
                          match
                            p_map
                              st110
                              (lam x144.
                                 printError (concat x144 "\n"))
                              x143
                          with
                            (st111, #var"21")
                          in
                          let #var"8" = flushStderr {} in
                          let #var"7" = {} in
                          match
                            p_map
                              st111
                              (lam x145.
                                 lam x146.
                                   lam st112.
                                     match
                                       gti
                                         (match x145 with Event1 x1301
                                          then
                                            x1301.fromState
                                          else
                                            let #var"121" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 85:5-85:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x146
                                     with
                                       true
                                     then
                                       getLossRate3 st112 currRep3 hostIndex1 modelParams
                                     else
                                       getGainRate3 st112 currRep3 hostIndex1 modelParams)
                              nextEvent
                          with
                            (st113, x147)
                          in
                          match
                            p_map
                              st113
                              (lam x148.
                                 match x148 with Event1 x1311
                                 then
                                   x1311.toState
                                 else
                                   let #var"122" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 85:27-85:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st114, x149)
                          in
                          match
                            p_subApply st114 simpleStoreSubmodel (simpleInit {}) x147 x149
                          with
                            (st115, x150)
                          in
                          match p_join st115 x150 with (st116, x151)
                          in
                          match
                            p_map
                              st116
                              (lam x152.
                                 lam x153.
                                   divf x152 x153)
                              x151
                          with
                            (st117, x156)
                          in
                          match p_apply st117 x156 totalLeavingRate1 with (st118, x157)
                          in
                          match log11 st118 x157 with (st119, x158)
                          in
                          match
                            p_map
                              st119
                              (lam x159.
                                 lam x160.
                                   lam x161.
                                     addf (subf x159 x160) x161)
                              x158
                          with
                            (st120, x162)
                          in
                          match
                            p_map
                              st120
                              (lam x163.
                                 lam x164.
                                   lam x165.
                                     mulf (subf x163 x164) x165)
                              currAge
                          with
                            (st121, x166)
                          in
                          match p_apply st121 x166 newAge with (st122, x167)
                          in
                          match p_apply st122 x167 totalLeavingRate1 with (st123, x168)
                          in
                          match p_apply st123 x162 x168 with (st124, x169)
                          in
                          match
                            updateRepertoire1 st124 currRep3 nextEvent nhosts5
                          with
                            (st125, x170)
                          in
                          match
                            fullModelWeight
                              st125
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
                            (st126, x171)
                          in
                          p_apply st126 x169 x171
    let fullModelWeight1 =
      lam st127.
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
                                st127
                                (lam x172.
                                   lam x173.
                                     mulf (negf (subf x172 finalAge1)) x173)
                                currAge1
                            with
                              (st128, x174)
                            in
                            match
                              getTotalRate1 st128 currRep31 modelParams1 nhosts51
                            with
                              (st129, x175)
                            in
                            p_apply st129 x174 x175
                          else match
                            p_map
                              st127
                              (lam x176.
                                 get x176 (subi nextIndex1 1))
                              eventSeq31
                          with
                            (st130, nextEvent1)
                          in
                          match
                            p_map
                              st130
                              (lam x177.
                                 match x177 with Event1 x312
                                 then
                                   x312.eventTime
                                 else
                                   let #var"123" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st131, newAge1)
                          in
                          match
                            getTotalRate1 st131 currRep31 modelParams1 nhosts51
                          with
                            (st132, totalLeavingRate11)
                          in
                          match
                            p_map
                              st132
                              (lam x178.
                                 match x178 with Event1 x1342
                                 then
                                   x1342.host
                                 else
                                   let #var"124" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st133, hostIndex11)
                          in
                          match
                            p_map
                              st133
                              (lam x179.
                                 match x179 with Event1 x1322
                                 then
                                   x1322.fromState
                                 else
                                   let #var"125" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:45-84:64>:\nField \'fromState\' not found\n[0m  printLn(paste0([\"From state: \", int2string([31mnextEvent.fromState[0m[0m), \", to state: \", int2string(nextEvent.toState)]));\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st134, x180)
                          in
                          match int2string1 st134 x180 with (st135, x181)
                          in
                          match
                            p_map
                              st135
                              (lam x182.
                                 match x182 with Event1 x1332
                                 then
                                   x1332.toState
                                 else
                                   let #var"126" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:94-84:111>:\nField \'toState\' not found\n[0m  printLn(paste0([\"From state: \", int2string(nextEvent.fromState), \", to state: \", int2string([31mnextEvent.toState[0m[0m)]));\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st136, x183)
                          in
                          match int2string1 st136 x183 with (st137, x184)
                          in
                          match
                            paste01
                              st137
                              [ p_pure "From state: ",
                                x181,
                                p_pure ", to state: ",
                                x184 ]
                          with
                            (st138, x185)
                          in
                          match
                            p_map
                              st138
                              (lam x186.
                                 printError (concat x186 "\n"))
                              x185
                          with
                            (st139, #var"211")
                          in
                          let #var"81" = flushStderr {} in
                          let #var"71" = {} in
                          match
                            p_map
                              st139
                              (lam x187.
                                 lam x188.
                                   lam st140.
                                     match
                                       gti
                                         (match x187 with Event1 x1302
                                          then
                                            x1302.fromState
                                          else
                                            let #var"127" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 85:5-85:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x188
                                     with
                                       true
                                     then
                                       getLossRate3 st140 currRep31 hostIndex11 modelParams1
                                     else
                                       getGainRate3 st140 currRep31 hostIndex11 modelParams1)
                              nextEvent1
                          with
                            (st141, x189)
                          in
                          match
                            p_map
                              st141
                              (lam x190.
                                 match x190 with Event1 x1312
                                 then
                                   x1312.toState
                                 else
                                   let #var"128" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 85:27-85:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st142, x191)
                          in
                          match
                            p_subApply st142 simpleStoreSubmodel (simpleInit {}) x189 x191
                          with
                            (st143, x192)
                          in
                          match p_join st143 x192 with (st144, x193)
                          in
                          match
                            p_map
                              st144
                              (lam x194.
                                 lam x195.
                                   divf x194 x195)
                              x193
                          with
                            (st145, x196)
                          in
                          match p_apply st145 x196 totalLeavingRate11 with (st146, x197)
                          in
                          match log11 st146 x197 with (st147, x198)
                          in
                          match
                            p_map
                              st147
                              (lam x199.
                                 lam x200.
                                   lam x201.
                                     addf (subf x199 x200) x201)
                              x198
                          with
                            (st148, x202)
                          in
                          match
                            p_map
                              st148
                              (lam x203.
                                 lam x204.
                                   lam x205.
                                     mulf (subf x203 x204) x205)
                              currAge1
                          with
                            (st149, x206)
                          in
                          match p_apply st149 x206 newAge1 with (st150, x207)
                          in
                          match p_apply st150 x207 totalLeavingRate11 with (st151, x208)
                          in
                          match p_apply st151 x202 x208 with (st152, x209)
                          in
                          match
                            updateRepertoire1 st152 currRep31 nextEvent1 nhosts51
                          with
                            (st153, x210)
                          in
                          match
                            fullModelWeight1
                              st153
                              (addi nextIndex1 1)
                              x210
                              finalRep1
                              newAge1
                              finalAge1
                              eventSeq31
                              nEvents31
                              nhosts51
                              modelParams1
                          with
                            (st154, x211)
                          in
                          p_apply st154 x209 x211
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
                      match length13 st155 eventSeq4 with (st156, x212)
                      in
                      p_bind
                        st156
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st157.
                           lam x213.
                             match gti nextIndex11 x213 with true
                             then
                               match
                                 p_traverseSeq
                                   st157
                                   (lam st158.
                                      lam x214.
                                        (st158, x214))
                                   (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x321
                                    then
                                      x321.totalRates
                                    else
                                      let #var"129" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x215.
                                           p_pure x215)
                                        (exit 1))
                               with
                                 (st159, x216)
                               in
                               match
                                 p_map
                                   st159
                                   (lam x217.
                                      lam x218.
                                        mulf (negf (subf currAge11 finalAge11)) (get x217 x218))
                                   x216
                               with
                                 (st160, x219)
                               in
                               match
                                 p_map
                                   st160
                                   (lam x220.
                                      subi (addi x220 1) 1)
                                   currState
                               with
                                 (st161, x222)
                               in
                               p_apply st161 x219 x222
                             else match
                               p_map
                                 st157
                                 (lam x223.
                                    get x223 (subi nextIndex11 1))
                                 eventSeq4
                             with
                               (st162, nextEvent11)
                             in
                             match
                               p_map
                                 st162
                                 (lam x224.
                                    match x224 with Event1 x361
                                    then
                                      x361.toState
                                    else
                                      let #var"130" =
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
                                 (lam x225.
                                    match x225 with Event1 x351
                                    then
                                      x351.eventTime
                                    else
                                      let #var"131" =
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
                                    lam x226.
                                      p_traverseSeq
                                        st165
                                        (lam st166.
                                           lam x227.
                                             (st166, x227))
                                        x226)
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x331
                                  then
                                    x331.transitionProbs
                                  else
                                    let #var"132" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x228.
                                         map
                                           (lam x229.
                                              p_pure x229)
                                           x228)
                                      (exit 1))
                             with
                               (st167, x230)
                             in
                             match
                               p_map
                                 st167
                                 (lam x232.
                                    lam x233.
                                      get (get x232 x233))
                                 x230
                             with
                               (st168, x234)
                             in
                             match
                               p_map
                                 st168
                                 (lam x235.
                                    subi (addi x235 1) 1)
                                 currState
                             with
                               (st169, x236)
                             in
                             match p_apply st169 x234 x236 with (st170, x237)
                             in
                             match
                               p_map
                                 st170
                                 (lam x238.
                                    subi (addi x238 1) 1)
                                 nextState
                             with
                               (st171, x239)
                             in
                             match p_apply st171 x237 x239 with (st172, x240)
                             in
                             match log11 st172 x240 with (st173, x241)
                             in
                             match
                               p_map
                                 st173
                                 (lam x242.
                                    lam x243.
                                      lam x244.
                                        addf (subf x242 x243) x244)
                                 x241
                             with
                               (st174, x245)
                             in
                             match
                               p_map
                                 st174
                                 (lam x246.
                                    lam x247.
                                      mulf (subf currAge11 x246) x247)
                                 nextAge
                             with
                               (st175, x248)
                             in
                             match
                               p_traverseSeq
                                 st175
                                 (lam st176.
                                    lam x249.
                                      (st176, x249))
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x341
                                  then
                                    x341.totalRates
                                  else
                                    let #var"133" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x250.
                                         p_pure x250)
                                      (exit 1))
                             with
                               (st177, x251)
                             in
                             match p_map st177 get x251 with (st178, x252)
                             in
                             match
                               p_map
                                 st178
                                 (lam x253.
                                    subi (addi x253 1) 1)
                                 currState
                             with
                               (st179, x254)
                             in
                             match p_apply st179 x252 x254 with (st180, x255)
                             in
                             match p_apply st180 x248 x255 with (st181, x256)
                             in
                             match p_apply st181 x245 x256 with (st182, x257)
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
                               (st183, x258)
                             in
                             p_apply st183 x257 x258)
                        x212
    let hostIndepLikelihood1 =
      lam st184.
        lam nextIndex12.
          lam currState1.
            lam finalState1.
              lam currAge12.
                lam finalAge12.
                  lam eventSeq41.
                    lam embeddedQMatrix1.
                      match length13 st184 eventSeq41 with (st185, x259)
                      in
                      p_bind
                        st185
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st186.
                           lam x260.
                             match gti nextIndex12 x260 with true
                             then
                               match
                                 p_map
                                   st186
                                   (lam x261.
                                      lam x262.
                                        mulf (negf (subf x261 finalAge12)) x262)
                                   currAge12
                               with
                                 (st187, x263)
                               in
                               match
                                 p_traverseSeq
                                   st187
                                   (lam st188.
                                      lam x264.
                                        (st188, x264))
                                   (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x322
                                    then
                                      x322.totalRates
                                    else
                                      let #var"134" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x265.
                                           p_pure x265)
                                        (exit 1))
                               with
                                 (st189, x266)
                               in
                               match p_map st189 get x266 with (st190, x267)
                               in
                               match
                                 p_map
                                   st190
                                   (lam x268.
                                      subi (addi x268 1) 1)
                                   currState1
                               with
                                 (st191, x269)
                               in
                               match p_apply st191 x267 x269 with (st192, x270)
                               in
                               p_apply st192 x263 x270
                             else match
                               p_map
                                 st186
                                 (lam x271.
                                    get x271 (subi nextIndex12 1))
                                 eventSeq41
                             with
                               (st193, nextEvent12)
                             in
                             match
                               p_map
                                 st193
                                 (lam x272.
                                    match x272 with Event1 x362
                                    then
                                      x362.toState
                                    else
                                      let #var"135" =
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
                                 (lam x273.
                                    match x273 with Event1 x352
                                    then
                                      x352.eventTime
                                    else
                                      let #var"136" =
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
                                    lam x274.
                                      p_traverseSeq
                                        st196
                                        (lam st197.
                                           lam x275.
                                             (st197, x275))
                                        x274)
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x332
                                  then
                                    x332.transitionProbs
                                  else
                                    let #var"137" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x276.
                                         map
                                           (lam x277.
                                              p_pure x277)
                                           x276)
                                      (exit 1))
                             with
                               (st198, x278)
                             in
                             match
                               p_map
                                 st198
                                 (lam x279.
                                    lam x280.
                                      get (get x279 x280))
                                 x278
                             with
                               (st199, x281)
                             in
                             match
                               p_map
                                 st199
                                 (lam x282.
                                    subi (addi x282 1) 1)
                                 currState1
                             with
                               (st200, x283)
                             in
                             match p_apply st200 x281 x283 with (st201, x284)
                             in
                             match
                               p_map
                                 st201
                                 (lam x285.
                                    subi (addi x285 1) 1)
                                 nextState1
                             with
                               (st202, x286)
                             in
                             match p_apply st202 x284 x286 with (st203, x287)
                             in
                             match log11 st203 x287 with (st204, x288)
                             in
                             match
                               p_map
                                 st204
                                 (lam x289.
                                    lam x290.
                                      lam x291.
                                        addf (subf x289 x290) x291)
                                 x288
                             with
                               (st205, x292)
                             in
                             match
                               p_map
                                 st205
                                 (lam x293.
                                    lam x294.
                                      lam x295.
                                        mulf (subf x293 x294) x295)
                                 currAge12
                             with
                               (st206, x296)
                             in
                             match p_apply st206 x296 nextAge1 with (st207, x297)
                             in
                             match
                               p_traverseSeq
                                 st207
                                 (lam st208.
                                    lam x298.
                                      (st208, x298))
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x342
                                  then
                                    x342.totalRates
                                  else
                                    let #var"138" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x299.
                                         p_pure x299)
                                      (exit 1))
                             with
                               (st209, x300)
                             in
                             match p_map st209 get x300 with (st210, x303)
                             in
                             match
                               p_map
                                 st210
                                 (lam x304.
                                    subi (addi x304 1) 1)
                                 currState1
                             with
                               (st211, x305)
                             in
                             match p_apply st211 x303 x305 with (st212, x306)
                             in
                             match p_apply st212 x297 x306 with (st213, x307)
                             in
                             match p_apply st213 x292 x307 with (st214, x308)
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
                               (st215, x309)
                             in
                             p_apply st215 x308 x309)
                        x259
    let hostIndepLikelihood2 =
      lam st216.
        lam nextIndex13.
          lam currState2.
            lam finalState2.
              lam currAge13.
                lam finalAge13.
                  lam eventSeq42.
                    lam embeddedQMatrix2.
                      match length13 st216 eventSeq42 with (st217, x310)
                      in
                      p_bind
                        st217
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st218.
                           lam x313.
                             match gti nextIndex13 x313 with true
                             then
                               match
                                 p_traverseSeq
                                   st218
                                   (lam st219.
                                      lam x314.
                                        (st219, x314))
                                   (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x323
                                    then
                                      x323.totalRates
                                    else
                                      let #var"139" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x315.
                                           p_pure x315)
                                        (exit 1))
                               with
                                 (st220, x316)
                               in
                               match
                                 p_map
                                   st220
                                   (lam x317.
                                      lam x318.
                                        mulf (negf (subf currAge13 finalAge13)) (get x317 x318))
                                   x316
                               with
                                 (st221, x319)
                               in
                               match
                                 p_map
                                   st221
                                   (lam x320.
                                      subi (addi x320 1) 1)
                                   currState2
                               with
                                 (st222, x324)
                               in
                               p_apply st222 x319 x324
                             else match
                               p_map
                                 st218
                                 (lam x325.
                                    get x325 (subi nextIndex13 1))
                                 eventSeq42
                             with
                               (st223, nextEvent13)
                             in
                             match
                               p_map
                                 st223
                                 (lam x326.
                                    match x326 with Event1 x363
                                    then
                                      x363.toState
                                    else
                                      let #var"140" =
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
                                 (lam x327.
                                    match x327 with Event1 x353
                                    then
                                      x353.eventTime
                                    else
                                      let #var"141" =
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
                                    lam x328.
                                      p_traverseSeq
                                        st226
                                        (lam st227.
                                           lam x329.
                                             (st227, x329))
                                        x328)
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x333
                                  then
                                    x333.transitionProbs
                                  else
                                    let #var"142" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x330.
                                         map
                                           (lam x334.
                                              p_pure x334)
                                           x330)
                                      (exit 1))
                             with
                               (st228, x335)
                             in
                             match
                               p_map
                                 st228
                                 (lam x336.
                                    lam x337.
                                      get (get x336 x337))
                                 x335
                             with
                               (st229, x338)
                             in
                             match
                               p_map
                                 st229
                                 (lam x339.
                                    subi (addi x339 1) 1)
                                 currState2
                             with
                               (st230, x340)
                             in
                             match p_apply st230 x338 x340 with (st231, x343)
                             in
                             match
                               p_map
                                 st231
                                 (lam x344.
                                    subi (addi x344 1) 1)
                                 nextState2
                             with
                               (st232, x345)
                             in
                             match p_apply st232 x343 x345 with (st233, x346)
                             in
                             match log11 st233 x346 with (st234, x347)
                             in
                             match
                               p_map
                                 st234
                                 (lam x348.
                                    lam x349.
                                      lam x350.
                                        addf (subf x348 x349) x350)
                                 x347
                             with
                               (st235, x354)
                             in
                             match
                               p_map
                                 st235
                                 (lam x355.
                                    lam x356.
                                      mulf (subf currAge13 x355) x356)
                                 nextAge2
                             with
                               (st236, x357)
                             in
                             match
                               p_traverseSeq
                                 st236
                                 (lam st237.
                                    lam x358.
                                      (st237, x358))
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x3410
                                  then
                                    x3410.totalRates
                                  else
                                    let #var"143" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x359.
                                         p_pure x359)
                                      (exit 1))
                             with
                               (st238, x360)
                             in
                             match p_map st238 get x360 with (st239, x364)
                             in
                             match
                               p_map
                                 st239
                                 (lam x365.
                                    subi (addi x365 1) 1)
                                 currState2
                             with
                               (st240, x366)
                             in
                             match p_apply st240 x364 x366 with (st241, x367)
                             in
                             match p_apply st241 x357 x367 with (st242, x368)
                             in
                             match p_apply st242 x354 x368 with (st243, x369)
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
                               (st244, x370)
                             in
                             p_apply st244 x369 x370)
                        x310
    let hostIndepLikelihood3 =
      lam st245.
        lam nextIndex14.
          lam currState3.
            lam finalState3.
              lam currAge14.
                lam finalAge14.
                  lam eventSeq43.
                    lam embeddedQMatrix3.
                      match length13 st245 eventSeq43 with (st246, x371)
                      in
                      p_bind
                        st246
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st247.
                           lam x372.
                             match gti nextIndex14 x372 with true
                             then
                               match
                                 p_map
                                   st247
                                   (lam x373.
                                      lam x374.
                                        mulf (negf (subf x373 finalAge14)) x374)
                                   currAge14
                               with
                                 (st248, x375)
                               in
                               match
                                 p_traverseSeq
                                   st248
                                   (lam st249.
                                      lam x376.
                                        (st249, x376))
                                   (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3210
                                    then
                                      x3210.totalRates
                                    else
                                      let #var"144" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x377.
                                           p_pure x377)
                                        (exit 1))
                               with
                                 (st250, x378)
                               in
                               match p_map st250 get x378 with (st251, x379)
                               in
                               match
                                 p_map
                                   st251
                                   (lam x380.
                                      subi (addi x380 1) 1)
                                   currState3
                               with
                                 (st252, x381)
                               in
                               match p_apply st252 x379 x381 with (st253, x382)
                               in
                               p_apply st253 x375 x382
                             else match
                               p_map
                                 st247
                                 (lam x383.
                                    get x383 (subi nextIndex14 1))
                                 eventSeq43
                             with
                               (st254, nextEvent14)
                             in
                             match
                               p_map
                                 st254
                                 (lam x384.
                                    match x384 with Event1 x3610
                                    then
                                      x3610.toState
                                    else
                                      let #var"145" =
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
                                 (lam x385.
                                    match x385 with Event1 x3510
                                    then
                                      x3510.eventTime
                                    else
                                      let #var"146" =
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
                                    lam x386.
                                      p_traverseSeq
                                        st257
                                        (lam st258.
                                           lam x387.
                                             (st258, x387))
                                        x386)
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3310
                                  then
                                    x3310.transitionProbs
                                  else
                                    let #var"147" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x388.
                                         map
                                           (lam x389.
                                              p_pure x389)
                                           x388)
                                      (exit 1))
                             with
                               (st259, x390)
                             in
                             match
                               p_map
                                 st259
                                 (lam x391.
                                    lam x392.
                                      get (get x391 x392))
                                 x390
                             with
                               (st260, x393)
                             in
                             match
                               p_map
                                 st260
                                 (lam x394.
                                    subi (addi x394 1) 1)
                                 currState3
                             with
                               (st261, x395)
                             in
                             match p_apply st261 x393 x395 with (st262, x396)
                             in
                             match
                               p_map
                                 st262
                                 (lam x397.
                                    subi (addi x397 1) 1)
                                 nextState3
                             with
                               (st263, x398)
                             in
                             match p_apply st263 x396 x398 with (st264, x399)
                             in
                             match log11 st264 x399 with (st265, x400)
                             in
                             match
                               p_map
                                 st265
                                 (lam x401.
                                    lam x402.
                                      lam x403.
                                        addf (subf x401 x402) x403)
                                 x400
                             with
                               (st266, x404)
                             in
                             match
                               p_map
                                 st266
                                 (lam x405.
                                    lam x406.
                                      lam x407.
                                        mulf (subf x405 x406) x407)
                                 currAge14
                             with
                               (st267, x408)
                             in
                             match p_apply st267 x408 nextAge3 with (st268, x409)
                             in
                             match
                               p_traverseSeq
                                 st268
                                 (lam st269.
                                    lam x410.
                                      (st269, x410))
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3411
                                  then
                                    x3411.totalRates
                                  else
                                    let #var"148" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x411.
                                         p_pure x411)
                                      (exit 1))
                             with
                               (st270, x412)
                             in
                             match p_map st270 get x412 with (st271, x413)
                             in
                             match
                               p_map
                                 st271
                                 (lam x414.
                                    subi (addi x414 1) 1)
                                 currState3
                             with
                               (st272, x415)
                             in
                             match p_apply st272 x413 x415 with (st273, x416)
                             in
                             match p_apply st273 x409 x416 with (st274, x417)
                             in
                             match p_apply st274 x404 x417 with (st275, x418)
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
                               (st276, x419)
                             in
                             p_apply st276 x418 x419)
                        x371
  in
  let anon14 = lam x916.
      addi x916 1 in
  recursive
    let rec34 =
      lam i16.
        lam acc17.
          match geqi i16 0 with true
          then
            rec34 (subi i16 1) (cons (anon14 i16) acc17)
          else
            acc17
  in
  let anon15 =
    lam st583.
      lam msg1.
        lam x909.
          match mtx3ToSeq st583 msg1 x909 with (st584, x910)
          in
          match
            p_traverseSeq
              st584
              (lam st585.
                 lam x912.
                   (st585, x912))
              x910
          with
            (st586, x913)
          in
          match
            p_map st586 (lam x914.
                 mkCategorical x914) x913
          with
            (st587, x915)
          in
          p_assume st587 simpleStoreAssume x915
  in
  recursive
    let rec8 =
      lam st277.
        lam c23.
          lam s8.
            match s8 with [ _,
                _ ] ++ _
            then
              match anon15 st277 c23 (get s8 0) with (st278, x420)
              in
              match splitAt s8 1 with {#label"1" = x421}
              in
              match rec8 st278 c23 x421 with (st279, x422)
              in
              (st279, cons x420 x422)
            else match s8 with [ e10 ]
            then
              match splitAt s8 1 with {#label"1" = x423}
              in
              let slice9 = x423 in
              match anon15 st277 c23 e10 with (st280, x424)
              in
              (st280, [ x424 ])
            else match s8 with ""
            in
            (st277, "")
  in
  let suggestNodeRep =
    lam st582.
      lam msg.
        lam nHosts4.
          lam nodeLabel5.
            let i111 = subi (addi (subi nHosts4 1) 1) 1 in
            rec8
              st582
              msg
              (match geqi i111 0 with true
               then
                 rec34 (subi i111 1) (cons (anon14 i111) "")
               else
                 "")
  in
  recursive
    let sampleHostHistoryRec =
      lam st281.
        lam currentState.
          lam finalState11.
            lam currentAge.
              lam finalAge2.
                lam host.
                  lam nodeLabel.
                    lam embeddedQMatrix11.
                      p_bind
                        st281
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st282.
                           lam x425.
                             match ltf x425 finalAge2 with true
                             then
                               p_map
                                 st282
                                 (lam x426.
                                    match eqi x426 finalState11 with true
                                    then
                                      Bridge1
                                        { success = true, events = "" }
                                    else
                                      Bridge1
                                        { success = false, events = "" })
                                 currentState
                             else match
                               p_traverseSeq
                                 st282
                                 (lam st283.
                                    lam x427.
                                      p_traverseSeq
                                        st283
                                        (lam st284.
                                           lam x428.
                                             (st284, x428))
                                        x427)
                                 (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x4010
                                  then
                                    x4010.transitionProbs
                                  else
                                    let #var"149" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 335:16-335:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                    in
                                    map
                                      (lam x429.
                                         map
                                           (lam x430.
                                              p_pure x430)
                                           x429)
                                      (exit 1))
                             with
                               (st285, x431)
                             in
                             match
                               p_map
                                 st285
                                 (lam x432.
                                    lam x433.
                                      mkCategorical (get x432 x433))
                                 x431
                             with
                               (st286, x434)
                             in
                             match
                               p_map
                                 st286
                                 (lam x435.
                                    subi (addi x435 1) 1)
                                 currentState
                             with
                               (st287, x436)
                             in
                             match p_apply st287 x434 x436 with (st288, x437)
                             in
                             match p_assume st288 simpleStoreAssume x437 with (st289, nextState11)
                             in
                             match
                               p_traverseSeq
                                 st289
                                 (lam st290.
                                    lam x438.
                                      (st290, x438))
                                 (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x3910
                                  then
                                    x3910.totalRates
                                  else
                                    let #var"150" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 339:20-339:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                    in
                                    map
                                      (lam x439.
                                         p_pure x439)
                                      (exit 1))
                             with
                               (st291, x440)
                             in
                             match
                               p_map
                                 st291
                                 (lam x441.
                                    lam x442.
                                      mkExponential
                                        (addf
                                           (addf (get x441 x442) (mulf (int2float host) 0.))
                                           (mulf (int2float nodeLabel) 0.)))
                                 x440
                             with
                               (st292, x443)
                             in
                             match
                               p_map
                                 st292
                                 (lam x444.
                                    subi (addi x444 1) 1)
                                 nextState11
                             with
                               (st293, x445)
                             in
                             match p_apply st293 x443 x445 with (st294, x446)
                             in
                             match p_assume st294 simpleStoreAssume x446 with (st295, x447)
                             in
                             match
                               p_map
                                 st295
                                 (lam x448.
                                    subf x425 x448)
                                 x447
                             with
                               (st296, x449)
                             in
                             match
                               sampleHostHistoryRec
                                 st296
                                 nextState11
                                 finalState11
                                 x449
                                 finalAge2
                                 host
                                 nodeLabel
                                 embeddedQMatrix11
                             with
                               (st297, restOfHistory)
                             in
                             match
                               p_map
                                 st297
                                 (lam x450.
                                    lam x451.
                                      Bridge1
                                        { success =
                                            match x450 with Bridge1 x3710
                                            then
                                              x3710.success
                                            else
                                              let #var"151" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 357:18-357:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                              in
                                              exit 1,
                                          events = x451 })
                                 restOfHistory
                             with
                               (st298, x452)
                             in
                             match
                               p_map
                                 st298
                                 (lam x453.
                                    match x453 with Bridge1 x3810
                                    then
                                      x3810.events
                                    else
                                      let #var"152" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 355:10-355:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                      in
                                      exit 1)
                                 restOfHistory
                             with
                               (st299, x454)
                             in
                             match
                               cons11
                                 st299
                                 (Event1
                                    { host = host,
                                      toState = nextState11,
                                      eventTime = x425,
                                      fromState = currentState })
                                 x454
                             with
                               (st300, x455)
                             in
                             p_apply st300 x452 x455)
                        currentAge
    let sampleHostHistoryRec1 =
      lam st301.
        lam currentState1.
          lam finalState12.
            lam currentAge1.
              lam finalAge21.
                lam host1.
                  lam nodeLabel1.
                    lam embeddedQMatrix12.
                      p_bind
                        st301
                        simpleStoreSubmodel
                        (simpleInit {})
                        (lam st302.
                           lam x456.
                             match ltf x456 finalAge21 with true
                             then
                               match
                                 p_map
                                   st302
                                   (lam x457.
                                      lam x458.
                                        match eqi x457 x458 with true
                                        then
                                          Bridge1
                                            { success = true, events = "" }
                                        else
                                          Bridge1
                                            { success = false, events = "" })
                                   currentState1
                               with
                                 (st303, x459)
                               in
                               p_apply st303 x459 finalState12
                             else match
                               p_traverseSeq
                                 st302
                                 (lam st304.
                                    lam x460.
                                      p_traverseSeq
                                        st304
                                        (lam st305.
                                           lam x461.
                                             (st305, x461))
                                        x460)
                                 (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x4011
                                  then
                                    x4011.transitionProbs
                                  else
                                    let #var"153" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 335:16-335:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                    in
                                    map
                                      (lam x462.
                                         map
                                           (lam x463.
                                              p_pure x463)
                                           x462)
                                      (exit 1))
                             with
                               (st306, x464)
                             in
                             match
                               p_map
                                 st306
                                 (lam x465.
                                    lam x466.
                                      mkCategorical (get x465 x466))
                                 x464
                             with
                               (st307, x467)
                             in
                             match
                               p_map
                                 st307
                                 (lam x468.
                                    subi (addi x468 1) 1)
                                 currentState1
                             with
                               (st308, x469)
                             in
                             match p_apply st308 x467 x469 with (st309, x470)
                             in
                             match p_assume st309 simpleStoreAssume x470 with (st310, nextState12)
                             in
                             match
                               p_traverseSeq
                                 st310
                                 (lam st311.
                                    lam x471.
                                      (st311, x471))
                                 (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x3911
                                  then
                                    x3911.totalRates
                                  else
                                    let #var"154" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 339:20-339:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                    in
                                    map
                                      (lam x472.
                                         p_pure x472)
                                      (exit 1))
                             with
                               (st312, x473)
                             in
                             match
                               p_map
                                 st312
                                 (lam x474.
                                    lam x475.
                                      mkExponential
                                        (addf
                                           (addf (get x474 x475) (mulf (int2float host1) 0.))
                                           (mulf (int2float nodeLabel1) 0.)))
                                 x473
                             with
                               (st313, x476)
                             in
                             match
                               p_map
                                 st313
                                 (lam x477.
                                    subi (addi x477 1) 1)
                                 nextState12
                             with
                               (st314, x478)
                             in
                             match p_apply st314 x476 x478 with (st315, x479)
                             in
                             match p_assume st315 simpleStoreAssume x479 with (st316, x480)
                             in
                             match
                               p_map
                                 st316
                                 (lam x481.
                                    subf x456 x481)
                                 x480
                             with
                               (st317, x482)
                             in
                             match
                               sampleHostHistoryRec1
                                 st317
                                 nextState12
                                 finalState12
                                 x482
                                 finalAge21
                                 host1
                                 nodeLabel1
                                 embeddedQMatrix12
                             with
                               (st318, restOfHistory1)
                             in
                             match
                               p_map
                                 st318
                                 (lam x483.
                                    lam x484.
                                      Bridge1
                                        { success =
                                            match x483 with Bridge1 x3711
                                            then
                                              x3711.success
                                            else
                                              let #var"155" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 357:18-357:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                              in
                                              exit 1,
                                          events = x484 })
                                 restOfHistory1
                             with
                               (st319, x485)
                             in
                             match
                               p_map
                                 st319
                                 (lam x486.
                                    match x486 with Bridge1 x3811
                                    then
                                      x3811.events
                                    else
                                      let #var"156" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 355:10-355:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                      in
                                      exit 1)
                                 restOfHistory1
                             with
                               (st320, x487)
                             in
                             match
                               cons11
                                 st320
                                 (Event1
                                    { host = host1,
                                      toState = nextState12,
                                      eventTime = x456,
                                      fromState = currentState1 })
                                 x487
                             with
                               (st321, x488)
                             in
                             p_apply st321 x485 x488)
                        currentAge1
  in
  let anon16 = lam x908.
      addi x908 1 in
  recursive
    let rec35 =
      lam i17.
        lam acc18.
          match geqi i17 0 with true
          then
            rec35 (subi i17 1) (cons (anon16 i17) acc18)
          else
            acc18
  in
  let create13 =
    lam l62.
      let i110 = subi l62 1 in
      match geqi i110 0 with true
      then
        rec35 (subi i110 1) (cons (anon16 i110) "")
      else
        ""
  in
  let anon17 =
    lam st570.
      lam startRep1.
        lam finalRep12.
          lam startAge1.
            lam finalAge33.
              lam nodeLabel12.
                lam modelParams31.
                  lam x888.
                    let startState1 = get startRep1 (subi x888 1) in
                    let embeddedQMatrix51 =
                      match modelParams31 with ModelParams1 x1042
                      then
                        x1042.embeddedQMatrix
                      else
                        let #var"1125" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 207:4-207:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st570
                        (lam st571.
                           lam x889.
                             (st571, x889))
                        (match embeddedQMatrix51 with EmbeddedMarkovChainMatrix1 x1082
                         then
                           x1082.totalRates
                         else
                           let #var"1122" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 298:18-298:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x890.
                                p_pure x890)
                             (exit 1))
                    with
                      (st572, x892)
                    in
                    match
                      p_map
                        st572
                        (lam x893.
                           lam x894.
                             mkExponential
                               (addf
                                  (addf (get x893 x894) (mulf (int2float x888) 0.))
                                  (mulf (int2float nodeLabel12) 0.)))
                        x892
                    with
                      (st573, x895)
                    in
                    match
                      p_map
                        st573
                        (lam x896.
                           subi (addi x896 1) 1)
                        startState1
                    with
                      (st574, x897)
                    in
                    match p_apply st574 x895 x897 with (st575, x898)
                    in
                    match p_assume st575 simpleStoreAssume x898 with (st576, x899)
                    in
                    match
                      p_map
                        st576
                        (lam x900.
                           subf startAge1 x900)
                        x899
                    with
                      (st577, x902)
                    in
                    match
                      sampleHostHistoryRec
                        st577
                        startState1
                        (get finalRep12 (subi x888 1))
                        x902
                        finalAge33
                        x888
                        nodeLabel12
                        embeddedQMatrix51
                    with
                      (st578, bridge1)
                    in
                    match
                      p_map
                        st578
                        (lam x903.
                           match x903 with Bridge1 x1072
                           then
                             x1072.success
                           else
                             let #var"1123" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 310:19-310:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge1
                    with
                      (st579, x904)
                    in
                    match bool2real st579 x904 with (st580, x905)
                    in
                    let st581 =
                      p_weight
                        st580
                        simpleStoreWeight
                        (lam x907.
                           externalLog
                             (addf
                                (addf x907 (mulf (int2float x888) 0.))
                                (mulf (int2float nodeLabel12) 0.)))
                        x905
                    in
                    let foo51 = {} in
                    p_map
                      st581
                      (lam x906.
                         match x906 with Bridge1 x1062
                         then
                           x1062.events
                         else
                           let #var"1124" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 311:9-311:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge1
  in
  let anon18 =
    lam st558.
      lam startRep.
        lam finalRep11.
          lam startAge.
            lam finalAge32.
              lam nodeLabel11.
                lam modelParams3.
                  lam x869.
                    let startState = get startRep (subi x869 1) in
                    let embeddedQMatrix5 =
                      match modelParams3 with ModelParams1 x1041
                      then
                        x1041.embeddedQMatrix
                      else
                        let #var"1121" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 207:4-207:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st558
                        (lam st559.
                           lam x870.
                             (st559, x870))
                        (match embeddedQMatrix5 with EmbeddedMarkovChainMatrix1 x1081
                         then
                           x1081.totalRates
                         else
                           let #var"1118" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 298:18-298:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x871.
                                p_pure x871)
                             (exit 1))
                    with
                      (st560, x872)
                    in
                    match
                      p_map
                        st560
                        (lam x873.
                           lam x874.
                             mkExponential
                               (addf
                                  (addf (get x873 x874) (mulf (int2float x869) 0.))
                                  (mulf (int2float nodeLabel11) 0.)))
                        x872
                    with
                      (st561, x875)
                    in
                    match
                      p_map
                        st561
                        (lam x876.
                           subi (addi x876 1) 1)
                        startState
                    with
                      (st562, x877)
                    in
                    match p_apply st562 x875 x877 with (st563, x878)
                    in
                    match p_assume st563 simpleStoreAssume x878 with (st564, x879)
                    in
                    match
                      p_map
                        st564
                        (lam x880.
                           subf startAge x880)
                        x879
                    with
                      (st565, x882)
                    in
                    match
                      sampleHostHistoryRec1
                        st565
                        startState
                        (get finalRep11 (subi x869 1))
                        x882
                        finalAge32
                        x869
                        nodeLabel11
                        embeddedQMatrix5
                    with
                      (st566, bridge)
                    in
                    match
                      p_map
                        st566
                        (lam x883.
                           match x883 with Bridge1 x1071
                           then
                             x1071.success
                           else
                             let #var"1119" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 310:19-310:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge
                    with
                      (st567, x884)
                    in
                    match bool2real st567 x884 with (st568, x885)
                    in
                    let st569 =
                      p_weight
                        st568
                        simpleStoreWeight
                        (lam x887.
                           externalLog
                             (addf
                                (addf x887 (mulf (int2float x869) 0.))
                                (mulf (int2float nodeLabel11) 0.)))
                        x885
                    in
                    let foo5 = {} in
                    p_map
                      st569
                      (lam x886.
                         match x886 with Bridge1 x1061
                         then
                           x1061.events
                         else
                           let #var"1120" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 311:9-311:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge
  in
  recursive
    let rec9 =
      lam st322.
        lam c24.
          lam c25.
            lam c26.
              lam c27.
                lam c28.
                  lam c29.
                    lam s9.
                      match s9 with [ _,
                          _ ] ++ _
                      then
                        match anon17 st322 c24 c25 c26 c27 c28 c29 (get s9 0) with (st323, x489)
                        in
                        match splitAt s9 1 with {#label"1" = x490}
                        in
                        match rec9 st323 c24 c25 c26 c27 c28 c29 x490 with (st324, x491)
                        in
                        (st324, cons x489 x491)
                      else match s9 with [ e11 ]
                      then
                        match splitAt s9 1 with {#label"1" = x492}
                        in
                        let slice10 = x492 in
                        match anon17 st322 c24 c25 c26 c27 c28 c29 e11 with (st325, x493)
                        in
                        (st325, [ x493 ])
                      else match s9 with ""
                      in
                      (st322, "")
    let rec10 =
      lam st326.
        lam c30.
          lam c31.
            lam c32.
              lam c33.
                lam c34.
                  lam c35.
                    lam s10.
                      match s10 with [ _,
                          _ ] ++ _
                      then
                        match
                          anon18 st326 c30 c31 c32 c33 c34 c35 (get s10 0)
                        with
                          (st327, x494)
                        in
                        match splitAt s10 1 with {#label"1" = x495}
                        in
                        match rec10 st327 c30 c31 c32 c33 c34 c35 x495 with (st328, x496)
                        in
                        (st328, cons x494 x496)
                      else match s10 with [ e12 ]
                      then
                        match splitAt s10 1 with {#label"1" = x497}
                        in
                        let slice11 = x497 in
                        match anon18 st326 c30 c31 c32 c33 c34 c35 e12 with (st329, x498)
                        in
                        (st329, [ x498 ])
                      else match s10 with ""
                      in
                      (st326, "")
  in
  let anon19 =
    lam h2.
      lam x868.
        lti
          (match
             isNaN1
               (match h2 with Event1 x1091
                then
                  x1091.eventTime
                else
                  let #var"1114" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 247:12-247:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             negi 1
           else match
             isNaN1
               (match x868 with Event1 x1131
                then
                  x1131.eventTime
                else
                  let #var"1115" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 250:12-250:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
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
                  let #var"1116" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 253:6-253:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
                  in
                  exit 1)
               (match x868 with Event1 x1151
                then
                  x1151.eventTime
                else
                  let #var"1117" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 253:25-253:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
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
      lam c36.
        lam l.
          lam r.
            lam seq1.
              match seq1 with [ _ ] ++ _
              then
                let s41 = get seq1 0 in
                match splitAt seq1 1 with {#label"1" = x499}
                in
                let seq2 = x499 in
                match anon19 c36 s41 with true
                then
                  work11 c36 (cons s41 l) r seq2
                else
                  work11 c36 l (cons s41 r) seq2
              else match seq1 with ""
              in
              (l, r)
    let work12 =
      lam c37.
        lam l1.
          lam r1.
            lam seq11.
              match seq11 with [ _ ] ++ _
              then
                let s42 = get seq11 0 in
                match splitAt seq11 1 with {#label"1" = x500}
                in
                let seq21 = x500 in
                match anon19 c37 s42 with true
                then
                  work12 c37 (cons s42 l1) r1 seq21
                else
                  work11 c37 l1 (cons s42 r1) seq21
              else match seq11 with ""
              in
              (l1, r1)
    let work13 =
      lam c38.
        lam l2.
          lam r2.
            lam seq12.
              match seq12 with [ _ ] ++ _
              then
                let s43 = get seq12 0 in
                match splitAt seq12 1 with {#label"1" = x501}
                in
                let seq22 = x501 in
                match anon19 c38 s43 with true
                then
                  work11 c38 (cons s43 l2) r2 seq22
                else
                  work13 c38 l2 (cons s43 r2) seq22
              else match seq12 with ""
              in
              (l2, r2)
    let work14 =
      lam c39.
        lam l3.
          lam r3.
            lam seq13.
              match seq13 with [ _ ] ++ _
              then
                let s44 = get seq13 0 in
                match splitAt seq13 1 with {#label"1" = x502}
                in
                let seq23 = x502 in
                match anon19 c39 s44 with true
                then
                  work12 c39 (cons s44 l3) r3 seq23
                else
                  work13 c39 l3 (cons s44 r3) seq23
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
      lam st330.
        lam seq31.
          p_map
            st330
            (lam x503.
               match null x503 with true
               then
                 x503
               else
                 let h1 = head x503 in
                 let lr1 = work14 h1 "" "" (reverse (tail x503)) in
                 match lr1 with (#var"X6",)
                 in
                 match lr1 with {#label"1" = #var"X7"}
                 in
                 concat (quickSort #var"X6") (cons h1 (quickSort #var"X7")))
            seq31
  in
  recursive
    let rec213 =
      lam st331.
        lam c40.
          lam c41.
            lam c42.
              lam c43.
                lam c44.
                  lam c45.
                    lam acc19.
                      lam s214.
                        match s214 with [ _ ] ++ _
                        then
                          let x504 = get s214 0 in
                          match
                            p_map
                              st331
                              (lam x505.
                                 lam x506.
                                   addf x505 x506)
                              acc19
                          with
                            (st332, x507)
                          in
                          match
                            hostIndepLikelihood
                              st332
                              1
                              (get c40 (subi x504 1))
                              (get c41 (subi x504 1))
                              c42
                              c43
                              (get c45 (subi x504 1))
                              (match c44 with ModelParams1 x1191
                               then
                                 x1191.embeddedQMatrix
                               else
                                 let #var"157" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st333, x508)
                          in
                          match p_apply st333 x507 x508 with (st334, x509)
                          in
                          match splitAt s214 1 with {#label"1" = x510}
                          in
                          rec213 st334 c40 c41 c42 c43 c44 c45 x509 x510
                        else match s214 with ""
                        in
                        (st331, acc19)
    let rec214 =
      lam st335.
        lam c46.
          lam c47.
            lam c48.
              lam c49.
                lam c50.
                  lam c51.
                    lam acc20.
                      lam s215.
                        match s215 with [ _ ] ++ _
                        then
                          let x511 = get s215 0 in
                          match
                            p_map
                              st335
                              (lam x512.
                                 lam x513.
                                   addf x512 x513)
                              acc20
                          with
                            (st336, x514)
                          in
                          match
                            hostIndepLikelihood2
                              st336
                              1
                              (get c46 (subi x511 1))
                              (get c47 (subi x511 1))
                              c48
                              c49
                              (get c51 (subi x511 1))
                              (match c50 with ModelParams1 x1192
                               then
                                 x1192.embeddedQMatrix
                               else
                                 let #var"158" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st337, x515)
                          in
                          match p_apply st337 x514 x515 with (st338, x516)
                          in
                          match splitAt s215 1 with {#label"1" = x517}
                          in
                          rec214 st338 c46 c47 c48 c49 c50 c51 x516 x517
                        else match s215 with ""
                        in
                        (st335, acc20)
  in
  let anon20 = lam x867.
      addi x867 1 in
  recursive
    let rec36 =
      lam i18.
        lam acc110.
          match geqi i18 0 with true
          then
            rec36 (subi i18 1) (cons (anon20 i18) acc110)
          else
            acc110
  in
  let create14 =
    lam l61.
      let i19 = subi l61 1 in
      match geqi i19 0 with true
      then
        rec36 (subi i19 1) (cons (anon20 i19) "")
      else
        ""
  in
  recursive
    let rec215 =
      lam st339.
        lam acc23.
          lam s216.
            match s216 with [ _ ] ++ _
            then
              match
                p_map
                  st339
                  (lam x518.
                     lam x519.
                       addf x518 x519)
                  acc23
              with
                (st340, x520)
              in
              match p_apply st340 x520 (get s216 0) with (st341, x521)
              in
              match splitAt s216 1 with {#label"1" = x522}
              in
              rec215 st341 x521 x522
            else match s216 with ""
            in
            (st339, acc23)
  in
  let fold2 =
    lam st556.
      lam init11.
        lam seq51.
          match seq51 with [ _ ] ++ _
          then
            match
              p_map
                st556
                (lam x864.
                   addf init11 x864)
                (get seq51 0)
            with
              (st557, x865)
            in
            match splitAt seq51 1 with {#label"1" = x866}
            in
            rec215 st557 x865 x866
          else match seq51 with ""
          in
          (st556, p_pure init11)
  in
  recursive
    let rec216 =
      lam st342.
        lam c52.
          lam acc24.
            lam s217.
              match s217 with [ _ ] ++ _
              then
                match acc24 with (field2, field3)
                in
                match
                  match field3 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st342
                        (lam x523.
                           addi x523 1)
                        (get field3 0)
                    with
                      (st343, x524)
                    in
                    match mtxGet1 st343 x524 (addi (get s217 0) 1) c52 with (st344, x525)
                    in
                    match log11 st344 x525 with (st345, x526)
                    in
                    match splitAt field3 1 with {#label"1" = x527}
                    in
                    (st345, (snoc field2 x526, x527))
                  else
                    let x528 = error "foldl2: Cannot happen!" in
                    match x528 with (x529,)
                    in
                    match x528 with {#label"1" = x530}
                    in
                    (st342, (map (lam x531.
                         p_pure x531) x529, map (lam x532.
                         p_pure x532) x530))
                with
                  (st346, x533)
                in
                match splitAt s217 1 with {#label"1" = x534}
                in
                rec216 st346 c52 x533 x534
              else match s217 with ""
              in
              (st342, acc24)
    let rec217 =
      lam st347.
        lam c53.
          lam acc25.
            lam s218.
              match s218 with [ _ ] ++ _
              then
                match acc25 with (field4, field5)
                in
                match
                  match field5 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st347
                        (lam x535.
                           addi x535 1)
                        (get field5 0)
                    with
                      (st348, x536)
                    in
                    match
                      p_map
                        st348
                        (lam x537.
                           addi x537 1)
                        (get s218 0)
                    with
                      (st349, x538)
                    in
                    match mtxGet2 st349 x536 x538 c53 with (st350, x539)
                    in
                    match log11 st350 x539 with (st351, x540)
                    in
                    match splitAt field5 1 with {#label"1" = x541}
                    in
                    (st351, (snoc field4 x540, x541))
                  else
                    let x542 = error "foldl2: Cannot happen!" in
                    match x542 with (x543,)
                    in
                    match x542 with {#label"1" = x544}
                    in
                    (st347, (map (lam x545.
                         p_pure x545) x543, map (lam x546.
                         p_pure x546) x544))
                with
                  (st352, x547)
                in
                match splitAt s218 1 with {#label"1" = x548}
                in
                rec217 st352 c53 x547 x548
              else match s218 with ""
              in
              (st347, acc25)
  in
  recursive
    let rec218 =
      lam st353.
        lam c54.
          lam acc26.
            lam s219.
              match s219 with [ _ ] ++ _
              then
                match acc26 with (field6, field7)
                in
                match
                  match field7 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st353
                        (lam x549.
                           addi x549 1)
                        (get s219 0)
                    with
                      (st354, x550)
                    in
                    match mtxGet1 st354 x550 (addi (get field7 0) 1) c54 with (st355, x551)
                    in
                    match log11 st355 x551 with (st356, x552)
                    in
                    match splitAt field7 1 with {#label"1" = x553}
                    in
                    (st356, (snoc field6 x552, x553))
                  else
                    let x554 = error "foldl2: Cannot happen!" in
                    match x554 with (x555,)
                    in
                    match x554 with {#label"1" = x556}
                    in
                    (st353, (map (lam x557.
                         p_pure x557) x555, x556))
                with
                  (st357, x558)
                in
                match splitAt s219 1 with {#label"1" = x559}
                in
                rec218 st357 c54 x558 x559
              else match s219 with ""
              in
              (st353, acc26)
    let rec219 =
      lam st358.
        lam c55.
          lam acc27.
            lam s220.
              match s220 with [ _ ] ++ _
              then
                match acc27 with (field8, field9)
                in
                match
                  match field9 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st358
                        (lam x560.
                           addi x560 1)
                        (get s220 0)
                    with
                      (st359, x561)
                    in
                    match
                      p_map
                        st359
                        (lam x562.
                           addi x562 1)
                        (get field9 0)
                    with
                      (st360, x563)
                    in
                    match mtxGet2 st360 x561 x563 c55 with (st361, x564)
                    in
                    match log11 st361 x564 with (st362, x565)
                    in
                    match splitAt field9 1 with {#label"1" = x566}
                    in
                    (st362, (snoc field8 x565, x566))
                  else
                    let x567 = error "foldl2: Cannot happen!" in
                    match x567 with (x568,)
                    in
                    match x567 with {#label"1" = x569}
                    in
                    (st358, (map (lam x570.
                         p_pure x570) x568, map (lam x571.
                         p_pure x571) x569))
                with
                  (st363, x572)
                in
                match splitAt s220 1 with {#label"1" = x573}
                in
                rec219 st363 c55 x572 x573
              else match s220 with ""
              in
              (st358, acc27)
  in
  recursive
    let sampleTreeHistory =
      lam st364.
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
                            let #var"174" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 121:14-121:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
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
                            let #var"173" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 127:6-127:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                            in
                            exit 1
                        in
                        match
                          rec9
                            st364
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
                               let #var"159" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:6-129:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create13 (addi (subi nHosts 1) 1))
                        with
                          (st365, unorderedBranch)
                        in
                        match paste0 st365 unorderedBranch with (st366, x574)
                        in
                        match quickSort1 st366 x574 with (st367, orderedEvents)
                        in
                        match length13 st367 orderedEvents with (st368, nEvents4)
                        in
                        match
                          allTimesValidBranch st368 parentRep orderedEvents 1 nEvents4 nHosts
                        with
                          (st369, x575)
                        in
                        match
                          p_bind
                            st369
                            simpleStoreSubmodel
                            (simpleInit {})
                            (lam st370.
                               lam x576.
                                 match
                                   match x576 with true
                                   then
                                     let s221 = create14 (addi (subi (length11 unorderedBranch) 1) 1)
                                     in
                                     match
                                       match s221 with [ _ ] ++ _
                                       then
                                         let x577 = get s221 0 in
                                         match
                                           hostIndepLikelihood
                                             st370
                                             1
                                             (get parentRep (subi x577 1))
                                             (get rep1 (subi x577 1))
                                             parentAge
                                             finalAge3
                                             (get unorderedBranch (subi x577 1))
                                             (match modelParams11 with ModelParams1 x1193
                                              then
                                                x1193.embeddedQMatrix
                                              else
                                                let #var"160" =
                                                  print
                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                                in
                                                exit 1)
                                         with
                                           (st371, x578)
                                         in
                                         match
                                           p_map
                                             st371
                                             (lam x579.
                                                addf 0. x579)
                                             x578
                                         with
                                           (st372, x580)
                                         in
                                         match splitAt s221 1 with {#label"1" = x581}
                                         in
                                         rec213
                                           st372
                                           parentRep
                                           rep1
                                           parentAge
                                           finalAge3
                                           modelParams11
                                           unorderedBranch
                                           x580
                                           x581
                                       else match s221 with ""
                                       in
                                       (st370, p_pure 0.)
                                     with
                                       (st373, x582)
                                     in
                                     match
                                       p_map
                                         st373
                                         (lam x583.
                                            lam x584.
                                              subf x583 x584)
                                         x582
                                     with
                                       (st374, x585)
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
                                                     st374
                                                     (lam x586.
                                                        addi x586 1)
                                                     (get field11 0)
                                                 with
                                                   (st375, x587)
                                                 in
                                                 match
                                                   mtxGet1 st375 x587 (addi (get rep1 0) 1) branchKernel
                                                 with
                                                   (st376, x588)
                                                 in
                                                 match log11 st376 x588 with (st377, x589)
                                                 in
                                                 match splitAt field11 1 with {#label"1" = x590}
                                                 in
                                                 (st377, (snoc field10 x589, x590))
                                               else
                                                 let x591 = error "foldl2: Cannot happen!" in
                                                 match x591 with (x592,)
                                                 in
                                                 match x591 with {#label"1" = x593}
                                                 in
                                                 (st374, (map
                                                   (lam x594.
                                                      p_pure x594)
                                                   x592, map
                                                   (lam x595.
                                                      p_pure x595)
                                                   x593))
                                             with
                                               (st378, x596)
                                             in
                                             match splitAt rep1 1 with {#label"1" = x597}
                                             in
                                             rec216 st378 branchKernel x596 x597
                                           else match rep1 with ""
                                           in
                                           (st374, acc28)
                                         with
                                           (st379, x598)
                                         in
                                         match x598 with (field12, field13)
                                         in
                                         (st379, field12)
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
                                                     st374
                                                     (lam x599.
                                                        addi x599 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st380, x600)
                                                 in
                                                 match
                                                   mtxGet1 st380 x600 (addi (get field15 0) 1) branchKernel
                                                 with
                                                   (st381, x601)
                                                 in
                                                 match log11 st381 x601 with (st382, x602)
                                                 in
                                                 match splitAt field15 1 with {#label"1" = x603}
                                                 in
                                                 (st382, (snoc field14 x602, x603))
                                               else
                                                 let x604 = error "foldl2: Cannot happen!" in
                                                 match x604 with (x605,)
                                                 in
                                                 match x604 with {#label"1" = x606}
                                                 in
                                                 (st374, (map
                                                   (lam x607.
                                                      p_pure x607)
                                                   x605, x606))
                                             with
                                               (st383, x608)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x609}
                                             in
                                             rec218 st383 branchKernel x608 x609
                                           else match parentRep with ""
                                           in
                                           (st374, acc29)
                                         with
                                           (st384, x610)
                                         in
                                         match x610 with (field16, field17)
                                         in
                                         (st384, field16)
                                     with
                                       (st385, x611)
                                     in
                                     match fold2 st385 0. x611 with (st386, x612)
                                     in
                                     match p_apply st386 x585 x612 with (st387, x613)
                                     in
                                     match
                                       p_bind
                                         st387
                                         simpleStoreSubmodel
                                         (simpleInit {})
                                         (lam st388.
                                            lam x614.
                                              match gti 1 x614 with true
                                              then
                                                match
                                                  getTotalRate st388 parentRep modelParams11 nHosts
                                                with
                                                  (st389, x615)
                                                in
                                                p_map
                                                  st389
                                                  (lam x616.
                                                     mulf (negf (subf parentAge finalAge3)) x616)
                                                  x615
                                              else match
                                                p_map
                                                  st388
                                                  (lam x617.
                                                     get x617 (subi 1 1))
                                                  orderedEvents
                                              with
                                                (st390, nextEvent2)
                                              in
                                              match
                                                p_map
                                                  st390
                                                  (lam x618.
                                                     match x618 with Event1 x3110
                                                     then
                                                       x3110.eventTime
                                                     else
                                                       let #var"161" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st391, newAge2)
                                              in
                                              match
                                                getTotalRate st391 parentRep modelParams11 nHosts
                                              with
                                                (st392, totalLeavingRate12)
                                              in
                                              match
                                                p_map
                                                  st392
                                                  (lam x619.
                                                     match x619 with Event1 x1343
                                                     then
                                                       x1343.host
                                                     else
                                                       let #var"162" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st393, hostIndex12)
                                              in
                                              match
                                                p_map
                                                  st393
                                                  (lam x620.
                                                     match x620 with Event1 x1323
                                                     then
                                                       x1323.fromState
                                                     else
                                                       let #var"163" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:45-84:64>:\nField \'fromState\' not found\n[0m  printLn(paste0([\"From state: \", int2string([31mnextEvent.fromState[0m[0m), \", to state: \", int2string(nextEvent.toState)]));\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st394, x621)
                                              in
                                              match int2string1 st394 x621 with (st395, x622)
                                              in
                                              match
                                                p_map
                                                  st395
                                                  (lam x623.
                                                     match x623 with Event1 x1333
                                                     then
                                                       x1333.toState
                                                     else
                                                       let #var"164" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:94-84:111>:\nField \'toState\' not found\n[0m  printLn(paste0([\"From state: \", int2string(nextEvent.fromState), \", to state: \", int2string([31mnextEvent.toState[0m[0m)]));\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st396, x624)
                                              in
                                              match int2string1 st396 x624 with (st397, x625)
                                              in
                                              match
                                                paste01
                                                  st397
                                                  [ p_pure "From state: ",
                                                    x622,
                                                    p_pure ", to state: ",
                                                    x625 ]
                                              with
                                                (st398, x626)
                                              in
                                              match
                                                p_map
                                                  st398
                                                  (lam x627.
                                                     printError (concat x627 "\n"))
                                                  x626
                                              with
                                                (st399, #var"212")
                                              in
                                              let #var"82" = flushStderr {} in
                                              let #var"72" = {} in
                                              match
                                                p_map
                                                  st399
                                                  (lam x628.
                                                     lam x629.
                                                       lam st400.
                                                         match
                                                           gti
                                                             (match x628 with Event1 x1303
                                                              then
                                                                x1303.fromState
                                                              else
                                                                let #var"165" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 85:5-85:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x629
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st400 parentRep hostIndex12 modelParams11
                                                         else
                                                           getGainRate2 st400 parentRep hostIndex12 modelParams11)
                                                  nextEvent2
                                              with
                                                (st401, x630)
                                              in
                                              match
                                                p_map
                                                  st401
                                                  (lam x631.
                                                     match x631 with Event1 x1313
                                                     then
                                                       x1313.toState
                                                     else
                                                       let #var"166" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 85:27-85:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st402, x632)
                                              in
                                              match
                                                p_subApply st402 simpleStoreSubmodel (simpleInit {}) x630 x632
                                              with
                                                (st403, x633)
                                              in
                                              match p_join st403 x633 with (st404, x634)
                                              in
                                              match
                                                p_map
                                                  st404
                                                  (lam x635.
                                                     lam x636.
                                                       divf x635 x636)
                                                  x634
                                              with
                                                (st405, x637)
                                              in
                                              match p_apply st405 x637 totalLeavingRate12 with (st406, x638)
                                              in
                                              match log11 st406 x638 with (st407, x639)
                                              in
                                              match
                                                p_map
                                                  st407
                                                  (lam x640.
                                                     lam x641.
                                                       lam x642.
                                                         addf (subf x640 x641) x642)
                                                  x639
                                              with
                                                (st408, x643)
                                              in
                                              match
                                                p_map
                                                  st408
                                                  (lam x644.
                                                     lam x645.
                                                       mulf (subf parentAge x644) x645)
                                                  newAge2
                                              with
                                                (st409, x646)
                                              in
                                              match p_apply st409 x646 totalLeavingRate12 with (st410, x647)
                                              in
                                              match p_apply st410 x643 x647 with (st411, x648)
                                              in
                                              match
                                                updateRepertoire st411 parentRep nextEvent2 nHosts
                                              with
                                                (st412, x649)
                                              in
                                              match
                                                fullModelWeight
                                                  st412
                                                  (addi 1 1)
                                                  x649
                                                  rep1
                                                  newAge2
                                                  finalAge3
                                                  orderedEvents
                                                  x614
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st413, x650)
                                              in
                                              p_apply st413 x648 x650)
                                         nEvents4
                                     with
                                       (st414, x651)
                                     in
                                     (st414, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = x613,
                                         logModelDensity = x651,
                                         success = true })
                                   else
                                     (st370, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = p_pure (log1 0.),
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st415, x652)
                                 in
                                 match x652 with CorrectedBranchSample1 x653
                                 in
                                 match x653 with {history = x654}
                                 in
                                 match
                                   p_map
                                     st415
                                     (lam x655.
                                        lam x656.
                                          lam x657.
                                            match x653 with {success = x658}
                                            in
                                            CorrectedBranchSample1
                                              { history = x655,
                                                logSamplingDensity = x656,
                                                logModelDensity = x657,
                                                success = x658 })
                                     x654
                                 with
                                   (st416, x659)
                                 in
                                 match x653 with {logSamplingDensity = x660}
                                 in
                                 match p_apply st416 x659 x660 with (st417, x661)
                                 in
                                 match x653 with {logModelDensity = x662}
                                 in
                                 p_apply st417 x661 x662)
                            x575
                        with
                          (st418, branchSample)
                        in
                        match
                          p_map
                            st418
                            (lam x663.
                               lam x664.
                                 mulf
                                   (subf
                                      (match x663 with CorrectedBranchSample1 x4610
                                       then
                                         x4610.logModelDensity
                                       else
                                         let #var"167" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 135:15-135:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x664)
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
                                               let #var"168" =
                                                 print
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 135:90-135:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1))
                                         0.)))
                            branchSample
                        with
                          (st419, x665)
                        in
                        match
                          p_map
                            st419
                            (lam x666.
                               match x666 with CorrectedBranchSample1 x4710
                               then
                                 x4710.logSamplingDensity
                               else
                                 let #var"169" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 135:46-135:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st420, x667)
                        in
                        match p_apply st420 x665 x667 with (st421, x668)
                        in
                        let st422 =
                          p_weight
                            st421
                            simpleStoreWeight
                            (/-temp-/lam x671.
                               x671)
                            x668
                        in
                        let foo = {} in
                        match
                          p_map
                            st422
                            (lam x669.
                               match x669 with CorrectedBranchSample1 x4510
                               then
                                 x4510.history
                               else
                                 let #var"170" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 141:16-141:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st423, x670)
                        in
                        (st423, HistoryLeaf
                          { age =
                              match tree2 with MsgLeaf carried28
                              then
                                carried28.age
                              else match tree2 with MsgNode carried29
                              then
                                carried29.age
                              else
                                let #var"171" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 138:12-138:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                let #var"172" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 139:14-139:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            history = x670,
                            repertoire = rep1 })
                      else match
                        mtxElemMul
                          st364
                          (match tree2 with MsgLeaf carried34
                           then
                             match carried34 with {outMsg = #var"X8"}
                             in
                             p_pure #var"X8"
                           else match tree2 with MsgNode carried35
                           then
                             carried35.outMsg
                           else
                             let #var"175" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 144:34-144:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                             in
                             p_pure (exit 1))
                          preorderMsg
                      with
                        (st424, samplingProb)
                      in
                      match
                        suggestNodeRep
                          st424
                          samplingProb
                          nHosts
                          (match tree2 with MsgLeaf carried36
                           then
                             carried36.label
                           else match tree2 with MsgNode carried37
                           then
                             carried37.label
                           else
                             let #var"176" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 145:51-145:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                             in
                             exit 1)
                      with
                        (st425, rep2)
                      in
                      match any1 st425 rep2 with (st426, x672)
                      in
                      match bool2real st426 x672 with (st427, x673)
                      in
                      let st428 =
                        p_weight
                          st427
                          simpleStoreWeight
                          (lam x787.
                             externalLog
                               (addf
                                  x787
                                  (mulf
                                     (int2float
                                        (match tree2 with MsgLeaf carried52
                                         then
                                           carried52.label
                                         else match tree2 with MsgNode carried53
                                         then
                                           carried53.label
                                         else
                                           let #var"1100" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 147:43-147:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1))
                                     0.)))
                          x673
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
                          let #var"199" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 155:6-155:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                          in
                          exit 1
                      in
                      match
                        rec10
                          st428
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
                             let #var"177" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:6-157:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                             in
                             exit 1)
                          modelParams11
                          (create13 (addi (subi nHosts 1) 1))
                      with
                        (st429, unorderedBranch1)
                      in
                      match paste0 st429 unorderedBranch1 with (st430, x674)
                      in
                      match quickSort1 st430 x674 with (st431, orderedEvents1)
                      in
                      match length13 st431 orderedEvents1 with (st432, nEvents41)
                      in
                      match
                        allTimesValidBranch st432 parentRep orderedEvents1 1 nEvents41 nHosts
                      with
                        (st433, x675)
                      in
                      match
                        p_bind
                          st433
                          simpleStoreSubmodel
                          (simpleInit {})
                          (lam st434.
                             lam x676.
                               match
                                 match x676 with true
                                 then
                                   let s222 = create14 (addi (subi (length11 unorderedBranch1) 1) 1)
                                   in
                                   match
                                     match s222 with [ _ ] ++ _
                                     then
                                       let x677 = get s222 0 in
                                       match
                                         hostIndepLikelihood2
                                           st434
                                           1
                                           (get parentRep (subi x677 1))
                                           (get rep2 (subi x677 1))
                                           parentAge
                                           finalAge31
                                           (get unorderedBranch1 (subi x677 1))
                                           (match modelParams11 with ModelParams1 x1194
                                            then
                                              x1194.embeddedQMatrix
                                            else
                                              let #var"178" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                              in
                                              exit 1)
                                       with
                                         (st435, x678)
                                       in
                                       match
                                         p_map
                                           st435
                                           (lam x679.
                                              addf 0. x679)
                                           x678
                                       with
                                         (st436, x680)
                                       in
                                       match splitAt s222 1 with {#label"1" = x681}
                                       in
                                       rec214
                                         st436
                                         parentRep
                                         rep2
                                         parentAge
                                         finalAge31
                                         modelParams11
                                         unorderedBranch1
                                         x680
                                         x681
                                     else match s222 with ""
                                     in
                                     (st434, p_pure 0.)
                                   with
                                     (st437, x682)
                                   in
                                   match
                                     p_map
                                       st437
                                       (lam x683.
                                          lam x684.
                                            subf x683 x684)
                                       x682
                                   with
                                     (st438, x685)
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
                                                   st438
                                                   (lam x686.
                                                      addi x686 1)
                                                   (get field19 0)
                                               with
                                                 (st439, x687)
                                               in
                                               match
                                                 p_map
                                                   st439
                                                   (lam x688.
                                                      addi x688 1)
                                                   (get rep2 0)
                                               with
                                                 (st440, x689)
                                               in
                                               match mtxGet2 st440 x687 x689 branchKernel with (st441, x690)
                                               in
                                               match log11 st441 x690 with (st442, x691)
                                               in
                                               match splitAt field19 1 with {#label"1" = x692}
                                               in
                                               (st442, (snoc field18 x691, x692))
                                             else
                                               let x693 = error "foldl2: Cannot happen!" in
                                               match x693 with (x694,)
                                               in
                                               match x693 with {#label"1" = x695}
                                               in
                                               (st438, (map
                                                 (lam x696.
                                                    p_pure x696)
                                                 x694, map
                                                 (lam x697.
                                                    p_pure x697)
                                                 x695))
                                           with
                                             (st443, x698)
                                           in
                                           match splitAt rep2 1 with {#label"1" = x699}
                                           in
                                           rec217 st443 branchKernel x698 x699
                                         else match rep2 with ""
                                         in
                                         (st438, acc30)
                                       with
                                         (st444, x700)
                                       in
                                       match x700 with (field20, field21)
                                       in
                                       (st444, field20)
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
                                                   st438
                                                   (lam x701.
                                                      addi x701 1)
                                                   (get parentRep 0)
                                               with
                                                 (st445, x702)
                                               in
                                               match
                                                 p_map
                                                   st445
                                                   (lam x703.
                                                      addi x703 1)
                                                   (get field23 0)
                                               with
                                                 (st446, x704)
                                               in
                                               match mtxGet2 st446 x702 x704 branchKernel with (st447, x705)
                                               in
                                               match log11 st447 x705 with (st448, x706)
                                               in
                                               match splitAt field23 1 with {#label"1" = x707}
                                               in
                                               (st448, (snoc field22 x706, x707))
                                             else
                                               let x708 = error "foldl2: Cannot happen!" in
                                               match x708 with (x709,)
                                               in
                                               match x708 with {#label"1" = x710}
                                               in
                                               (st438, (map
                                                 (lam x711.
                                                    p_pure x711)
                                                 x709, map
                                                 (lam x712.
                                                    p_pure x712)
                                                 x710))
                                           with
                                             (st449, x713)
                                           in
                                           match splitAt parentRep 1 with {#label"1" = x714}
                                           in
                                           rec219 st449 branchKernel x713 x714
                                         else match parentRep with ""
                                         in
                                         (st438, acc33)
                                       with
                                         (st450, x715)
                                       in
                                       match x715 with (field24, field25)
                                       in
                                       (st450, field24)
                                   with
                                     (st451, x716)
                                   in
                                   match fold2 st451 0. x716 with (st452, x717)
                                   in
                                   match p_apply st452 x685 x717 with (st453, x718)
                                   in
                                   match
                                     p_bind
                                       st453
                                       simpleStoreSubmodel
                                       (simpleInit {})
                                       (lam st454.
                                          lam x719.
                                            match gti 1 x719 with true
                                            then
                                              match
                                                getTotalRate st454 parentRep modelParams11 nHosts
                                              with
                                                (st455, x720)
                                              in
                                              p_map
                                                st455
                                                (lam x721.
                                                   mulf (negf (subf parentAge finalAge31)) x721)
                                                x720
                                            else match
                                              p_map
                                                st454
                                                (lam x722.
                                                   get x722 (subi 1 1))
                                                orderedEvents1
                                            with
                                              (st456, nextEvent3)
                                            in
                                            match
                                              p_map
                                                st456
                                                (lam x723.
                                                   match x723 with Event1 x3111
                                                   then
                                                     x3111.eventTime
                                                   else
                                                     let #var"179" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st457, newAge3)
                                            in
                                            match
                                              getTotalRate st457 parentRep modelParams11 nHosts
                                            with
                                              (st458, totalLeavingRate13)
                                            in
                                            match
                                              p_map
                                                st458
                                                (lam x724.
                                                   match x724 with Event1 x1344
                                                   then
                                                     x1344.host
                                                   else
                                                     let #var"180" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st459, hostIndex13)
                                            in
                                            match
                                              p_map
                                                st459
                                                (lam x725.
                                                   match x725 with Event1 x1324
                                                   then
                                                     x1324.fromState
                                                   else
                                                     let #var"181" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:45-84:64>:\nField \'fromState\' not found\n[0m  printLn(paste0([\"From state: \", int2string([31mnextEvent.fromState[0m[0m), \", to state: \", int2string(nextEvent.toState)]));\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st460, x726)
                                            in
                                            match int2string1 st460 x726 with (st461, x727)
                                            in
                                            match
                                              p_map
                                                st461
                                                (lam x728.
                                                   match x728 with Event1 x1334
                                                   then
                                                     x1334.toState
                                                   else
                                                     let #var"182" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:94-84:111>:\nField \'toState\' not found\n[0m  printLn(paste0([\"From state: \", int2string(nextEvent.fromState), \", to state: \", int2string([31mnextEvent.toState[0m[0m)]));\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st462, x729)
                                            in
                                            match int2string1 st462 x729 with (st463, x730)
                                            in
                                            match
                                              paste01
                                                st463
                                                [ p_pure "From state: ",
                                                  x727,
                                                  p_pure ", to state: ",
                                                  x730 ]
                                            with
                                              (st464, x731)
                                            in
                                            match
                                              p_map
                                                st464
                                                (lam x732.
                                                   printError (concat x732 "\n"))
                                                x731
                                            with
                                              (st465, #var"213")
                                            in
                                            let #var"83" = flushStderr {} in
                                            let #var"73" = {} in
                                            match
                                              p_map
                                                st465
                                                (lam x733.
                                                   lam x734.
                                                     lam st466.
                                                       match
                                                         gti
                                                           (match x733 with Event1 x1304
                                                            then
                                                              x1304.fromState
                                                            else
                                                              let #var"183" =
                                                                print
                                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 85:5-85:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                              in
                                                              exit 1)
                                                           x734
                                                       with
                                                         true
                                                       then
                                                         getLossRate2 st466 parentRep hostIndex13 modelParams11
                                                       else
                                                         getGainRate2 st466 parentRep hostIndex13 modelParams11)
                                                nextEvent3
                                            with
                                              (st467, x735)
                                            in
                                            match
                                              p_map
                                                st467
                                                (lam x736.
                                                   match x736 with Event1 x1314
                                                   then
                                                     x1314.toState
                                                   else
                                                     let #var"184" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 85:27-85:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st468, x737)
                                            in
                                            match
                                              p_subApply st468 simpleStoreSubmodel (simpleInit {}) x735 x737
                                            with
                                              (st469, x738)
                                            in
                                            match p_join st469 x738 with (st470, x739)
                                            in
                                            match
                                              p_map
                                                st470
                                                (lam x740.
                                                   lam x741.
                                                     divf x740 x741)
                                                x739
                                            with
                                              (st471, x742)
                                            in
                                            match p_apply st471 x742 totalLeavingRate13 with (st472, x743)
                                            in
                                            match log11 st472 x743 with (st473, x744)
                                            in
                                            match
                                              p_map
                                                st473
                                                (lam x745.
                                                   lam x746.
                                                     lam x747.
                                                       addf (subf x745 x746) x747)
                                                x744
                                            with
                                              (st474, x748)
                                            in
                                            match
                                              p_map
                                                st474
                                                (lam x749.
                                                   lam x750.
                                                     mulf (subf parentAge x749) x750)
                                                newAge3
                                            with
                                              (st475, x751)
                                            in
                                            match p_apply st475 x751 totalLeavingRate13 with (st476, x752)
                                            in
                                            match p_apply st476 x748 x752 with (st477, x753)
                                            in
                                            match
                                              updateRepertoire st477 parentRep nextEvent3 nHosts
                                            with
                                              (st478, x754)
                                            in
                                            match
                                              fullModelWeight1
                                                st478
                                                (addi 1 1)
                                                x754
                                                rep2
                                                newAge3
                                                finalAge31
                                                orderedEvents1
                                                x719
                                                nHosts
                                                modelParams11
                                            with
                                              (st479, x755)
                                            in
                                            p_apply st479 x753 x755)
                                       nEvents41
                                   with
                                     (st480, x756)
                                   in
                                   (st480, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = x718,
                                       logModelDensity = x756,
                                       success = true })
                                 else
                                   (st434, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = p_pure (log1 0.),
                                       logModelDensity = p_pure (log1 0.),
                                       success = false })
                               with
                                 (st481, x757)
                               in
                               match x757 with CorrectedBranchSample1 x758
                               in
                               match x758 with {history = x759}
                               in
                               match
                                 p_map
                                   st481
                                   (lam x760.
                                      lam x761.
                                        lam x762.
                                          match x758 with {success = x763}
                                          in
                                          CorrectedBranchSample1
                                            { history = x760,
                                              logSamplingDensity = x761,
                                              logModelDensity = x762,
                                              success = x763 })
                                   x759
                               with
                                 (st482, x764)
                               in
                               match x758 with {logSamplingDensity = x765}
                               in
                               match p_apply st482 x764 x765 with (st483, x766)
                               in
                               match x758 with {logModelDensity = x767}
                               in
                               p_apply st483 x766 x767)
                          x675
                      with
                        (st484, branchSample1)
                      in
                      match
                        p_map
                          st484
                          (lam x768.
                             lam x769.
                               lam x770.
                                 subf
                                   (subf
                                      (match x768 with CorrectedBranchSample1 x7010
                                       then
                                         x7010.logModelDensity
                                       else
                                         let #var"185" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 163:14-163:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x769)
                                   x770)
                          branchSample1
                      with
                        (st485, x771)
                      in
                      match
                        p_map
                          st485
                          (lam x772.
                             match x772 with CorrectedBranchSample1 x7110
                             then
                               x7110.logSamplingDensity
                             else
                               let #var"186" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 163:45-163:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st486, x773)
                      in
                      match p_apply st486 x771 x773 with (st487, x774)
                      in
                      match
                        getRepertoireSamplingDensity st487 rep2 samplingProb nHosts
                      with
                        (st488, x775)
                      in
                      match
                        p_map
                          st488
                          (lam x776.
                             mulf
                               x776
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
                                           let #var"187" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 163:113-163:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1))
                                     0.)))
                          x775
                      with
                        (st489, x777)
                      in
                      match p_apply st489 x774 x777 with (st490, x778)
                      in
                      let st491 =
                        p_weight
                          st490
                          simpleStoreWeight
                          (/-temp-/lam x786.
                             x786)
                          x778
                      in
                      let foo2 = {} in
                      match observationMessage1 st491 rep2 1 nHosts with (st492, x779)
                      in
                      match mtxCreate1 st492 nHosts 3 x779 with (st493, newMsg)
                      in
                      match
                        mtxMul
                          st493
                          newMsg
                          (match tree2 with MsgNode x6910
                           then
                             x6910.leftKernel
                           else
                             let #var"188" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 167:33-167:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st494, x780)
                      in
                      match
                        sampleTreeHistory
                          st494
                          (match tree2 with MsgNode x6410
                           then
                             x6410.left
                           else
                             let #var"189" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 172:6-172:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          nHosts
                          x780
                          rep2
                          (match tree2 with MsgLeaf carried42
                           then
                             carried42.age
                           else match tree2 with MsgNode carried43
                           then
                             carried43.age
                           else
                             let #var"190" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 172:39-172:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6710
                           then
                             x6710.leftKernel
                           else
                             let #var"191" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 172:62-172:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st495, x781)
                      in
                      match
                        mtxMul
                          st495
                          newMsg
                          (match tree2 with MsgNode x6810
                           then
                             x6810.rightKernel
                           else
                             let #var"192" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 168:34-168:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st496, x782)
                      in
                      match
                        sampleTreeHistory
                          st496
                          (match tree2 with MsgNode x6010
                           then
                             x6010.right
                           else
                             let #var"193" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 175:6-175:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          nHosts
                          x782
                          rep2
                          (match tree2 with MsgLeaf carried44
                           then
                             carried44.age
                           else match tree2 with MsgNode carried45
                           then
                             carried45.age
                           else
                             let #var"194" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 175:41-175:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6310
                           then
                             x6310.rightKernel
                           else
                             let #var"195" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 175:64-175:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st497, x783)
                      in
                      match
                        p_map
                          st497
                          (lam x784.
                             match x784 with CorrectedBranchSample1 x5910
                             then
                               x5910.history
                             else
                               let #var"196" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 182:16-182:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st498, x785)
                      in
                      (st498, HistoryNode
                        { age =
                            match tree2 with MsgLeaf carried46
                            then
                              carried46.age
                            else match tree2 with MsgNode carried47
                            then
                              carried47.age
                            else
                              let #var"197" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 179:12-179:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                              let #var"198" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 180:14-180:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                              in
                              exit 1,
                          left = x781,
                          right = x783,
                          history = x785,
                          repertoire = rep2 })
  in
  let input1 =
    { dMean = 1.,
      interactions = [ [ 1, 1 ],
          [ 1, 1 ] ],
      symbiontTree =
        Node
          { age = 1.,
            label = 3,
            left = Leaf
                { age = 0., label = 1 },
            right = Leaf
                { age = 0., label = 2 } },
      hostDistances = [ [ 0., 1. ],
          [ 1., 0. ] ] }
  in
  match input1 with {symbiontTree = #var"X9"}
  in
  let symbiontTree = #var"X9" in
  match input1 with {hostDistances = #var"X10"}
  in
  let hostDistances = #var"X10" in
  let nHosts1 = length1 hostDistances in
  match
    p_assume
      st simpleStoreAssume (p_pure (mkDirichlet [ 1., 1., 1., 1. ]))
  with
    (st499, lambda)
  in
  match
    p_assume st499 simpleStoreAssume (p_pure (mkExponential 10.))
  with
    (st500, mu)
  in
  match
    p_assume st500 simpleStoreAssume (p_pure (mkExponential 1.))
  with
    (st501, beta)
  in
  match
    p_map
      st501
      (lam x788.
         subf 0. (get x788 (subi 1 1)))
      lambda
  with
    (st502, x789)
  in
  match
    p_map st502 (lam x790.
         get x790 (subi 1 1)) lambda
  with
    (st503, x791)
  in
  match
    p_map st503 (lam x792.
         get x792 (subi 2 1)) lambda
  with
    (st504, x793)
  in
  match
    p_map
      st504
      (lam x794.
         lam x795.
           subf 0. (addf (get x794 (subi 2 1)) x795))
      lambda
  with
    (st505, x796)
  in
  match
    p_map st505 (lam x797.
         get x797 (subi 3 1)) lambda
  with
    (st506, x798)
  in
  match p_apply st506 x796 x798 with (st507, x799)
  in
  match
    p_map st507 (lam x800.
         get x800 (subi 3 1)) lambda
  with
    (st508, x801)
  in
  match
    p_map st508 (lam x802.
         get x802 (subi 4 1)) lambda
  with
    (st509, x803)
  in
  match
    p_map
      st509
      (lam x804.
         subf 0. (get x804 (subi 4 1)))
      lambda
  with
    (st510, x805)
  in
  match
    mtxCreate1
      st510
      3
      3
      [ x789,
        x791,
        p_pure 0.,
        x793,
        x799,
        x801,
        p_pure 0.,
        x803,
        x805 ]
  with
    (st511, mtx4)
  in
  match p_map st511 (lam x806.
         x806.m) mtx4 with (st512, m2)
  in
  match p_map st512 (lam x807.
         x807.n) mtx4 with (st513, n4)
  in
  match
    p_map
      st513
      (lam x808.
         lam x809.
           lam x810.
             lam x811.
               lam x812.
                 tmOpaque (let b14 = matMakeUninit (externalExtArrKind x812.arr) x808 x809
                  in
                  let #var"1310" = externalCblasCopy x810 x812.arr 1 b14.arr 1 in
                  let #var"1410" = externalCblasScal x810 x811 b14.arr 1 in
                  b14))
      m2
  with
    (st514, x813)
  in
  match p_apply st514 x813 n4 with (st515, x814)
  in
  match
    p_map
      st515
      (lam x815.
         lam x816.
           muli x815 x816)
      m2
  with
    (st516, x817)
  in
  match p_apply st516 x817 n4 with (st517, x818)
  in
  match p_apply st517 x814 x818 with (st518, x819)
  in
  match p_apply st518 x819 mu with (st519, x820)
  in
  match p_apply st519 x820 mtx4 with (st520, qMatrix2)
  in
  match input1 with {interactions = #var"X11"}
  in
  match
    postorderTraverse st520 symbiontTree qMatrix2 #var"X11" nHosts1
  with
    (st521, postorderTree)
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
      let #var"1113" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 39:36-39:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n"
      in
      p_pure (exit 1)
  in
  let b4 = mtxCreate nHosts1 3 (ones (muli 3 nHosts1)) in
  match
    p_map
      st521
      (lam x821.
         match x821 with {m = #var"X12"}
         in
         match b4 with {m = #var"X13"}
         in
         eqi #var"X12" #var"X13")
      a36
  with
    (st522, x822)
  in
  match
    p_map
      st522
      (lam x823.
         match x823 with {n = #var"X14"}
         in
         match b4 with {n = #var"X15"}
         in
         eqi #var"X14" #var"X15")
      a36
  with
    (st523, x824)
  in
  match and1 st523 x822 x824 with (st524, x825)
  in
  match
    p_bind
      st524
      simpleStoreSubmodel
      (simpleInit {})
      (lam st525.
         lam x826.
           match
             match x826 with true
             then
               match
                 p_map
                   st525
                   (lam x827.
                      tmOpaque (let c310 = matMakeUninit (externalExtArrKind x827.arr) x827.m x827.n
                       in
                       let #var"1510" = matElemMulNoAlloc x827 b4 c310 in
                       c310))
                   a36
               with
                 (st526, x828)
               in
               (st526, Right
                 x828)
             else
               (st525, Left
                 (DimensionMismatch
                    {}))
           with
             (st527, n2)
           in
           match n2 with Right x829
           then
             p_map
               st527
               (lam x830.
                  Right
                    x830)
               x829
           else match n2 with Left x831
           in
           (st527, p_pure (Left
                x831)))
      x825
  with
    (st528, x832)
  in
  match eitherEither st528 x832 with (st529, rootSamplingProb)
  in
  match
    suggestNodeRep
      st529
      rootSamplingProb
      nHosts1
      (match postorderTree with MsgLeaf carried54
       then
         carried54.label
       else match postorderTree with MsgNode carried55
       then
         carried55.label
       else
         let #var"1101" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 40:57-40:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
         in
         exit 1)
  with
    (st530, rootRep)
  in
  match any1 st530 rootRep with (st531, x833)
  in
  match bool2real st531 x833 with (st532, x834)
  in
  let st533 =
    p_weight
      st532
      simpleStoreWeight
      (lam x863.
         externalLog
           (addf
              x863
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried64
                     then
                       carried64.label
                     else match postorderTree with MsgNode carried65
                     then
                       carried65.label
                     else
                       let #var"1112" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 42:45-42:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1))
                 0.)))
      x834
  in
  let foo3 = {} in
  match
    getRepertoireSamplingDensity st533 rootRep rootSamplingProb nHosts1
  with
    (st534, x835)
  in
  let st535 =
    p_weight
      st534
      simpleStoreWeight
      (lam x862.
         mulf
           (subf
              (negf
                 (log1
                    (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1)))))
              x862)
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
                       let #var"1111" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 49:70-49:89>:\nField \'label\' not found\n[0m  logWeight (rootLogModelDensity - rootLogSamplingDensity) * exp(Real([31mpostorderTree.label[0m[0m) * 0.);\n"
                       in
                       exit 1))
                 0.)))
      x835
  in
  let foo4 = {} in
  match observationMessage1 st535 rootRep 1 nHosts1 with (st536, x836)
  in
  match mtxCreate1 st536 nHosts1 3 x836 with (st537, newMsg1)
  in
  match input1 with {dMean = #var"X16"}
  in
  match mtxGet st537 2 2 qMatrix2 with (st538, x837)
  in
  match p_map st538 (lam x838.
         negf x838) x837 with (st539, q2)
  in
  match mtxGet st539 1 1 qMatrix2 with (st540, x839)
  in
  match p_map st540 (lam x840.
         negf x840) x839 with (st541, x841)
  in
  match mtxGet st541 3 3 qMatrix2 with (st542, x842)
  in
  match p_map st542 (lam x843.
         negf x843) x842 with (st543, x844)
  in
  match mtxGet st543 2 1 qMatrix2 with (st544, x845)
  in
  match
    p_map
      st544
      (lam x846.
         lam x847.
           divf x846 x847)
      x845
  with
    (st545, x848)
  in
  match p_apply st545 x848 q2 with (st546, x849)
  in
  match mtxGet st546 2 3 qMatrix2 with (st547, x850)
  in
  match
    p_map
      st547
      (lam x851.
         lam x852.
           divf x851 x852)
      x850
  with
    (st548, x853)
  in
  match p_apply st548 x853 q2 with (st549, x854)
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
               match splitAt hostDistances 1 with {#label"1" = x861}
               in
               rec2 (concat "" (get hostDistances 0)) x861
             else match hostDistances with ""
             in
             ""),
        embeddedQMatrix =
          EmbeddedMarkovChainMatrix1
            { totalRates =
                [ x841,
                  q2,
                  x844 ],
              transitionProbs =
                [ [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ],
                  [ x849,
                    p_pure 0.,
                    x854 ],
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
      let #var"1110" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 65:16-65:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    mtxMul
      st549
      newMsg1
      (match postorderTree with MsgNode x951
       then
         x951.leftKernel
       else
         let #var"1102" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 53:31-53:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st550, x855)
  in
  match
    sampleTreeHistory
      st550
      (match postorderTree with MsgNode x901
       then
         x901.left
       else
         let #var"1103" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 67:4-67:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
         in
         exit 1)
      nHosts1
      x855
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x911
       then
         x911.leftKernel
       else
         let #var"1104" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 67:72-67:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st551, x856)
  in
  match
    mtxMul
      st551
      newMsg1
      (match postorderTree with MsgNode x941
       then
         x941.rightKernel
       else
         let #var"1105" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 54:32-54:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st552, x857)
  in
  match
    sampleTreeHistory
      st552
      (match postorderTree with MsgNode x881
       then
         x881.right
       else
         let #var"1106" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 71:4-71:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
         in
         exit 1)
      nHosts1
      x857
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x891
       then
         x891.rightKernel
       else
         let #var"1107" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 71:74-71:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st553, x858)
  in
  match
    p_traverseSeq
      st553
      (lam st554.
         lam x859.
           (st554, x859))
      ""
  with
    (st555, x860)
  in
  p_export
    st555
    simpleStoreExport
    (p_pure
       (dprint
          (ReturnType1
             { mu = mu,
               beta = beta,
               tree =
                 HistoryNode
                   { age =
                       match symbiontTree with Leaf carried56
                       then
                         carried56.age
                       else match symbiontTree with Node carried57
                       then
                         carried57.age
                       else
                         let #var"1108" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 76:10-76:26>:\nField \'age\' not found\n[0m    age = [31msymbiontTree.age[0m[0m, label = symbiontTree.label,\n"
                         in
                         exit 1,
                     label =
                       match symbiontTree with Leaf carried58
                       then
                         carried58.label
                       else match symbiontTree with Node carried59
                       then
                         carried59.label
                       else
                         let #var"1109" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 76:36-76:54>:\nField \'label\' not found\n[0m    age = symbiontTree.age, label = [31msymbiontTree.label[0m[0m,\n"
                         in
                         exit 1,
                     left = x856,
                     right = x858,
                     history = x860,
                     repertoire = rootRep },
               lambda = lambda })))
