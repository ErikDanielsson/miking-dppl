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
    lam a88.
      lam b30.
        match a88 with true
        then
          b30
        else
          false
  in
  let pow = lam x1713.
      lam y2.
        externalPow x1713 y2
  in
  let pow1 =
    lam st668.
      lam x1712.
        lam y1.
          p_map
            st668 (lam x1063.
               externalPow x1712 x1063) y1
  in
  let pow2 =
    lam st666.
      lam x1711.
        lam y.
          match
            p_map
              st666
              (lam x1058.
                 lam x1059.
                   externalPow x1058 x1059)
              x1711
          with
            (st667, x1060)
          in
          p_apply st667 x1060 y
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
  recursive
    let rec1 =
      lam c.
        lam i.
          lam s1.
            match s1 with [ _,
                _ ] ++ _
            then
              match splitAt s1 1 with {#label"1" = x8}
              in
              cons (externalExtArrSet c i (get s1 0)) (rec1 c (addi i 1) x8)
            else match s1 with [ e ]
            then
              match splitAt s1 1 with {#label"1" = x9}
              in
              let slice = x9 in
              [ externalExtArrSet c i e ]
            else match s1 with ""
            in
            ""
    let rec11 =
      lam st7.
        lam c1.
          lam i1.
            lam s11.
              match s11 with [ _,
                  _ ] ++ _
              then
                match
                  p_map
                    st7
                    (lam x10.
                       externalExtArrSet c1 i1 x10)
                    (get s11 0)
                with
                  (st8, x11)
                in
                match splitAt s11 1 with {#label"1" = x12}
                in
                match rec11 st8 c1 (addi i1 1) x12 with (st9, x13)
                in
                (st9, cons x11 x13)
              else match s11 with [ e1 ]
              then
                match splitAt s11 1 with {#label"1" = x14}
                in
                let slice1 = x14 in
                match
                  p_map
                    st7
                    (lam x15.
                       externalExtArrSet c1 i1 x15)
                    e1
                with
                  (st10, x16)
                in
                (st10, [ x16 ])
              else match s11 with ""
              in
              (st7, "")
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
        lam n51.
          { arr = externalExtArrMakeUninit kind1 (muli m41 n51),
            n = n51,
            m = m41 }
  in
  let matMakeUninit1 =
    lam st664.
      lam kind.
        lam m4.
          lam n5.
            match
              p_map
                st664
                (lam x1056.
                   externalExtArrMakeUninit kind (muli m4 x1056))
                n5
            with
              (st665, x1057)
            in
            (st665, { arr = x1057, n = n5, m = m4 })
  in
  let matGetExn =
    lam a671.
      lam i162.
        lam j11.
          match a671 with {arr = #var"X80"}
          in
          match a671 with {n = #var"X81"}
          in
          externalExtArrGet #var"X80" (addi (muli i162 #var"X81") j11)
  in
  let matGetExn1 =
    lam st663.
      lam a67.
        lam i161.
          lam j1.
            p_map
              st663
              (lam x1055.
                 match a67 with {arr = #var"X78"}
                 in
                 match a67 with {n = #var"X79"}
                 in
                 externalExtArrGet #var"X78" (addi (muli x1055 #var"X79") j1))
              i161
  in
  let matHasSameShape2 =
    lam a61.
      lam b21.
        match a61 with {m = #var"X74"}
        in
        match b21 with {m = #var"X75"}
        in
        match a61 with {n = #var"X76"}
        in
        match b21 with {n = #var"X77"}
        in
        and (eqi #var"X74" #var"X75") (eqi #var"X76" #var"X77")
  in
  let exp1 = lam x1591.
      externalExp x1591 in
  let log1 = lam x1582.
      externalLog x1582 in
  let log11 =
    lam st662.
      lam x1581.
        p_map st662 (lam x1054.
             externalLog x1054) x1581
  in
  let cons1 = lam e112.
      lam s83.
        cons e112 s83 in
  let cons11 =
    lam st658.
      lam e111.
        lam s82.
          match e111 with Event1 x1044
          in
          match x1044 with {toState = x1045}
          in
          match
            p_map
              st658
              (lam x1046.
                 lam x1047.
                   match x1044 with {host = x1048}
                   in
                   match x1044 with {eventTime = x1049}
                   in
                   Event1
                     { host = x1048,
                       toState = x1046,
                       eventTime = x1049,
                       fromState = x1047 })
              x1045
          with
            (st659, x1050)
          in
          match x1044 with {fromState = x1051}
          in
          match p_apply st659 x1050 x1051 with (st660, x1052)
          in
          match p_map st660 cons x1052 with (st661, x1053)
          in
          p_apply st661 x1053 s82
  in
  let cons12 = lam e110.
      lam s81.
        cons e110 s81 in
  let paste0 =
    lam st652.
      lam l51.
        match l51 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st652
              (lam st653.
                 lam x1036.
                   (st653, x1036))
              ""
          with
            (st654, x1037)
          in
          match p_map st654 concat x1037 with (st655, x1038)
          in
          match p_apply st655 x1038 (get l51 0) with (st656, x1039)
          in
          match splitAt l51 1 with {#label"1" = x1040}
          in
          rec22 st656 x1039 x1040
        else match l51 with ""
        in
        p_traverseSeq
          st652
          (lam st657.
             lam x1043.
               (st657, x1043))
          ""
  in
  let paste01 =
    lam st646.
      lam l5.
        match l5 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st646
              (lam st647.
                 lam x1030.
                   (st647, x1030))
              ""
          with
            (st648, x1031)
          in
          match p_map st648 concat x1031 with (st649, x1032)
          in
          match p_apply st649 x1032 (get l5 0) with (st650, x1033)
          in
          match splitAt l5 1 with {#label"1" = x1034}
          in
          rec23 st650 x1033 x1034
        else match l5 with ""
        in
        p_traverseSeq
          st646
          (lam st651.
             lam x1035.
               (st651, x1035))
          ""
  in
  let slice2 =
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
  let length13 = lam st645.
      lam l31.
        p_map st645 length l31
  in
  let anon =
    lam x1027.
      lam x1028.
        lam x1029.
          match x1029 with true
          then
            snoc x1027 (addi x1028 1)
          else
            x1027
  in
  recursive
    let work =
      lam acc21.
        lam i2.
          lam s3.
            match s3 with [ e2 ] ++ rest
            then
              work
                (match e2 with true
                 then
                   snoc acc21 (addi i2 1)
                 else
                   acc21)
                (addi i2 1)
                rest
            else
              acc21
    let work1 =
      lam st11.
        lam acc22.
          lam i21.
            lam s31.
              match s31 with [ e3 ] ++ rest1
              then
                match
                  p_bind
                    st11
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st12.
                       lam x17.
                         match x17 with true
                         then
                           p_map
                             st12
                             (lam x18.
                                snoc x18 (addi i21 1))
                             acc22
                         else
                           (st12, acc22))
                    e3
                with
                  (st13, x19)
                in
                work1 st13 x19 (addi i21 1) rest1
              else
                (st11, acc22)
  in
  let whichTrue =
    lam s63.
      match s63 with [ e24 ] ++ rest4
      then
        work (anon "" 0 e24) (addi 0 1) rest4
      else
        ""
  in
  let whichTrue1 =
    lam st642.
      lam s62.
        match s62 with [ e20 ] ++ rest3
        then
          match
            p_map
              st642
              (lam x1024.
                 match x1024 with true
                 then
                   snoc "" (addi 0 1)
                 else
                   "")
              e20
          with
            (st643, x1025)
          in
          work1 st643 x1025 (addi 0 1) rest3
        else
          p_traverseSeq
            st642
            (lam st644.
               lam x1026.
                 (st644, x1026))
            ""
  in
  let whichTrue2 =
    lam st641.
      lam s61.
        p_map
          st641
          (lam x1023.
             match x1023 with [ e19 ] ++ rest2
             then
               work (anon "" 0 e19) (addi 0 1) rest2
             else
               "")
          s61
  in
  let bool2real =
    lam st640.
      lam v.
        p_map
          st640
          (lam x1022.
             match x1022 with true
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
          let a701 = externalExtArrMakeUninit extArrKindFloat64 (length data1)
          in
          let #var"1914" = rec1 a701 0 data1 in
          let #var"1711" = {} in
          let a631 = a701 in
          match eqi (muli rows1 cols12) (externalExtArrLength a631) with true
          then
            { arr = a631, n = cols12, m = rows1 }
          else
            error "matFromArrExn: dimensions mismatch"
  in
  let mtxCreate1 =
    lam st638.
      lam rows.
        lam cols11.
          lam data.
            let a70 = externalExtArrMakeUninit extArrKindFloat64 (length data)
            in
            match rec11 st638 a70 0 data with (st639, #var"1913")
            in
            let #var"1710" = {} in
            let a63 = a70 in
            (st639, match eqi (muli rows cols11) (externalExtArrLength a63) with true
            then
              { arr = a63, n = cols11, m = rows }
            else
              error "matFromArrExn: dimensions mismatch")
  in
  let mtxGet =
    lam row13.
      lam col2.
        lam mtx62.
          matGetExn mtx62 (subi row13 1) (subi col2 1)
  in
  let mtxGet1 =
    lam st636.
      lam row12.
        lam col1.
          lam mtx61.
            match
              p_map st636 (lam x1020.
                   subi x1020 1) row12
            with
              (st637, x1021)
            in
            matGetExn1 st637 mtx61 x1021 (subi col1 1)
  in
  let mtxGet2 =
    lam st632.
      lam row11.
        lam col.
          lam mtx6.
            match
              p_map st632 (lam x1013.
                   subi x1013 1) row11
            with
              (st633, x1014)
            in
            match
              p_map
                st633
                (lam x1015.
                   lam x1016.
                     match mtx6 with {arr = #var"X72"}
                     in
                     match mtx6 with {n = #var"X73"}
                     in
                     externalExtArrGet #var"X72" (addi (muli x1015 #var"X73") x1016))
                x1014
            with
              (st634, x1017)
            in
            match
              p_map st634 (lam x1018.
                   subi x1018 1) col
            with
              (st635, x1019)
            in
            p_apply st635 x1017 x1019
  in
  let anon1 =
    lam new5.
      lam mtx55.
        lam row5.
          lam x1011.
            lam x1012.
              match new5 with {arr = #var"X70"}
              in
              match new5 with {n = #var"X71"}
              in
              externalExtArrSet
                #var"X70"
                (addi (muli 0 #var"X71") x1011)
                (matGetExn mtx55 (subi row5 1) (subi x1012 1))
  in
  let anon2 =
    lam st629.
      lam new4.
        lam mtx54.
          lam row4.
            lam x1004.
              lam x1005.
                match new4 with {arr = #var"X68"}
                in
                match
                  p_map
                    st629
                    (lam x1006.
                       lam x1007.
                         externalExtArrSet x1006 x1007 (matGetExn mtx54 (subi row4 1) (subi x1005 1)))
                    #var"X68"
                with
                  (st630, x1008)
                in
                match new4 with {n = #var"X69"}
                in
                match
                  p_map
                    st630
                    (lam x1009.
                       addi (muli 0 x1009) x1004)
                    #var"X69"
                with
                  (st631, x1010)
                in
                p_apply st631 x1008 x1010
  in
  let anon3 =
    lam st623.
      lam new3.
        lam mtx53.
          lam row3.
            lam x992.
              lam x993.
                match new3 with {arr = #var"X66"}
                in
                match
                  p_map
                    st623
                    (lam x994.
                       lam x995.
                         lam x996.
                           externalExtArrSet x994 x995 x996)
                    #var"X66"
                with
                  (st624, x997)
                in
                match new3 with {n = #var"X67"}
                in
                match
                  p_map
                    st624
                    (lam x998.
                       addi (muli 0 x998) x992)
                    #var"X67"
                with
                  (st625, x999)
                in
                match p_apply st625 x997 x999 with (st626, x1000)
                in
                match
                  p_map st626 (lam x1001.
                       subi x1001 1) row3
                with
                  (st627, x1002)
                in
                match matGetExn1 st627 mtx53 x1002 (subi x993 1) with (st628, x1003)
                in
                p_apply st628 x1000 x1003
  in
  recursive
    let rec12 =
      lam c2.
        lam c3.
          lam c4.
            lam i3.
              lam s12.
                match s12 with [ _,
                    _ ] ++ _
                then
                  match splitAt s12 1 with {#label"1" = x20}
                  in
                  cons
                    (anon1 c2 c3 c4 i3 (get s12 0))
                    (rec12 c2 c3 c4 (addi i3 1) x20)
                else match s12 with [ e4 ]
                then
                  match splitAt s12 1 with {#label"1" = x21}
                  in
                  let slice3 = x21 in
                  [ anon1 c2 c3 c4 i3 e4 ]
                else match s12 with ""
                in
                ""
    let rec13 =
      lam st14.
        lam c5.
          lam c6.
            lam c7.
              lam i4.
                lam s13.
                  match s13 with [ _,
                      _ ] ++ _
                  then
                    match anon2 st14 c5 c6 c7 i4 (get s13 0) with (st15, x22)
                    in
                    match splitAt s13 1 with {#label"1" = x23}
                    in
                    match rec13 st15 c5 c6 c7 (addi i4 1) x23 with (st16, x24)
                    in
                    (st16, cons x22 x24)
                  else match s13 with [ e5 ]
                  then
                    match splitAt s13 1 with {#label"1" = x25}
                    in
                    let slice4 = x25 in
                    match anon2 st14 c5 c6 c7 i4 e5 with (st17, x26)
                    in
                    (st17, [ x26 ])
                  else match s13 with ""
                  in
                  (st14, "")
    let rec14 =
      lam st18.
        lam c8.
          lam c9.
            lam c10.
              lam i5.
                lam s14.
                  match s14 with [ _,
                      _ ] ++ _
                  then
                    match anon3 st18 c8 c9 c10 i5 (get s14 0) with (st19, x27)
                    in
                    match splitAt s14 1 with {#label"1" = x28}
                    in
                    match rec14 st19 c8 c9 c10 (addi i5 1) x28 with (st20, x29)
                    in
                    (st20, cons x27 x29)
                  else match s14 with [ e6 ]
                  then
                    match splitAt s14 1 with {#label"1" = x30}
                    in
                    let slice5 = x30 in
                    match anon3 st18 c8 c9 c10 i5 e6 with (st21, x31)
                    in
                    (st21, [ x31 ])
                  else match s14 with ""
                  in
                  (st18, "")
  in
  let mtxRowCols =
    lam mtx52.
      lam row2.
        lam cols2.
          match mtx52 with {arr = #var"X65"}
          in
          let new2 =
            matMakeUninit (externalExtArrKind #var"X65") 1 (length cols2)
          in
          let #var"1912" = rec12 new2 mtx52 row2 0 cols2 in
          let #var"92" = {} in
          new2
  in
  let mtxRowCols1 =
    lam st613.
      lam mtx51.
        lam row1.
          lam cols1.
            match mtx51 with {arr = #var"X64"}
            in
            match p_map st613 length cols1 with (st614, x983)
            in
            match
              matMakeUninit1 st614 (externalExtArrKind #var"X64") 1 x983
            with
              (st615, new1)
            in
            match
              p_bind
                st615
                hrmStoreSubmodel
                (hrmInit {})
                (lam st616.
                   lam x984.
                     match
                       match x984 with [ _,
                           _ ] ++ _
                       then
                         match anon2 st616 new1 mtx51 row1 0 (get x984 0) with (st617, x985)
                         in
                         match splitAt x984 1 with {#label"1" = x986}
                         in
                         match rec13 st617 new1 mtx51 row1 (addi 0 1) x986 with (st618, x987)
                         in
                         (st618, cons x985 x987)
                       else match x984 with [ e18 ]
                       then
                         match splitAt x984 1 with {#label"1" = x988}
                         in
                         let slice17 = x988 in
                         match anon2 st616 new1 mtx51 row1 0 e18 with (st619, x989)
                         in
                         (st619, [ x989 ])
                       else match x984 with ""
                       in
                       (st616, "")
                     with
                       (st620, x990)
                     in
                     p_traverseSeq
                       st620
                       (lam st621.
                          lam x991.
                            (st621, x991))
                       x990)
                cols1
            with
              (st622, #var"1911")
            in
            let #var"91" = {} in
            (st622, new1)
  in
  let mtxRowCols2 =
    lam st603.
      lam mtx5.
        lam row.
          lam cols.
            match mtx5 with {arr = #var"X63"}
            in
            match p_map st603 length cols with (st604, x974)
            in
            match
              matMakeUninit1 st604 (externalExtArrKind #var"X63") 1 x974
            with
              (st605, new)
            in
            match
              p_bind
                st605
                hrmStoreSubmodel
                (hrmInit {})
                (lam st606.
                   lam x975.
                     match
                       match x975 with [ _,
                           _ ] ++ _
                       then
                         match anon3 st606 new mtx5 row 0 (get x975 0) with (st607, x976)
                         in
                         match splitAt x975 1 with {#label"1" = x977}
                         in
                         match rec14 st607 new mtx5 row (addi 0 1) x977 with (st608, x978)
                         in
                         (st608, cons x976 x978)
                       else match x975 with [ e17 ]
                       then
                         match splitAt x975 1 with {#label"1" = x979}
                         in
                         let slice16 = x979 in
                         match anon3 st606 new mtx5 row 0 e17 with (st609, x980)
                         in
                         (st609, [ x980 ])
                       else match x975 with ""
                       in
                       (st606, "")
                     with
                       (st610, x981)
                     in
                     p_traverseSeq
                       st610
                       (lam st611.
                          lam x982.
                            (st611, x982))
                       x981)
                cols
            with
              (st612, #var"1910")
            in
            let #var"9" = {} in
            (st612, new)
  in
  let mtxSclrMul =
    lam scalar.
      lam mtx41.
        match mtx41 with {m = #var"X57"}
        in
        let m21 = #var"X57" in
        match mtx41 with {n = #var"X58"}
        in
        let n31 = #var"X58" in
        match mtx41 with {arr = #var"X59"}
        in
        let b141 = matMakeUninit (externalExtArrKind #var"X59") m21 n31
        in
        let mn1 = muli m21 n31 in
        match mtx41 with {arr = #var"X60"}
        in
        match b141 with {arr = #var"X61"}
        in
        let #var"1163" = externalCblasCopy mn1 #var"X60" 1 #var"X61" 1
        in
        match b141 with {arr = #var"X62"}
        in
        let #var"1211" = externalCblasScal mn1 scalar #var"X62" 1 in
        b141
  in
  let mtxTrans =
    lam mtx3.
      match mtx3 with {arr = #var"X46"}
      in
      match mtx3 with {n = #var"X47"}
      in
      match mtx3 with {m = #var"X48"}
      in
      let b17 =
        matMakeUninit (externalExtArrKind #var"X46") #var"X47" #var"X48"
      in
      match mtx3 with {m = #var"X49"}
      in
      match b17 with {n = #var"X50"}
      in
      match mtx3 with {n = #var"X51"}
      in
      match b17 with {m = #var"X52"}
      in
      let #var"1410" =
        match and (eqi #var"X49" #var"X50") (eqi #var"X51" #var"X52") with true
        then
          match mtx3 with {m = #var"X53"}
          in
          match mtx3 with {n = #var"X54"}
          in
          match mtx3 with {arr = #var"X55"}
          in
          match b17 with {arr = #var"X56"}
          in
          let #var"1610" = externalMatTranspose #var"X53" #var"X54" #var"X55" #var"X56"
          in
          Right
            {}
        else
          Left
            (DimensionMismatch
               {})
      in
      b17
  in
  let mtxExp =
    lam mtx2.
      match mtx2 with {m = #var"X41"}
      in
      match mtx2 with {n = #var"X42"}
      in
      let e23 =
        match eqi #var"X41" #var"X42" with true
        then
          match mtx2 with {m = #var"X43"}
          in
          match mtx2 with {n = #var"X44"}
          in
          match mtx2 with {arr = #var"X45"}
          in
          Right
            { mtx2 with arr = externalMatExp #var"X43" #var"X44" #var"X45" }
        else
          Left
            (NotSquare
               {})
      in
      match e23 with Left carried72
      then
        match carried72 with NotSquare carried73
        in
        error "Not square"
      else match e23 with Right carried74
      in
      carried74
  in
  let mtxMul =
    lam a37.
      lam b5.
        match a37 with {m = #var"X33"}
        in
        let m1 = #var"X33" in
        match b5 with {n = #var"X34"}
        in
        let n2 = #var"X34" in
        match a37 with {n = #var"X35"}
        in
        let k2 = #var"X35" in
        match b5 with {m = #var"X36"}
        in
        let e22 =
          match eqi k2 #var"X36" with true
          then
            match b5 with {arr = #var"X37"}
            in
            let c210 = matMakeUninit (externalExtArrKind #var"X37") m1 n2
            in
            match a37 with {arr = #var"X38"}
            in
            match b5 with {arr = #var"X39"}
            in
            match c210 with {arr = #var"X40"}
            in
            let #var"10" =
              externalCblasGemm
                cblasRowMajor
                cblasNoTrans
                cblasNoTrans
                m1
                n2
                k2
                1.
                #var"X38"
                k2
                #var"X39"
                n2
                0.
                #var"X40"
                n2
            in
            Right
              c210
          else
            Left
              (DimensionMismatch
                 {})
        in
        match e22 with Left carried70
        then
          error (matErrorToString carried70)
        else match e22 with Right carried71
        in
        carried71
  in
  let mtxElemMul =
    lam a36.
      lam b4.
        let e21 =
          match matHasSameShape2 a36 b4 with true
          then
            match a36 with {arr = #var"X25"}
            in
            match a36 with {m = #var"X26"}
            in
            match a36 with {n = #var"X27"}
            in
            let c310 =
              matMakeUninit (externalExtArrKind #var"X25") #var"X26" #var"X27"
            in
            let #var"1310" =
              match and (matHasSameShape2 a36 b4) (matHasSameShape2 b4 c310) with true
              then
                match a36 with {m = #var"X28"}
                in
                match a36 with {n = #var"X29"}
                in
                match a36 with {arr = #var"X30"}
                in
                match b4 with {arr = #var"X31"}
                in
                match c310 with {arr = #var"X32"}
                in
                let #var"1510" =
                  externalMatElemMul #var"X28" #var"X29" #var"X30" #var"X31" #var"X32"
                in
                Right
                  {}
              else
                Left
                  (DimensionMismatch
                     {})
            in
            Right
              c310
          else
            Left
              (DimensionMismatch
                 {})
        in
        match e21 with Left carried68
        then
          error (matErrorToString carried68)
        else match e21 with Right carried69
        in
        carried69
  in
  recursive
    let work2 =
      lam bound.
        lam c11.
          lam i31.
            lam acc31.
              match lti i31 bound with true
              then
                match c11 with {arr = #var"X"}
                in
                work2
                  bound
                  c11
                  (addi i31 1)
                  (addf acc31 (externalExtArrGet #var"X" i31))
              else
                acc31
    let work21 =
      lam st22.
        lam bound1.
          lam c12.
            lam i32.
              lam acc32.
                match lti i32 bound1 with true
                then
                  match
                    p_map
                      st22
                      (lam x32.
                         lam x33.
                           addf x32 x33)
                      acc32
                  with
                    (st23, x34)
                  in
                  match c12 with {arr = #var"X1"}
                  in
                  match
                    p_map
                      st23
                      (lam x35.
                         externalExtArrGet x35 i32)
                      #var"X1"
                  with
                    (st24, x36)
                  in
                  match p_apply st24 x34 x36 with (st25, x37)
                  in
                  work21 st25 bound1 c12 (addi i32 1) x37
                else
                  (st22, acc32)
  in
  let mtxMean =
    lam mtx11.
      match mtx11 with {m = #var"X21"}
      in
      match mtx11 with {n = #var"X22"}
      in
      match mtx11 with {m = #var"X23"}
      in
      match mtx11 with {n = #var"X24"}
      in
      divf
        (work2 (muli #var"X21" #var"X22") mtx11 0 0.)
        (int2float (muli #var"X23" #var"X24"))
  in
  let mtxMean1 =
    lam st596.
      lam mtx1.
        match mtx1 with {n = #var"X16"}
        in
        match
          p_map
            st596
            (lam x963.
               match mtx1 with {m = #var"X17"}
               in
               muli #var"X17" x963)
            #var"X16"
        with
          (st597, x964)
        in
        match
          p_bind
            st597
            hrmStoreSubmodel
            (hrmInit {})
            (lam st598.
               lam x965.
                 match lti 0 x965 with true
                 then
                   match mtx1 with {arr = #var"X18"}
                   in
                   match
                     p_map
                       st598
                       (lam x966.
                          addf 0. (externalExtArrGet x966 0))
                       #var"X18"
                   with
                     (st599, x967)
                   in
                   work21 st599 x965 mtx1 (addi 0 1) x967
                 else
                   (st598, p_pure 0.))
            x964
        with
          (st600, x968)
        in
        match
          p_map
            st600
            (lam x969.
               lam x970.
                 divf x969 x970)
            x968
        with
          (st601, x971)
        in
        match mtx1 with {n = #var"X19"}
        in
        match
          p_map
            st601
            (lam x972.
               match mtx1 with {m = #var"X20"}
               in
               int2float (muli #var"X20" x972))
            #var"X19"
        with
          (st602, x973)
        in
        p_apply st602 x971 x973
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
      lam st26.
        lam seq.
          match null seq with true
          then
            (st26, p_pure false)
          else match
            p_map st26 (lam x38.
                 eqi x38 2) (head seq)
          with
            (st27, x39)
          in
          p_bind
            st27
            hrmStoreSubmodel
            (hrmInit {})
            (lam st28.
               lam x40.
                 match x40 with true
                 then
                   (st28, p_pure true)
                 else
                   any st28 (tail seq))
            x39
  in
  let any1 = lam st595.
      lam l21.
        any st595 l21 in
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
    lam st577.
      lam currRep81.
        lam event31.
          lam nhosts81.
            match
              p_map
                st577
                (lam x939.
                   match x939 with Event1 x1532
                   then
                     x1532.host
                   else
                     let #var"1161" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event31
            with
              (st578, hostIndex42)
            in
            match
              p_traverseSeq
                st578
                (lam st579.
                   lam x940.
                     (st579, x940))
                currRep81
            with
              (st580, x942)
            in
            match
              p_map
                st580
                (lam x943.
                   subsequence x943 (subi 1 1))
                x942
            with
              (st581, x944)
            in
            match
              p_map
                st581 (lam x945.
                   subi x945 1) hostIndex42
            with
              (st582, x946)
            in
            match p_apply st582 x944 x946 with (st583, x947)
            in
            match
              p_map
                st583
                (lam x948.
                   match x948 with Event1 x1522
                   then
                     x1522.toState
                   else
                     let #var"1162" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event31
            with
              (st584, x949)
            in
            match
              p_traverseSeq
                st584
                (lam st585.
                   lam x950.
                     (st585, x950))
                [ x949 ]
            with
              (st586, x952)
            in
            match
              p_map
                st586 (lam x953.
                   addi x953 1) hostIndex42
            with
              (st587, first1)
            in
            match
              p_traverseSeq
                st587
                (lam st588.
                   lam x954.
                     (st588, x954))
                currRep81
            with
              (st589, x955)
            in
            match p_map st589 subsequence x955 with (st590, x956)
            in
            match
              p_map st590 (lam x957.
                   subi x957 1) first1
            with
              (st591, x958)
            in
            match p_apply st591 x956 x958 with (st592, x959)
            in
            match
              p_map
                st592
                (lam x960.
                   subi (addi nhosts81 1) x960)
                first1
            with
              (st593, x961)
            in
            match p_apply st593 x959 x961 with (st594, x962)
            in
            paste01 st594 [ x947,
                x952,
                x962 ]
  in
  let updateRepertoire1 =
    lam st563.
      lam currRep8.
        lam event3.
          lam nhosts8.
            match
              p_map
                st563
                (lam x921.
                   match x921 with Event1 x1531
                   then
                     x1531.host
                   else
                     let #var"1159" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event3
            with
              (st564, hostIndex41)
            in
            match
              p_map
                st564
                (lam x922.
                   subsequence x922 (subi 1 1))
                currRep8
            with
              (st565, x923)
            in
            match
              p_map
                st565 (lam x924.
                   subi x924 1) hostIndex41
            with
              (st566, x925)
            in
            match p_apply st566 x923 x925 with (st567, x926)
            in
            match
              p_map
                st567
                (lam x927.
                   match x927 with Event1 x1521
                   then
                     x1521.toState
                   else
                     let #var"1160" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event3
            with
              (st568, x928)
            in
            match
              p_traverseSeq
                st568
                (lam st569.
                   lam x929.
                     (st569, x929))
                [ x928 ]
            with
              (st570, x930)
            in
            match
              p_map
                st570 (lam x931.
                   addi x931 1) hostIndex41
            with
              (st571, first)
            in
            match p_map st571 subsequence currRep8 with (st572, x932)
            in
            match
              p_map st572 (lam x933.
                   subi x933 1) first
            with
              (st573, x934)
            in
            match p_apply st573 x932 x934 with (st574, x935)
            in
            match
              p_map
                st574
                (lam x936.
                   subi (addi nhosts8 1) x936)
                first
            with
              (st575, x937)
            in
            match p_apply st575 x935 x937 with (st576, x938)
            in
            paste01 st576 [ x926,
                x930,
                x938 ]
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
      lam c13.
        lam s.
          match s with [ _,
              _ ] ++ _
          then
            match splitAt s 1 with {#label"1" = x41}
            in
            cons (anon4 c13 (get s 0)) (rec c13 x41)
          else match s with [ e7 ]
          then
            match splitAt s 1 with {#label"1" = x42}
            in
            let slice6 = x42 in
            [ anon4 c13 e7 ]
          else match s with ""
          in
          ""
    let map1 = lam c14.
        lam s141.
          rec c14 s141
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
        lam x43.
          match eqi (subi (addi interaction 1) 1) x43 with true
          then
            1.
          else
            0.
    let anon5 = lam x44.
        1.
    let observationMessage =
      lam obsRepertoire.
        lam i41.
          lam max.
            match leqi i41 max with true
            then
              let interaction1 = get obsRepertoire (subi i41 1) in
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
                      (observationMessage obsRepertoire (addi i41 1) max)))
            else
              ""
    let observationMessage1 =
      lam st29.
        lam obsRepertoire1.
          lam i42.
            lam max1.
              match leqi i42 max1 with true
              then
                match
                  p_map
                    st29
                    (lam x45.
                       match
                         match geqi x45 0 with true
                         then
                           leqi x45 2
                         else
                           false
                       with
                         true
                       then
                         map1 x45 (unfoldr 0)
                       else
                         create1 3)
                    (get obsRepertoire1 (subi i42 1))
                with
                  (st30, stateMsg1)
                in
                match
                  p_map
                    st30
                    (lam x46.
                       get x46 (subi 1 1))
                    stateMsg1
                with
                  (st31, x47)
                in
                match
                  p_map
                    st31
                    (lam x48.
                       get x48 (subi 2 1))
                    stateMsg1
                with
                  (st32, x49)
                in
                match
                  p_map
                    st32
                    (lam x50.
                       get x50 (subi 3 1))
                    stateMsg1
                with
                  (st33, x51)
                in
                match
                  observationMessage1 st33 obsRepertoire1 (addi i42 1) max1
                with
                  (st34, x52)
                in
                (st34, cons12 x47 (cons12 x49 (cons12 x51 x52)))
              else
                (st29, "")
  in
  recursive
    let postorderTraverse =
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
                MsgLeaf
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
                      mtxCreate nhosts1 3 (observationMessage leafInts 1 nhosts1) }
              else
                let left =
                  postorderTraverse
                    (match tree1 with Node x231
                     then
                       x231.left
                     else
                       let #var"112" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 19:31-19:40>:\nField \'left\' not found\n[0m  let left = postorderTraverse([31mtree.left[0m[0m, qMatrix, interactions, nhosts);\n"
                       in
                       exit 1)
                    qMatrix1
                    interactions1
                    nhosts1
                in
                let right =
                  postorderTraverse
                    (match tree1 with Node x221
                     then
                       x221.right
                     else
                       let #var"111" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 20:32-20:42>:\nField \'right\' not found\n[0m  let right = postorderTraverse([31mtree.right[0m[0m, qMatrix, interactions, nhosts);\n"
                       in
                       exit 1)
                    qMatrix1
                    interactions1
                    nhosts1
                in
                let leftKernel =
                  mtxExp
                    (mtxSclrMul
                       (subf
                          (match tree1 with Leaf carried20
                           then
                             carried20.age
                           else match tree1 with Node carried21
                           then
                             carried21.age
                           else
                             let #var"19" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:37-23:45>:\nField \'age\' not found\n[0m  let leftKernel = mtxExp(mtxSclrMul([31mtree.age[0m[0m-left.age, qMatrix));\n"
                             in
                             exit 1)
                          (match left with MsgLeaf carried22
                           then
                             carried22.age
                           else match left with MsgNode carried23
                           then
                             carried23.age
                           else
                             let #var"110" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:46-23:54>:\nField \'age\' not found\n[0m  let leftKernel = mtxExp(mtxSclrMul(tree.age-[31mleft.age[0m[0m, qMatrix));\n"
                             in
                             exit 1))
                       qMatrix1)
                in
                let rightKernel =
                  mtxExp
                    (mtxSclrMul
                       (subf
                          (match tree1 with Leaf carried16
                           then
                             carried16.age
                           else match tree1 with Node carried17
                           then
                             carried17.age
                           else
                             let #var"17" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:38-24:46>:\nField \'age\' not found\n[0m  let rightKernel = mtxExp(mtxSclrMul([31mtree.age[0m[0m-right.age, qMatrix));\n"
                             in
                             exit 1)
                          (match right with MsgLeaf carried18
                           then
                             carried18.age
                           else match right with MsgNode carried19
                           then
                             carried19.age
                           else
                             let #var"18" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:47-24:56>:\nField \'age\' not found\n[0m  let rightKernel = mtxExp(mtxSclrMul(tree.age-[31mright.age[0m[0m, qMatrix));\n"
                             in
                             exit 1))
                       qMatrix1)
                in
                let leftInMsg =
                  mtxMul
                    (match left with MsgLeaf carried14
                     then
                       carried14.outMsg
                     else match left with MsgNode carried15
                     then
                       carried15.outMsg
                     else
                       let #var"16" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:25-30:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n"
                       in
                       exit 1)
                    (mtxTrans leftKernel)
                in
                let rightInMsg =
                  mtxMul
                    (match right with MsgLeaf carried12
                     then
                       carried12.outMsg
                     else match right with MsgNode carried13
                     then
                       carried13.outMsg
                     else
                       let #var"15" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 31:26-31:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n"
                       in
                       exit 1)
                    (mtxTrans rightKernel)
                in
                MsgNode
                  { age =
                      match tree1 with Leaf carried8
                      then
                        carried8.age
                      else match tree1 with Node carried9
                      then
                        carried9.age
                      else
                        let #var"13" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:10-36:18>:\nField \'age\' not found\n[0m    age = [31mtree.age[0m[0m, label = tree.label,\n"
                        in
                        exit 1,
                    label =
                      match tree1 with Leaf carried10
                      then
                        carried10.label
                      else match tree1 with Node carried11
                      then
                        carried11.label
                      else
                        let #var"14" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:28-36:38>:\nField \'label\' not found\n[0m    age = tree.age, label = [31mtree.label[0m[0m,\n"
                        in
                        exit 1,
                    left = left,
                    right = right,
                    rightKernel = rightKernel,
                    leftKernel = leftKernel,
                    outMsg = mtxElemMul leftInMsg rightInMsg,
                    leftInMsg = leftInMsg,
                    rightInMsg = rightInMsg }
  in
  let mtx3ToSeq =
    lam mtx.
      lam i115.
        let p111 = mtxGet i115 1 mtx in
        let p210 = mtxGet i115 2 mtx in
        let p310 = mtxGet i115 3 mtx in
        let s51 = addf (addf p111 p210) p310 in
        [ divf p111 s51,
          divf p210 s51,
          divf p310 s51 ]
  in
  recursive
    let rec24 =
      lam st35.
        lam c15.
          lam c16.
            lam acc4.
              lam s24.
                match s24 with [ _ ] ++ _
                then
                  let x53 = get s24 0 in
                  match
                    p_map
                      st35
                      (lam x54.
                         lam x55.
                           addf x54 x55)
                      acc4
                  with
                    (st36, x56)
                  in
                  let params = mtx3ToSeq c16 x53 in
                  match
                    p_map
                      st36
                      (lam x57.
                         match
                           match geqi x57 0 with true
                           then
                             lti x57 (length1 params)
                           else
                             false
                         with
                           true
                         then
                           log1 (get params (subi (addi x57 1) 1))
                         else
                           log1 0.)
                      (get c15 (subi x53 1))
                  with
                    (st37, x58)
                  in
                  match p_apply st37 x56 x58 with (st38, x59)
                  in
                  match splitAt s24 1 with {#label"1" = x60}
                  in
                  rec24 st38 c15 c16 x59 x60
                else match s24 with ""
                in
                (st35, acc4)
  in
  let anon6 = lam x920.
      addi x920 1 in
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
    lam st560.
      lam x1481.
        lam samplingProb1.
          lam nhosts7.
            let i114 = subi (addi (subi nhosts7 1) 1) 1 in
            let s226 =
              match geqi i114 0 with true
              then
                rec31 (subi i114 1) (cons (anon6 i114) "")
              else
                ""
            in
            match s226 with [ _ ] ++ _
            then
              let x914 = get s226 0 in
              let params1 = mtx3ToSeq samplingProb1 x914 in
              match
                p_map
                  st560
                  (lam x915.
                     match
                       match geqi x915 0 with true
                       then
                         lti x915 (length1 params1)
                       else
                         false
                     with
                       true
                     then
                       log1 (get params1 (subi (addi x915 1) 1))
                     else
                       log1 0.)
                  (get x1481 (subi x914 1))
              with
                (st561, x916)
              in
              match
                p_map st561 (lam x917.
                     addf 0. x917) x916
              with
                (st562, x918)
              in
              match splitAt s226 1 with {#label"1" = x919}
              in
              rec24 st562 x1481 samplingProb1 x918 x919
            else match s226 with ""
            in
            (st560, p_pure 0.)
  in
  recursive
    let rec25 =
      lam st39.
        lam acc5.
          lam s25.
            match s25 with [ _ ] ++ _
            then
              match
                p_bind
                  st39
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st40.
                     lam x61.
                       match eqi x61 2 with true
                       then
                         p_map
                           st40 (lam x62.
                              addi x62 1) acc5
                       else
                         (st40, acc5))
                  (get s25 0)
              with
                (st41, x63)
              in
              match splitAt s25 1 with {#label"1" = x64}
              in
              rec25 st41 x63 x64
            else match s25 with ""
            in
            (st39, acc5)
    let fold =
      lam st42.
        lam init1.
          lam seq5.
            match seq5 with [ _ ] ++ _
            then
              match
                p_map
                  st42
                  (lam x65.
                     match eqi x65 2 with true
                     then
                       addi init1 1
                     else
                       init1)
                  (get seq5 0)
              with
                (st43, x66)
              in
              match splitAt seq5 1 with {#label"1" = x67}
              in
              rec25 st43 x66 x67
            else match seq5 with ""
            in
            (st42, p_pure init1)
    let ifCont3 =
      lam st44.
        lam currRep.
          lam eventSeq.
            lam eventIndex.
              lam nEvents.
                lam nhosts2.
                  lam event.
                    lam #var"2".
                      let hostIndex4 =
                        match event with Event1 x153
                        then
                          x153.host
                        else
                          let #var"115" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                          in
                          exit 1
                      in
                      let s26 =
                        [ slice2 currRep 1 hostIndex4,
                          [ p_pure
                              (match event with Event1 x152
                               then
                                 x152.toState
                               else
                                 let #var"114" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                                 in
                                 exit 1) ],
                          slice2 currRep (addi hostIndex4 1) (addi nhosts2 1) ]
                      in
                      let currRep1 =
                        match s26 with [ _ ] ++ _
                        then
                          match splitAt s26 1 with {#label"1" = x73}
                          in
                          rec21 (concat "" (get s26 0)) x73
                        else match s26 with ""
                        in
                        ""
                      in
                      let eventIndex1 = addi eventIndex 1 in
                      match gti eventIndex1 nEvents with true
                      then
                        (st44, p_pure true)
                      else match
                        p_map
                          st44
                          (lam x68.
                             get x68 (subi eventIndex1 1))
                          eventSeq
                      with
                        (st45, x69)
                      in
                      p_bind
                        st45
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st46.
                           lam x70.
                             match
                               eqi
                                 (match x70 with Event1 x301
                                  then
                                    x301.fromState
                                  else
                                    let #var"113" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 146:7-146:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                                    in
                                    exit 1)
                                 2
                             with
                               true
                             then
                               match fold st46 0 currRep1 with (st47, x71)
                               in
                               p_bind
                                 st47
                                 hrmStoreSubmodel
                                 (hrmInit {})
                                 (lam st48.
                                    lam x72.
                                      match eqi x72 1 with true
                                      then
                                        (st48, p_pure false)
                                      else
                                        ifCont3 st48 currRep1 eventSeq eventIndex1 nEvents nhosts2 x70 0)
                                 x71
                             else
                               ifCont3 st46 currRep1 eventSeq eventIndex1 nEvents nhosts2 x70 0)
                        x69
    let allTimesValidBranch =
      lam st49.
        lam currRep11.
          lam eventSeq1.
            lam eventIndex11.
              lam nEvents1.
                lam nhosts3.
                  p_bind
                    st49
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st50.
                       lam x74.
                         match gti eventIndex11 x74 with true
                         then
                           (st50, p_pure true)
                         else match
                           p_map
                             st50
                             (lam x75.
                                get x75 (subi eventIndex11 1))
                             eventSeq1
                         with
                           (st51, x76)
                         in
                         p_bind
                           st51
                           hrmStoreSubmodel
                           (hrmInit {})
                           (lam st52.
                              lam x77.
                                match
                                  eqi
                                    (match x77 with Event1 x302
                                     then
                                       x302.fromState
                                     else
                                       let #var"116" =
                                         print
                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 146:7-146:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                                       in
                                       exit 1)
                                    2
                                with
                                  true
                                then
                                  match fold st52 0 currRep11 with (st53, x78)
                                  in
                                  p_bind
                                    st53
                                    hrmStoreSubmodel
                                    (hrmInit {})
                                    (lam st54.
                                       lam x79.
                                         match eqi x79 1 with true
                                         then
                                           (st54, p_pure false)
                                         else
                                           ifCont3 st54 currRep11 eventSeq1 eventIndex11 x74 nhosts3 x77 0)
                                    x78
                                else
                                  ifCont3 st52 currRep11 eventSeq1 eventIndex11 x74 nhosts3 x77 0)
                           x76)
                    nEvents1
  in
  let anon7 =
    lam x913.
      match eqi x913 2 with true
      then
        true
      else
        eqi x913 1
  in
  let anon8 =
    lam st559.
      lam x910.
        p_map
          st559
          (lam x912.
             match eqi x912 2 with true
             then
               true
             else
               eqi x912 1)
          x910
  in
  recursive
    let rec4 =
      lam s4.
        match s4 with [ _,
            _ ] ++ _
        then
          match splitAt s4 1 with {#label"1" = x80}
          in
          cons (anon7 (get s4 0)) (rec4 x80)
        else match s4 with [ e8 ]
        then
          match splitAt s4 1 with {#label"1" = x81}
          in
          let slice7 = x81 in
          [ anon7 e8 ]
        else match s4 with ""
        in
        ""
    let rec5 =
      lam st55.
        lam s5.
          match s5 with [ _,
              _ ] ++ _
          then
            match anon8 st55 (get s5 0) with (st56, x82)
            in
            match splitAt s5 1 with {#label"1" = x83}
            in
            match rec5 st56 x83 with (st57, x84)
            in
            (st57, cons x82 x84)
          else match s5 with [ e9 ]
          then
            match splitAt s5 1 with {#label"1" = x85}
            in
            let slice8 = x85 in
            match anon8 st55 e9 with (st58, x86)
            in
            (st58, [ x86 ])
          else match s5 with ""
          in
          (st55, "")
  in
  let sapply = lam st558.
      lam s72.
        rec5 st558 s72
  in
  let anon9 = lam x909.
      eqi x909 2 in
  let anon10 =
    lam st557.
      lam x907.
        p_map st557 (lam x908.
             eqi x908 2) x907
  in
  recursive
    let rec6 =
      lam s6.
        match s6 with [ _,
            _ ] ++ _
        then
          match splitAt s6 1 with {#label"1" = x87}
          in
          cons (anon9 (get s6 0)) (rec6 x87)
        else match s6 with [ e10 ]
        then
          match splitAt s6 1 with {#label"1" = x88}
          in
          let slice9 = x88 in
          [ anon9 e10 ]
        else match s6 with ""
        in
        ""
    let rec7 =
      lam st59.
        lam s7.
          match s7 with [ _,
              _ ] ++ _
          then
            match anon10 st59 (get s7 0) with (st60, x89)
            in
            match splitAt s7 1 with {#label"1" = x90}
            in
            match rec7 st60 x90 with (st61, x91)
            in
            (st61, cons x89 x91)
          else match s7 with [ e11 ]
          then
            match splitAt s7 1 with {#label"1" = x92}
            in
            let slice10 = x92 in
            match anon10 st59 e11 with (st62, x93)
            in
            (st62, [ x93 ])
          else match s7 with ""
          in
          (st59, "")
  in
  let sapply1 = lam st556.
      lam s71.
        rec7 st556 s71
  in
  let getGainRate =
    lam st551.
      lam repertoire14.
        lam hostIndex33.
          lam modelParams123.
            let fromState53 = get repertoire14 (subi hostIndex33 1) in
            let baseRate13 =
              mtxGet
                (addi fromState53 1)
                (addi (addi fromState53 1) 1)
                (match
                   match modelParams123 with ModelParams1 x1444
                   then
                     x1444.embeddedQMatrix
                   else
                     let #var"1157" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1434
                 then
                   x1434.mat
                 else
                   let #var"1158" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   exit 1)
            in
            match eqi fromState53 0 with true
            then
              match
                p_map
                  st551
                  (lam x898.
                     negf x898)
                  (match modelParams123 with ModelParams1 x1384
                   then
                     x1384.beta
                   else
                     let #var"1151" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                     in
                     p_pure (exit 1))
              with
                (st552, x899)
              in
              match
                pow1
                  st552
                  (divf
                     (mtxMean
                        (mtxRowCols
                           (match modelParams123 with ModelParams1 x1394
                            then
                              x1394.hostMetric
                            else
                              let #var"1152" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                              in
                              exit 1)
                           hostIndex33
                           (whichTrue (rec4 repertoire14))))
                     (match modelParams123 with ModelParams1 x1374
                      then
                        x1374.meanDist
                      else
                        let #var"1153" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                        in
                        exit 1))
                  x899
              with
                (st553, x900)
              in
              p_map
                st553
                (lam x902.
                   mulf baseRate13 x902)
                x900
            else match
              p_map
                st551
                (lam x903.
                   negf x903)
                (match modelParams123 with ModelParams1 x1414
                 then
                   x1414.beta
                 else
                   let #var"1154" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                   in
                   p_pure (exit 1))
            with
              (st554, x904)
            in
            match
              pow1
                st554
                (divf
                   (mtxMean
                      (mtxRowCols
                         (match modelParams123 with ModelParams1 x1424
                          then
                            x1424.hostMetric
                          else
                            let #var"1155" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex33
                         (whichTrue (rec6 repertoire14))))
                   (match modelParams123 with ModelParams1 x1404
                    then
                      x1404.meanDist
                    else
                      let #var"1156" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                      in
                      exit 1))
                x904
            with
              (st555, x905)
            in
            p_map
              st555 (lam x906.
                 mulf baseRate13 x906) x905
  in
  let getGainRate1 =
    lam st530.
      lam repertoire13.
        lam hostIndex32.
          lam modelParams122.
            let fromState52 = get repertoire13 (subi hostIndex32 1) in
            match
              p_map
                st530 (lam x867.
                   addi x867 1) fromState52
            with
              (st531, x868)
            in
            match
              p_map
                st531
                (lam x869.
                   addi (addi x869 1) 1)
                fromState52
            with
              (st532, x870)
            in
            match
              mtxGet2
                st532
                x868
                x870
                (match
                   match modelParams122 with ModelParams1 x1443
                   then
                     x1443.embeddedQMatrix
                   else
                     let #var"1143" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1433
                 then
                   x1433.mat
                 else
                   let #var"1144" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   exit 1)
            with
              (st533, baseRate12)
            in
            p_bind
              st533
              hrmStoreSubmodel
              (hrmInit {})
              (lam st534.
                 lam x871.
                   match eqi x871 0 with true
                   then
                     match
                       p_map
                         st534
                         (lam x872.
                            lam x873.
                              mulf x872 x873)
                         baseRate12
                     with
                       (st535, x874)
                     in
                     match sapply st535 repertoire13 with (st536, x875)
                     in
                     match whichTrue1 st536 x875 with (st537, x876)
                     in
                     match
                       mtxRowCols1
                         st537
                         (match modelParams122 with ModelParams1 x1393
                          then
                            x1393.hostMetric
                          else
                            let #var"1145" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex32
                         x876
                     with
                       (st538, x877)
                     in
                     match mtxMean1 st538 x877 with (st539, x878)
                     in
                     match
                       p_map
                         st539
                         (lam x879.
                            divf
                              x879
                              (match modelParams122 with ModelParams1 x1373
                               then
                                 x1373.meanDist
                               else
                                 let #var"1146" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x878
                     with
                       (st540, x880)
                     in
                     match
                       p_map
                         st540
                         (lam x882.
                            negf x882)
                         (match modelParams122 with ModelParams1 x1383
                          then
                            x1383.beta
                          else
                            let #var"1147" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st541, x883)
                     in
                     match pow2 st541 x880 x883 with (st542, x884)
                     in
                     p_apply st542 x874 x884
                   else match
                     p_map
                       st534
                       (lam x885.
                          lam x886.
                            mulf x885 x886)
                       baseRate12
                   with
                     (st543, x887)
                   in
                   match sapply1 st543 repertoire13 with (st544, x888)
                   in
                   match whichTrue1 st544 x888 with (st545, x889)
                   in
                   match
                     mtxRowCols1
                       st545
                       (match modelParams122 with ModelParams1 x1423
                        then
                          x1423.hostMetric
                        else
                          let #var"1148" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex32
                       x889
                   with
                     (st546, x890)
                   in
                   match mtxMean1 st546 x890 with (st547, x892)
                   in
                   match
                     p_map
                       st547
                       (lam x893.
                          divf
                            x893
                            (match modelParams122 with ModelParams1 x1403
                             then
                               x1403.meanDist
                             else
                               let #var"1149" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x892
                   with
                     (st548, x894)
                   in
                   match
                     p_map
                       st548
                       (lam x895.
                          negf x895)
                       (match modelParams122 with ModelParams1 x1413
                        then
                          x1413.beta
                        else
                          let #var"1150" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st549, x896)
                   in
                   match pow2 st549 x894 x896 with (st550, x897)
                   in
                   p_apply st550 x887 x897)
              fromState52
  in
  let getGainRate2 =
    lam st504.
      lam repertoire12.
        lam hostIndex31.
          lam modelParams121.
            match
              p_traverseSeq
                st504
                (lam st505.
                   lam x833.
                     (st505, x833))
                repertoire12
            with
              (st506, x834)
            in
            match p_map st506 get x834 with (st507, x835)
            in
            match
              p_map
                st507 (lam x836.
                   subi x836 1) hostIndex31
            with
              (st508, x837)
            in
            match p_apply st508 x835 x837 with (st509, fromState51)
            in
            match
              p_map
                st509 (lam x838.
                   addi x838 1) fromState51
            with
              (st510, x839)
            in
            match
              p_map
                st510
                (lam x840.
                   addi (addi x840 1) 1)
                fromState51
            with
              (st511, x841)
            in
            match
              mtxGet2
                st511
                x839
                x841
                (match
                   match modelParams121 with ModelParams1 x1442
                   then
                     x1442.embeddedQMatrix
                   else
                     let #var"1135" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1432
                 then
                   x1432.mat
                 else
                   let #var"1136" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   exit 1)
            with
              (st512, baseRate11)
            in
            p_bind
              st512
              hrmStoreSubmodel
              (hrmInit {})
              (lam st513.
                 lam x842.
                   match eqi x842 0 with true
                   then
                     match
                       p_map
                         st513
                         (lam x843.
                            lam x844.
                              mulf x843 x844)
                         baseRate11
                     with
                       (st514, x845)
                     in
                     match sapply st514 repertoire12 with (st515, x846)
                     in
                     match whichTrue1 st515 x846 with (st516, x847)
                     in
                     match
                       mtxRowCols2
                         st516
                         (match modelParams121 with ModelParams1 x1392
                          then
                            x1392.hostMetric
                          else
                            let #var"1137" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex31
                         x847
                     with
                       (st517, x848)
                     in
                     match mtxMean1 st517 x848 with (st518, x849)
                     in
                     match
                       p_map
                         st518
                         (lam x850.
                            divf
                              x850
                              (match modelParams121 with ModelParams1 x1372
                               then
                                 x1372.meanDist
                               else
                                 let #var"1138" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x849
                     with
                       (st519, x851)
                     in
                     match
                       p_map
                         st519
                         (lam x852.
                            negf x852)
                         (match modelParams121 with ModelParams1 x1382
                          then
                            x1382.beta
                          else
                            let #var"1139" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st520, x853)
                     in
                     match pow2 st520 x851 x853 with (st521, x854)
                     in
                     p_apply st521 x845 x854
                   else match
                     p_map
                       st513
                       (lam x855.
                          lam x856.
                            mulf x855 x856)
                       baseRate11
                   with
                     (st522, x857)
                   in
                   match sapply1 st522 repertoire12 with (st523, x858)
                   in
                   match whichTrue1 st523 x858 with (st524, x859)
                   in
                   match
                     mtxRowCols2
                       st524
                       (match modelParams121 with ModelParams1 x1422
                        then
                          x1422.hostMetric
                        else
                          let #var"1140" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex31
                       x859
                   with
                     (st525, x860)
                   in
                   match mtxMean1 st525 x860 with (st526, x861)
                   in
                   match
                     p_map
                       st526
                       (lam x862.
                          divf
                            x862
                            (match modelParams121 with ModelParams1 x1402
                             then
                               x1402.meanDist
                             else
                               let #var"1141" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x861
                   with
                     (st527, x863)
                   in
                   match
                     p_map
                       st527
                       (lam x864.
                          negf x864)
                       (match modelParams121 with ModelParams1 x1412
                        then
                          x1412.beta
                        else
                          let #var"1142" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st528, x865)
                   in
                   match pow2 st528 x863 x865 with (st529, x866)
                   in
                   p_apply st529 x857 x866)
              fromState51
  in
  let getGainRate3 =
    lam st480.
      lam repertoire11.
        lam hostIndex3.
          lam modelParams12.
            match p_map st480 get repertoire11 with (st481, x795)
            in
            match
              p_map st481 (lam x796.
                   subi x796 1) hostIndex3
            with
              (st482, x797)
            in
            match p_apply st482 x795 x797 with (st483, fromState5)
            in
            match
              p_map st483 (lam x798.
                   addi x798 1) fromState5
            with
              (st484, x799)
            in
            match
              p_map
                st484
                (lam x800.
                   addi (addi x800 1) 1)
                fromState5
            with
              (st485, x801)
            in
            match
              mtxGet2
                st485
                x799
                x801
                (match
                   match modelParams12 with ModelParams1 x1441
                   then
                     x1441.embeddedQMatrix
                   else
                     let #var"1127" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1431
                 then
                   x1431.mat
                 else
                   let #var"1128" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   exit 1)
            with
              (st486, baseRate1)
            in
            p_bind
              st486
              hrmStoreSubmodel
              (hrmInit {})
              (lam st487.
                 lam x802.
                   match eqi x802 0 with true
                   then
                     match
                       p_map
                         st487
                         (lam x803.
                            lam x804.
                              mulf x803 x804)
                         baseRate1
                     with
                       (st488, x805)
                     in
                     match
                       p_map
                         st488
                         (lam x806.
                            match x806 with [ _,
                                _ ] ++ _
                            then
                              match splitAt x806 1 with {#label"1" = x807}
                              in
                              cons (anon7 (get x806 0)) (rec4 x807)
                            else match x806 with [ e15 ]
                            then
                              match splitAt x806 1 with {#label"1" = x808}
                              in
                              let slice14 = x808 in
                              [ anon7 e15 ]
                            else match x806 with ""
                            in
                            "")
                         repertoire11
                     with
                       (st489, x809)
                     in
                     match whichTrue2 st489 x809 with (st490, x810)
                     in
                     match
                       mtxRowCols2
                         st490
                         (match modelParams12 with ModelParams1 x1391
                          then
                            x1391.hostMetric
                          else
                            let #var"1129" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex3
                         x810
                     with
                       (st491, x811)
                     in
                     match mtxMean1 st491 x811 with (st492, x812)
                     in
                     match
                       p_map
                         st492
                         (lam x813.
                            divf
                              x813
                              (match modelParams12 with ModelParams1 x1371
                               then
                                 x1371.meanDist
                               else
                                 let #var"1130" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x812
                     with
                       (st493, x814)
                     in
                     match
                       p_map
                         st493
                         (lam x815.
                            negf x815)
                         (match modelParams12 with ModelParams1 x1381
                          then
                            x1381.beta
                          else
                            let #var"1131" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st494, x816)
                     in
                     match pow2 st494 x814 x816 with (st495, x817)
                     in
                     p_apply st495 x805 x817
                   else match
                     p_map
                       st487
                       (lam x818.
                          lam x819.
                            mulf x818 x819)
                       baseRate1
                   with
                     (st496, x820)
                   in
                   match
                     p_map
                       st496
                       (lam x821.
                          match x821 with [ _,
                              _ ] ++ _
                          then
                            match splitAt x821 1 with {#label"1" = x822}
                            in
                            cons (anon9 (get x821 0)) (rec6 x822)
                          else match x821 with [ e16 ]
                          then
                            match splitAt x821 1 with {#label"1" = x823}
                            in
                            let slice15 = x823 in
                            [ anon9 e16 ]
                          else match x821 with ""
                          in
                          "")
                       repertoire11
                   with
                     (st497, x824)
                   in
                   match whichTrue2 st497 x824 with (st498, x825)
                   in
                   match
                     mtxRowCols2
                       st498
                       (match modelParams12 with ModelParams1 x1421
                        then
                          x1421.hostMetric
                        else
                          let #var"1132" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex3
                       x825
                   with
                     (st499, x826)
                   in
                   match mtxMean1 st499 x826 with (st500, x827)
                   in
                   match
                     p_map
                       st500
                       (lam x828.
                          divf
                            x828
                            (match modelParams12 with ModelParams1 x1401
                             then
                               x1401.meanDist
                             else
                               let #var"1133" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x827
                   with
                     (st501, x829)
                   in
                   match
                     p_map
                       st501
                       (lam x830.
                          negf x830)
                       (match modelParams12 with ModelParams1 x1411
                        then
                          x1411.beta
                        else
                          let #var"1134" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st502, x831)
                   in
                   match pow2 st502 x829 x831 with (st503, x832)
                   in
                   p_apply st503 x820 x832)
              fromState5
  in
  let anon11 =
    lam x793.
      lam x794.
        match eqi x794 2 with true
        then
          addi x793 1
        else
          x793
  in
  recursive
    let rec26 =
      lam acc6.
        lam s27.
          match s27 with [ _ ] ++ _
          then
            match splitAt s27 1 with {#label"1" = x94}
            in
            rec26 (anon11 acc6 (get s27 0)) x94
          else match s27 with ""
          in
          acc6
    let rec27 =
      lam st63.
        lam acc7.
          lam s28.
            match s28 with [ _ ] ++ _
            then
              match
                p_bind
                  st63
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st64.
                     lam x95.
                       match eqi x95 2 with true
                       then
                         p_map
                           st64 (lam x96.
                              addi x96 1) acc7
                       else
                         (st64, acc7))
                  (get s28 0)
              with
                (st65, x97)
              in
              match splitAt s28 1 with {#label"1" = x98}
              in
              rec27 st65 x97 x98
            else match s28 with ""
            in
            (st63, acc7)
  in
  let fold1 =
    lam st478.
      lam init12.
        lam seq52.
          match seq52 with [ _ ] ++ _
          then
            match
              p_map
                st478
                (lam x790.
                   match eqi x790 2 with true
                   then
                     addi init12 1
                   else
                     init12)
                (get seq52 0)
            with
              (st479, x791)
            in
            match splitAt seq52 1 with {#label"1" = x792}
            in
            rec27 st479 x791 x792
          else match seq52 with ""
          in
          (st478, p_pure init12)
  in
  let getLossRate =
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
            0.
          else
            mtxGet
              (addi fromState33 1)
              (addi (subi fromState33 1) 1)
              (match
                 match modelParams103 with ModelParams1 x1354
                 then
                   x1354.embeddedQMatrix
                 else
                   let #var"1125" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                   in
                   exit 1
               with
                 EmbeddedMarkovChainMatrix1 x1344
               then
                 x1344.mat
               else
                 let #var"1126" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                 in
                 exit 1)
  in
  let getLossRate1 =
    lam st471.
      lam repertoire2.
        lam hostIndex22.
          lam modelParams102.
            let fromState32 = get repertoire2 (subi hostIndex22 1) in
            match
              p_bind
                st471
                hrmStoreSubmodel
                (hrmInit {})
                (lam st472.
                   lam x781.
                     match eqi x781 2 with true
                     then
                       match fold1 st472 0 repertoire2 with (st473, x782)
                       in
                       p_map
                         st473 (lam x783.
                            eqi x783 1) x782
                     else
                       (st472, p_pure false))
                fromState32
            with
              (st474, x784)
            in
            p_bind
              st474
              hrmStoreSubmodel
              (hrmInit {})
              (lam st475.
                 lam x785.
                   match x785 with true
                   then
                     (st475, p_pure 0.)
                   else match
                     p_map
                       st475
                       (lam x786.
                          addi x786 1)
                       fromState32
                   with
                     (st476, x787)
                   in
                   match
                     p_map
                       st476
                       (lam x788.
                          addi (subi x788 1) 1)
                       fromState32
                   with
                     (st477, x789)
                   in
                   mtxGet2
                     st477
                     x787
                     x789
                     (match
                        match modelParams102 with ModelParams1 x1353
                        then
                          x1353.embeddedQMatrix
                        else
                          let #var"1123" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1343
                      then
                        x1343.mat
                      else
                        let #var"1124" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        exit 1))
              x784
  in
  let getLossRate2 =
    lam st459.
      lam repertoire1.
        lam hostIndex21.
          lam modelParams101.
            match
              p_traverseSeq
                st459
                (lam st460.
                   lam x767.
                     (st460, x767))
                repertoire1
            with
              (st461, x768)
            in
            match p_map st461 get x768 with (st462, x769)
            in
            match
              p_map
                st462 (lam x770.
                   subi x770 1) hostIndex21
            with
              (st463, x771)
            in
            match p_apply st463 x769 x771 with (st464, fromState31)
            in
            match
              p_bind
                st464
                hrmStoreSubmodel
                (hrmInit {})
                (lam st465.
                   lam x772.
                     match eqi x772 2 with true
                     then
                       match fold1 st465 0 repertoire1 with (st466, x773)
                       in
                       p_map
                         st466 (lam x774.
                            eqi x774 1) x773
                     else
                       (st465, p_pure false))
                fromState31
            with
              (st467, x775)
            in
            p_bind
              st467
              hrmStoreSubmodel
              (hrmInit {})
              (lam st468.
                 lam x776.
                   match x776 with true
                   then
                     (st468, p_pure 0.)
                   else match
                     p_map
                       st468
                       (lam x777.
                          addi x777 1)
                       fromState31
                   with
                     (st469, x778)
                   in
                   match
                     p_map
                       st469
                       (lam x779.
                          addi (subi x779 1) 1)
                       fromState31
                   with
                     (st470, x780)
                   in
                   mtxGet2
                     st470
                     x778
                     x780
                     (match
                        match modelParams101 with ModelParams1 x1352
                        then
                          x1352.embeddedQMatrix
                        else
                          let #var"1121" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1342
                      then
                        x1342.mat
                      else
                        let #var"1122" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        exit 1))
              x775
  in
  let getLossRate3 =
    lam st449.
      lam repertoire.
        lam hostIndex2.
          lam modelParams10.
            match p_map st449 get repertoire with (st450, x753)
            in
            match
              p_map st450 (lam x754.
                   subi x754 1) hostIndex2
            with
              (st451, x755)
            in
            match p_apply st451 x753 x755 with (st452, fromState3)
            in
            match
              p_bind
                st452
                hrmStoreSubmodel
                (hrmInit {})
                (lam st453.
                   lam x756.
                     match eqi x756 2 with true
                     then
                       match
                         p_map
                           st453
                           (lam x757.
                              match x757 with [ _ ] ++ _
                              then
                                match splitAt x757 1 with {#label"1" = x758}
                                in
                                rec26 (anon11 0 (get x757 0)) x758
                              else match x757 with ""
                              in
                              0)
                           repertoire
                       with
                         (st454, x759)
                       in
                       p_map
                         st454 (lam x760.
                            eqi x760 1) x759
                     else
                       (st453, p_pure false))
                fromState3
            with
              (st455, x761)
            in
            p_bind
              st455
              hrmStoreSubmodel
              (hrmInit {})
              (lam st456.
                 lam x762.
                   match x762 with true
                   then
                     (st456, p_pure 0.)
                   else match
                     p_map
                       st456
                       (lam x763.
                          addi x763 1)
                       fromState3
                   with
                     (st457, x764)
                   in
                   match
                     p_map
                       st457
                       (lam x765.
                          addi (subi x765 1) 1)
                       fromState3
                   with
                     (st458, x766)
                   in
                   mtxGet2
                     st458
                     x764
                     x766
                     (match
                        match modelParams10 with ModelParams1 x1351
                        then
                          x1351.embeddedQMatrix
                        else
                          let #var"1119" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1341
                      then
                        x1341.mat
                      else
                        let #var"1120" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        exit 1))
              x761
  in
  recursive
    let rec28 =
      lam st66.
        lam c17.
          lam c18.
            lam acc8.
              lam s29.
                match s29 with [ _ ] ++ _
                then
                  let x99 = get s29 0 in
                  match
                    p_bind
                      st66
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st67.
                         lam x100.
                           match eqi x100 2 with true
                           then
                             (st67, acc8)
                           else match
                             p_map
                               st67
                               (lam x101.
                                  lam x102.
                                    addf x101 x102)
                               acc8
                           with
                             (st68, x103)
                           in
                           match getGainRate1 st68 c17 x99 c18 with (st69, x104)
                           in
                           p_apply st69 x103 x104)
                      (get c17 (subi x99 1))
                  with
                    (st70, x105)
                  in
                  match splitAt s29 1 with {#label"1" = x106}
                  in
                  rec28 st70 c17 c18 x105 x106
                else match s29 with ""
                in
                (st66, acc8)
    let rec29 =
      lam st71.
        lam c19.
          lam c20.
            lam acc9.
              lam s210.
                match s210 with [ _ ] ++ _
                then
                  let x107 = get s210 0 in
                  match
                    p_bind
                      st71
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st72.
                         lam x108.
                           match eqi (get x108 (subi x107 1)) 2 with true
                           then
                             (st72, acc9)
                           else match
                             p_map
                               st72
                               (lam x109.
                                  lam x110.
                                    addf x109 x110)
                               acc9
                           with
                             (st73, x111)
                           in
                           match getGainRate st73 x108 x107 c20 with (st74, x112)
                           in
                           p_apply st74 x111 x112)
                      c19
                  with
                    (st75, x113)
                  in
                  match splitAt s210 1 with {#label"1" = x114}
                  in
                  rec29 st75 c19 c20 x113 x114
                else match s210 with ""
                in
                (st71, acc9)
  in
  let anon12 = lam x752.
      addi x752 1 in
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
    let rec210 =
      lam st76.
        lam c21.
          lam c22.
            lam acc10.
              lam s211.
                match s211 with [ _ ] ++ _
                then
                  let x115 = get s211 0 in
                  match
                    p_bind
                      st76
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st77.
                         lam x116.
                           match eqi x116 0 with true
                           then
                             (st77, acc10)
                           else match
                             p_map
                               st77
                               (lam x117.
                                  lam x118.
                                    addf x117 x118)
                               acc10
                           with
                             (st78, x119)
                           in
                           match getLossRate1 st78 c21 x115 c22 with (st79, x120)
                           in
                           p_apply st79 x119 x120)
                      (get c21 (subi x115 1))
                  with
                    (st80, x121)
                  in
                  match splitAt s211 1 with {#label"1" = x122}
                  in
                  rec210 st80 c21 c22 x121 x122
                else match s211 with ""
                in
                (st76, acc10)
    let rec211 =
      lam st81.
        lam c23.
          lam c24.
            lam acc14.
              lam s212.
                match s212 with [ _ ] ++ _
                then
                  let x123 = get s212 0 in
                  match
                    p_bind
                      st81
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st82.
                         lam x124.
                           match eqi (get x124 (subi x123 1)) 0 with true
                           then
                             (st82, acc14)
                           else
                             p_map
                               st82
                               (lam x125.
                                  addf x125 (getLossRate x124 x123 c24))
                               acc14)
                      c23
                  with
                    (st83, x126)
                  in
                  match splitAt s212 1 with {#label"1" = x127}
                  in
                  rec211 st83 c23 c24 x126 x127
                else match s212 with ""
                in
                (st81, acc14)
  in
  let anon13 = lam x751.
      addi x751 1 in
  recursive
    let rec33 =
      lam i15.
        lam acc15.
          match geqi i15 0 with true
          then
            rec33 (subi i15 1) (cons (anon13 i15) acc15)
          else
            acc15
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
    lam st439.
      lam currRep51.
        lam modelParams81.
          lam nhosts61.
            let s224 = create11 (addi (subi nhosts61 1) 1) in
            match
              match s224 with [ _ ] ++ _
              then
                let x734 = get s224 0 in
                match
                  p_bind
                    st439
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st440.
                       lam x735.
                         match eqi x735 2 with true
                         then
                           (st440, p_pure 0.)
                         else match getGainRate1 st440 currRep51 x734 modelParams81 with (st441, x736)
                         in
                         p_map
                           st441
                           (lam x737.
                              addf 0. x737)
                           x736)
                    (get currRep51 (subi x734 1))
                with
                  (st442, x738)
                in
                match splitAt s224 1 with {#label"1" = x739}
                in
                rec28 st442 currRep51 modelParams81 x738 x739
              else match s224 with ""
              in
              (st439, p_pure 0.)
            with
              (st443, x740)
            in
            match
              p_map
                st443
                (lam x741.
                   lam x742.
                     addf x741 x742)
                x740
            with
              (st444, x743)
            in
            let s225 = create12 (addi (subi nhosts61 1) 1) in
            match
              match s225 with [ _ ] ++ _
              then
                let x744 = get s225 0 in
                match
                  p_bind
                    st444
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st445.
                       lam x745.
                         match eqi x745 0 with true
                         then
                           (st445, p_pure 0.)
                         else match getLossRate1 st445 currRep51 x744 modelParams81 with (st446, x746)
                         in
                         p_map
                           st446
                           (lam x747.
                              addf 0. x747)
                           x746)
                    (get currRep51 (subi x744 1))
                with
                  (st447, x748)
                in
                match splitAt s225 1 with {#label"1" = x749}
                in
                rec210 st447 currRep51 modelParams81 x748 x749
              else match s225 with ""
              in
              (st444, p_pure 0.)
            with
              (st448, x750)
            in
            p_apply st448 x743 x750
  in
  let getTotalRate1 =
    lam st431.
      lam currRep5.
        lam modelParams8.
          lam nhosts6.
            let s222 = create11 (addi (subi nhosts6 1) 1) in
            match
              match s222 with [ _ ] ++ _
              then
                let x719 = get s222 0 in
                match
                  p_bind
                    st431
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st432.
                       lam x720.
                         match eqi (get x720 (subi x719 1)) 2 with true
                         then
                           (st432, p_pure 0.)
                         else match getGainRate st432 x720 x719 modelParams8 with (st433, x721)
                         in
                         p_map
                           st433
                           (lam x722.
                              addf 0. x722)
                           x721)
                    currRep5
                with
                  (st434, x723)
                in
                match splitAt s222 1 with {#label"1" = x724}
                in
                rec29 st434 currRep5 modelParams8 x723 x724
              else match s222 with ""
              in
              (st431, p_pure 0.)
            with
              (st435, x725)
            in
            match
              p_map
                st435
                (lam x726.
                   lam x727.
                     addf x726 x727)
                x725
            with
              (st436, x728)
            in
            let s223 = create12 (addi (subi nhosts6 1) 1) in
            match
              match s223 with [ _ ] ++ _
              then
                let x729 = get s223 0 in
                match
                  p_map
                    st436
                    (lam x730.
                       match eqi (get x730 (subi x729 1)) 0 with true
                       then
                         0.
                       else
                         addf 0. (getLossRate x730 x729 modelParams8))
                    currRep5
                with
                  (st437, x731)
                in
                match splitAt s223 1 with {#label"1" = x732}
                in
                rec211 st437 currRep5 modelParams8 x731 x732
              else match s223 with ""
              in
              (st436, p_pure 0.)
            with
              (st438, x733)
            in
            p_apply st438 x728 x733
  in
  recursive
    let fullModelWeight =
      lam st84.
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
                                st84
                                (lam x128.
                                   lam x129.
                                     mulf (negf (subf x128 finalAge)) x129)
                                currAge
                            with
                              (st85, x130)
                            in
                            match getTotalRate1 st85 currRep3 modelParams nhosts5 with (st86, x131)
                            in
                            p_apply st86 x130 x131
                          else match
                            p_map
                              st84
                              (lam x132.
                                 get x132 (subi nextIndex 1))
                              eventSeq3
                          with
                            (st87, nextEvent)
                          in
                          match
                            p_map
                              st87
                              (lam x133.
                                 match x133 with Event1 x311
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
                            (st88, newAge)
                          in
                          match
                            getTotalRate1 st88 currRep3 modelParams nhosts5
                          with
                            (st89, totalLeavingRate1)
                          in
                          match
                            p_map
                              st89
                              (lam x134.
                                 match x134 with Event1 x1321
                                 then
                                   x1321.host
                                 else
                                   let #var"118" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st90, hostIndex1)
                          in
                          match
                            p_map
                              st90
                              (lam x135.
                                 lam x136.
                                   lam st91.
                                     match
                                       gti
                                         (match x135 with Event1 x1301
                                          then
                                            x1301.fromState
                                          else
                                            let #var"119" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x136
                                     with
                                       true
                                     then
                                       getLossRate3 st91 currRep3 hostIndex1 modelParams
                                     else
                                       getGainRate3 st91 currRep3 hostIndex1 modelParams)
                              nextEvent
                          with
                            (st92, x137)
                          in
                          match
                            p_map
                              st92
                              (lam x138.
                                 match x138 with Event1 x1311
                                 then
                                   x1311.toState
                                 else
                                   let #var"120" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent
                          with
                            (st93, x139)
                          in
                          match
                            p_subApply st93 hrmStoreSubmodel (hrmInit {}) x137 x139
                          with
                            (st94, x140)
                          in
                          match p_join st94 x140 with (st95, x141)
                          in
                          match
                            p_map
                              st95
                              (lam x142.
                                 lam x143.
                                   divf x142 x143)
                              x141
                          with
                            (st96, x144)
                          in
                          match p_apply st96 x144 totalLeavingRate1 with (st97, x145)
                          in
                          match log11 st97 x145 with (st98, x146)
                          in
                          match
                            p_map
                              st98
                              (lam x147.
                                 lam x148.
                                   lam x149.
                                     addf (subf x147 x148) x149)
                              x146
                          with
                            (st99, x150)
                          in
                          match
                            p_map
                              st99
                              (lam x151.
                                 lam x154.
                                   lam x155.
                                     mulf (subf x151 x154) x155)
                              currAge
                          with
                            (st100, x156)
                          in
                          match p_apply st100 x156 newAge with (st101, x157)
                          in
                          match p_apply st101 x157 totalLeavingRate1 with (st102, x158)
                          in
                          match p_apply st102 x150 x158 with (st103, x159)
                          in
                          match
                            updateRepertoire1 st103 currRep3 nextEvent nhosts5
                          with
                            (st104, x160)
                          in
                          match
                            fullModelWeight
                              st104
                              (addi nextIndex 1)
                              x160
                              finalRep
                              newAge
                              finalAge
                              eventSeq3
                              nEvents3
                              nhosts5
                              modelParams
                          with
                            (st105, x161)
                          in
                          p_apply st105 x159 x161
    let fullModelWeight1 =
      lam st106.
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
                                st106
                                (lam x162.
                                   lam x163.
                                     mulf (negf (subf x162 finalAge1)) x163)
                                currAge1
                            with
                              (st107, x164)
                            in
                            match
                              getTotalRate1 st107 currRep31 modelParams1 nhosts51
                            with
                              (st108, x165)
                            in
                            p_apply st108 x164 x165
                          else match
                            p_map
                              st106
                              (lam x166.
                                 get x166 (subi nextIndex1 1))
                              eventSeq31
                          with
                            (st109, nextEvent1)
                          in
                          match
                            p_map
                              st109
                              (lam x167.
                                 match x167 with Event1 x312
                                 then
                                   x312.eventTime
                                 else
                                   let #var"121" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st110, newAge1)
                          in
                          match
                            getTotalRate1 st110 currRep31 modelParams1 nhosts51
                          with
                            (st111, totalLeavingRate11)
                          in
                          match
                            p_map
                              st111
                              (lam x168.
                                 match x168 with Event1 x1322
                                 then
                                   x1322.host
                                 else
                                   let #var"122" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st112, hostIndex11)
                          in
                          match
                            p_map
                              st112
                              (lam x169.
                                 lam x170.
                                   lam st113.
                                     match
                                       gti
                                         (match x169 with Event1 x1302
                                          then
                                            x1302.fromState
                                          else
                                            let #var"123" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x170
                                     with
                                       true
                                     then
                                       getLossRate3 st113 currRep31 hostIndex11 modelParams1
                                     else
                                       getGainRate3 st113 currRep31 hostIndex11 modelParams1)
                              nextEvent1
                          with
                            (st114, x171)
                          in
                          match
                            p_map
                              st114
                              (lam x172.
                                 match x172 with Event1 x1312
                                 then
                                   x1312.toState
                                 else
                                   let #var"124" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                   in
                                   exit 1)
                              nextEvent1
                          with
                            (st115, x173)
                          in
                          match
                            p_subApply st115 hrmStoreSubmodel (hrmInit {}) x171 x173
                          with
                            (st116, x174)
                          in
                          match p_join st116 x174 with (st117, x175)
                          in
                          match
                            p_map
                              st117
                              (lam x176.
                                 lam x177.
                                   divf x176 x177)
                              x175
                          with
                            (st118, x178)
                          in
                          match p_apply st118 x178 totalLeavingRate11 with (st119, x179)
                          in
                          match log11 st119 x179 with (st120, x180)
                          in
                          match
                            p_map
                              st120
                              (lam x181.
                                 lam x182.
                                   lam x183.
                                     addf (subf x181 x182) x183)
                              x180
                          with
                            (st121, x184)
                          in
                          match
                            p_map
                              st121
                              (lam x185.
                                 lam x186.
                                   lam x187.
                                     mulf (subf x185 x186) x187)
                              currAge1
                          with
                            (st122, x188)
                          in
                          match p_apply st122 x188 newAge1 with (st123, x189)
                          in
                          match p_apply st123 x189 totalLeavingRate11 with (st124, x190)
                          in
                          match p_apply st124 x184 x190 with (st125, x191)
                          in
                          match
                            updateRepertoire1 st125 currRep31 nextEvent1 nhosts51
                          with
                            (st126, x192)
                          in
                          match
                            fullModelWeight1
                              st126
                              (addi nextIndex1 1)
                              x192
                              finalRep1
                              newAge1
                              finalAge1
                              eventSeq31
                              nEvents31
                              nhosts51
                              modelParams1
                          with
                            (st127, x193)
                          in
                          p_apply st127 x191 x193
  in
  recursive
    let hostIndepLikelihood =
      lam st128.
        lam nextIndex11.
          lam currState.
            lam finalState.
              lam currAge11.
                lam finalAge11.
                  lam eventSeq4.
                    lam embeddedQMatrix.
                      match length13 st128 eventSeq4 with (st129, x194)
                      in
                      p_bind
                        st129
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st130.
                           lam x195.
                             match gti nextIndex11 x195 with true
                             then
                               p_map
                                 st130
                                 (lam x196.
                                    mulf
                                      (negf (subf currAge11 finalAge11))
                                      (get
                                         (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x321
                                          then
                                            x321.totalRates
                                          else
                                            let #var"125" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                            in
                                            exit 1)
                                         (subi (addi x196 1) 1)))
                                 currState
                             else match
                               p_map
                                 st130
                                 (lam x197.
                                    get x197 (subi nextIndex11 1))
                                 eventSeq4
                             with
                               (st131, nextEvent11)
                             in
                             match
                               p_map
                                 st131
                                 (lam x198.
                                    match x198 with Event1 x361
                                    then
                                      x361.toState
                                    else
                                      let #var"126" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent11
                             with
                               (st132, nextState)
                             in
                             match
                               p_map
                                 st132
                                 (lam x199.
                                    match x199 with Event1 x351
                                    then
                                      x351.eventTime
                                    else
                                      let #var"127" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent11
                             with
                               (st133, nextAge)
                             in
                             match
                               p_map
                                 st133
                                 (lam x200.
                                    get
                                      (get
                                         (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x331
                                          then
                                            x331.transitionProbs
                                          else
                                            let #var"128" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                            in
                                            exit 1)
                                         (subi (addi x200 1) 1)))
                                 currState
                             with
                               (st134, x201)
                             in
                             match
                               p_map
                                 st134
                                 (lam x202.
                                    subi (addi x202 1) 1)
                                 nextState
                             with
                               (st135, x203)
                             in
                             match p_apply st135 x201 x203 with (st136, x204)
                             in
                             match log11 st136 x204 with (st137, x205)
                             in
                             match
                               p_map
                                 st137
                                 (lam x206.
                                    lam x207.
                                      lam x208.
                                        addf (subf x206 x207) x208)
                                 x205
                             with
                               (st138, x209)
                             in
                             match
                               p_map
                                 st138
                                 (lam x210.
                                    lam x211.
                                      mulf (subf currAge11 x210) x211)
                                 nextAge
                             with
                               (st139, x212)
                             in
                             match
                               p_map
                                 st139
                                 (lam x213.
                                    get
                                      (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x341
                                       then
                                         x341.totalRates
                                       else
                                         let #var"129" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                         in
                                         exit 1)
                                      (subi (addi x213 1) 1))
                                 currState
                             with
                               (st140, x214)
                             in
                             match p_apply st140 x212 x214 with (st141, x215)
                             in
                             match p_apply st141 x209 x215 with (st142, x216)
                             in
                             match
                               hostIndepLikelihood1
                                 st142
                                 (addi nextIndex11 1)
                                 nextState
                                 finalState
                                 nextAge
                                 finalAge11
                                 eventSeq4
                                 embeddedQMatrix
                             with
                               (st143, x217)
                             in
                             p_apply st143 x216 x217)
                        x194
    let hostIndepLikelihood1 =
      lam st144.
        lam nextIndex12.
          lam currState1.
            lam finalState1.
              lam currAge12.
                lam finalAge12.
                  lam eventSeq41.
                    lam embeddedQMatrix1.
                      match length13 st144 eventSeq41 with (st145, x218)
                      in
                      p_bind
                        st145
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st146.
                           lam x219.
                             match gti nextIndex12 x219 with true
                             then
                               match
                                 p_map
                                   st146
                                   (lam x220.
                                      lam x222.
                                        mulf (negf (subf x220 finalAge12)) x222)
                                   currAge12
                               with
                                 (st147, x223)
                               in
                               match
                                 p_map
                                   st147
                                   (lam x224.
                                      get
                                        (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x322
                                         then
                                           x322.totalRates
                                         else
                                           let #var"130" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                           in
                                           exit 1)
                                        (subi (addi x224 1) 1))
                                   currState1
                               with
                                 (st148, x225)
                               in
                               p_apply st148 x223 x225
                             else match
                               p_map
                                 st146
                                 (lam x226.
                                    get x226 (subi nextIndex12 1))
                                 eventSeq41
                             with
                               (st149, nextEvent12)
                             in
                             match
                               p_map
                                 st149
                                 (lam x227.
                                    match x227 with Event1 x362
                                    then
                                      x362.toState
                                    else
                                      let #var"131" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent12
                             with
                               (st150, nextState1)
                             in
                             match
                               p_map
                                 st150
                                 (lam x228.
                                    match x228 with Event1 x352
                                    then
                                      x352.eventTime
                                    else
                                      let #var"132" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent12
                             with
                               (st151, nextAge1)
                             in
                             match
                               p_map
                                 st151
                                 (lam x229.
                                    get
                                      (get
                                         (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x332
                                          then
                                            x332.transitionProbs
                                          else
                                            let #var"133" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                            in
                                            exit 1)
                                         (subi (addi x229 1) 1)))
                                 currState1
                             with
                               (st152, x230)
                             in
                             match
                               p_map
                                 st152
                                 (lam x232.
                                    subi (addi x232 1) 1)
                                 nextState1
                             with
                               (st153, x233)
                             in
                             match p_apply st153 x230 x233 with (st154, x234)
                             in
                             match log11 st154 x234 with (st155, x235)
                             in
                             match
                               p_map
                                 st155
                                 (lam x236.
                                    lam x237.
                                      lam x238.
                                        addf (subf x236 x237) x238)
                                 x235
                             with
                               (st156, x239)
                             in
                             match
                               p_map
                                 st156
                                 (lam x240.
                                    lam x241.
                                      lam x242.
                                        mulf (subf x240 x241) x242)
                                 currAge12
                             with
                               (st157, x243)
                             in
                             match p_apply st157 x243 nextAge1 with (st158, x244)
                             in
                             match
                               p_map
                                 st158
                                 (lam x245.
                                    get
                                      (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x342
                                       then
                                         x342.totalRates
                                       else
                                         let #var"134" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                         in
                                         exit 1)
                                      (subi (addi x245 1) 1))
                                 currState1
                             with
                               (st159, x246)
                             in
                             match p_apply st159 x244 x246 with (st160, x247)
                             in
                             match p_apply st160 x239 x247 with (st161, x248)
                             in
                             match
                               hostIndepLikelihood1
                                 st161
                                 (addi nextIndex12 1)
                                 nextState1
                                 finalState1
                                 nextAge1
                                 finalAge12
                                 eventSeq41
                                 embeddedQMatrix1
                             with
                               (st162, x249)
                             in
                             p_apply st162 x248 x249)
                        x218
    let hostIndepLikelihood2 =
      lam st163.
        lam nextIndex13.
          lam currState2.
            lam finalState2.
              lam currAge13.
                lam finalAge13.
                  lam eventSeq42.
                    lam embeddedQMatrix2.
                      match length13 st163 eventSeq42 with (st164, x250)
                      in
                      p_bind
                        st164
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st165.
                           lam x251.
                             match gti nextIndex13 x251 with true
                             then
                               p_map
                                 st165
                                 (lam x252.
                                    mulf
                                      (negf (subf currAge13 finalAge13))
                                      (get
                                         (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x323
                                          then
                                            x323.totalRates
                                          else
                                            let #var"135" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                            in
                                            exit 1)
                                         (subi (addi x252 1) 1)))
                                 currState2
                             else match
                               p_map
                                 st165
                                 (lam x253.
                                    get x253 (subi nextIndex13 1))
                                 eventSeq42
                             with
                               (st166, nextEvent13)
                             in
                             match
                               p_map
                                 st166
                                 (lam x254.
                                    match x254 with Event1 x363
                                    then
                                      x363.toState
                                    else
                                      let #var"136" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent13
                             with
                               (st167, nextState2)
                             in
                             match
                               p_map
                                 st167
                                 (lam x255.
                                    match x255 with Event1 x353
                                    then
                                      x353.eventTime
                                    else
                                      let #var"137" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent13
                             with
                               (st168, nextAge2)
                             in
                             match
                               p_map
                                 st168
                                 (lam x256.
                                    get
                                      (get
                                         (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x333
                                          then
                                            x333.transitionProbs
                                          else
                                            let #var"138" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                            in
                                            exit 1)
                                         (subi (addi x256 1) 1)))
                                 currState2
                             with
                               (st169, x257)
                             in
                             match
                               p_map
                                 st169
                                 (lam x258.
                                    subi (addi x258 1) 1)
                                 nextState2
                             with
                               (st170, x259)
                             in
                             match p_apply st170 x257 x259 with (st171, x260)
                             in
                             match log11 st171 x260 with (st172, x261)
                             in
                             match
                               p_map
                                 st172
                                 (lam x262.
                                    lam x263.
                                      lam x264.
                                        addf (subf x262 x263) x264)
                                 x261
                             with
                               (st173, x265)
                             in
                             match
                               p_map
                                 st173
                                 (lam x266.
                                    lam x267.
                                      mulf (subf currAge13 x266) x267)
                                 nextAge2
                             with
                               (st174, x268)
                             in
                             match
                               p_map
                                 st174
                                 (lam x269.
                                    get
                                      (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x343
                                       then
                                         x343.totalRates
                                       else
                                         let #var"139" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                         in
                                         exit 1)
                                      (subi (addi x269 1) 1))
                                 currState2
                             with
                               (st175, x270)
                             in
                             match p_apply st175 x268 x270 with (st176, x271)
                             in
                             match p_apply st176 x265 x271 with (st177, x272)
                             in
                             match
                               hostIndepLikelihood3
                                 st177
                                 (addi nextIndex13 1)
                                 nextState2
                                 finalState2
                                 nextAge2
                                 finalAge13
                                 eventSeq42
                                 embeddedQMatrix2
                             with
                               (st178, x273)
                             in
                             p_apply st178 x272 x273)
                        x250
    let hostIndepLikelihood3 =
      lam st179.
        lam nextIndex14.
          lam currState3.
            lam finalState3.
              lam currAge14.
                lam finalAge14.
                  lam eventSeq43.
                    lam embeddedQMatrix3.
                      match length13 st179 eventSeq43 with (st180, x274)
                      in
                      p_bind
                        st180
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st181.
                           lam x275.
                             match gti nextIndex14 x275 with true
                             then
                               match
                                 p_map
                                   st181
                                   (lam x276.
                                      lam x277.
                                        mulf (negf (subf x276 finalAge14)) x277)
                                   currAge14
                               with
                                 (st182, x278)
                               in
                               match
                                 p_map
                                   st182
                                   (lam x279.
                                      get
                                        (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x324
                                         then
                                           x324.totalRates
                                         else
                                           let #var"140" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                           in
                                           exit 1)
                                        (subi (addi x279 1) 1))
                                   currState3
                               with
                                 (st183, x280)
                               in
                               p_apply st183 x278 x280
                             else match
                               p_map
                                 st181
                                 (lam x281.
                                    get x281 (subi nextIndex14 1))
                                 eventSeq43
                             with
                               (st184, nextEvent14)
                             in
                             match
                               p_map
                                 st184
                                 (lam x282.
                                    match x282 with Event1 x364
                                    then
                                      x364.toState
                                    else
                                      let #var"141" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent14
                             with
                               (st185, nextState3)
                             in
                             match
                               p_map
                                 st185
                                 (lam x283.
                                    match x283 with Event1 x354
                                    then
                                      x354.eventTime
                                    else
                                      let #var"142" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                                      in
                                      exit 1)
                                 nextEvent14
                             with
                               (st186, nextAge3)
                             in
                             match
                               p_map
                                 st186
                                 (lam x284.
                                    get
                                      (get
                                         (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x334
                                          then
                                            x334.transitionProbs
                                          else
                                            let #var"143" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                            in
                                            exit 1)
                                         (subi (addi x284 1) 1)))
                                 currState3
                             with
                               (st187, x285)
                             in
                             match
                               p_map
                                 st187
                                 (lam x286.
                                    subi (addi x286 1) 1)
                                 nextState3
                             with
                               (st188, x287)
                             in
                             match p_apply st188 x285 x287 with (st189, x288)
                             in
                             match log11 st189 x288 with (st190, x289)
                             in
                             match
                               p_map
                                 st190
                                 (lam x290.
                                    lam x291.
                                      lam x292.
                                        addf (subf x290 x291) x292)
                                 x289
                             with
                               (st191, x293)
                             in
                             match
                               p_map
                                 st191
                                 (lam x294.
                                    lam x295.
                                      lam x296.
                                        mulf (subf x294 x295) x296)
                                 currAge14
                             with
                               (st192, x297)
                             in
                             match p_apply st192 x297 nextAge3 with (st193, x298)
                             in
                             match
                               p_map
                                 st193
                                 (lam x299.
                                    get
                                      (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x344
                                       then
                                         x344.totalRates
                                       else
                                         let #var"144" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                         in
                                         exit 1)
                                      (subi (addi x299 1) 1))
                                 currState3
                             with
                               (st194, x300)
                             in
                             match p_apply st194 x298 x300 with (st195, x303)
                             in
                             match p_apply st195 x293 x303 with (st196, x304)
                             in
                             match
                               hostIndepLikelihood3
                                 st196
                                 (addi nextIndex14 1)
                                 nextState3
                                 finalState3
                                 nextAge3
                                 finalAge14
                                 eventSeq43
                                 embeddedQMatrix3
                             with
                               (st197, x305)
                             in
                             p_apply st197 x304 x305)
                        x274
  in
  let anon14 = lam x718.
      addi x718 1 in
  recursive
    let rec34 =
      lam i16.
        lam acc16.
          match geqi i16 0 with true
          then
            rec34 (subi i16 1) (cons (anon14 i16) acc16)
          else
            acc16
  in
  let anon15 =
    lam st430.
      lam msg1.
        lam x717.
          lam nodeLabel.
          p_assume
            st430
            (hrmStoreNode nodeLabel x717)
            (p_pure (mkCategorical (mtx3ToSeq msg1 x717)))
  in
  recursive
    let rec8 =
      lam st198.
        lam c25.
          lam s8.
            lam nodeLabel.
            match s8 with [ _,
                _ ] ++ _
            then
              match anon15 st198 c25 (get s8 0) nodeLabel with (st199, x306)
              in
              match splitAt s8 1 with {#label"1" = x307}
              in
              match rec8 st199 c25 x307 nodeLabel with (st200, x308)
              in
              (st200, cons x306 x308)
            else match s8 with [ e12 ]
            then
              match splitAt s8 1 with {#label"1" = x309}
              in
              let slice11 = x309 in
              match anon15 st198 c25 e12 nodeLabel with (st201, x310)
              in
              (st201, [ x310 ])
            else match s8 with ""
            in
            (st198, "")
  in
  let suggestNodeRep =
    lam st429.
      lam msg.
        lam nHosts4.
          lam nodeLabel.
            let i111 = subi (addi (subi nHosts4 1) 1) 1 in
            rec8
              st429
              msg
              (match geqi i111 0 with true
               then
                 rec34 (subi i111 1) (cons (anon14 i111) "")
               else
                 "")
              nodeLabel
  in
  recursive
    let sampleHostHistoryRec =
      lam st202.
        lam currentState.
          lam finalState11.
            lam currentAge.
              lam finalAge2.
                lam host.
                  lam nodeLabel.
                    lam embeddedQMatrix11.
                      p_bind
                        st202
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st203.
                           lam x313.
                             match ltf x313 finalAge2 with true
                             then
                               p_map
                                 st203
                                 (lam x314.
                                    match eqi x314 finalState11 with true
                                    then
                                      Bridge1
                                        { success = true, events = "" }
                                    else
                                      Bridge1
                                        { success = false, events = "" })
                                 currentState
                             else match
                               p_map
                                 st203
                                 (lam x315.
                                    mkCategorical
                                      (get
                                         (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x401
                                          then
                                            x401.transitionProbs
                                          else
                                            let #var"145" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 335:16-335:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                            in
                                            exit 1)
                                         (subi (addi x315 1) 1)))
                                 currentState
                             with
                               (st204, x316)
                             in
                             match p_assume st204 (hrmStoreBranchState nodeLabel host) x316 with (st205, nextState11)
                             in
                             match
                               p_map
                                 st205
                                 (lam x317.
                                    mkExponential
                                            (get
                                               (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x391
                                                then
                                                  x391.totalRates
                                                else
                                                  let #var"146" =
                                                    print
                                                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 339:20-339:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                                  in
                                                  exit 1)
                                               (subi (addi x317 1) 1))
                                 )
                                 nextState11
                             with
                               (st206, x318)
                             in
                             match p_assume st206 (hrmStoreBranchTime nodeLabel host) x318 with (st207, x319)
                             in
                             match
                               p_map
                                 st207
                                 (lam x320.
                                    subf x313 x320)
                                 x319
                             with
                               (st208, x325)
                             in
                             match
                               sampleHostHistoryRec
                                 st208
                                 nextState11
                                 finalState11
                                 x325
                                 finalAge2
                                 host
                                 nodeLabel
                                 embeddedQMatrix11
                             with
                               (st209, restOfHistory)
                             in
                             match
                               p_map
                                 st209
                                 (lam x326.
                                    lam x327.
                                      Bridge1
                                        { success =
                                            match x326 with Bridge1 x371
                                            then
                                              x371.success
                                            else
                                              let #var"147" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 357:18-357:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                              in
                                              exit 1,
                                          events = x327 })
                                 restOfHistory
                             with
                               (st210, x328)
                             in
                             match
                               p_map
                                 st210
                                 (lam x329.
                                    match x329 with Bridge1 x381
                                    then
                                      x381.events
                                    else
                                      let #var"148" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 355:10-355:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                      in
                                      exit 1)
                                 restOfHistory
                             with
                               (st211, x330)
                             in
                             match
                               cons11
                                 st211
                                 (Event1
                                    { host = host,
                                      toState = nextState11,
                                      eventTime = x313,
                                      fromState = currentState })
                                 x330
                             with
                               (st212, x335)
                             in
                             p_apply st212 x328 x335)
                        currentAge
    let sampleHostHistoryRec1 =
      lam st213.
        lam currentState1.
          lam finalState12.
            lam currentAge1.
              lam finalAge21.
                lam host1.
                  lam nodeLabel1.
                    lam embeddedQMatrix12.
                      p_bind
                        st213
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st214.
                           lam x336.
                             match ltf x336 finalAge21 with true
                             then
                               match
                                 p_map
                                   st214
                                   (lam x337.
                                      lam x338.
                                        match eqi x337 x338 with true
                                        then
                                          Bridge1
                                            { success = true, events = "" }
                                        else
                                          Bridge1
                                            { success = false, events = "" })
                                   currentState1
                               with
                                 (st215, x339)
                               in
                               p_apply st215 x339 finalState12
                             else match
                               p_map
                                 st214
                                 (lam x340.
                                    mkCategorical
                                      (get
                                         (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x402
                                          then
                                            x402.transitionProbs
                                          else
                                            let #var"149" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 335:16-335:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                            in
                                            exit 1)
                                         (subi (addi x340 1) 1)))
                                 currentState1
                             with
                               (st216, x345)
                             in
                             match p_assume st216 (hrmStoreBranchState nodeLabel1 host1) x345 with (st217, nextState12)
                             in
                             match
                               p_map
                                 st217
                                 (lam x346.
                                    mkExponential
                                      (addf
                                         (addf
                                            (get
                                               (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x392
                                                then
                                                  x392.totalRates
                                                else
                                                  let #var"150" =
                                                    print
                                                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 339:20-339:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                                  in
                                                  exit 1)
                                               (subi (addi x346 1) 1))
                                            (mulf (int2float host1) 0.))
                                         (mulf (int2float nodeLabel1) 0.)))
                                 nextState12
                             with
                               (st218, x347)
                             in
                             match p_assume st218 (hrmStoreBranchTime nodeLabel1 host1) x347 with (st219, x348)
                             in
                             match
                               p_map
                                 st219
                                 (lam x349.
                                    subf x336 x349)
                                 x348
                             with
                               (st220, x350)
                             in
                             match
                               sampleHostHistoryRec1
                                 st220
                                 nextState12
                                 finalState12
                                 x350
                                 finalAge21
                                 host1
                                 nodeLabel1
                                 embeddedQMatrix12
                             with
                               (st221, restOfHistory1)
                             in
                             match
                               p_map
                                 st221
                                 (lam x355.
                                    lam x356.
                                      Bridge1
                                        { success =
                                            match x355 with Bridge1 x372
                                            then
                                              x372.success
                                            else
                                              let #var"151" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 357:18-357:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                              in
                                              exit 1,
                                          events = x356 })
                                 restOfHistory1
                             with
                               (st222, x357)
                             in
                             match
                               p_map
                                 st222
                                 (lam x358.
                                    match x358 with Bridge1 x382
                                    then
                                      x382.events
                                    else
                                      let #var"152" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 355:10-355:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                      in
                                      exit 1)
                                 restOfHistory1
                             with
                               (st223, x359)
                             in
                             match
                               cons11
                                 st223
                                 (Event1
                                    { host = host1,
                                      toState = nextState12,
                                      eventTime = x336,
                                      fromState = currentState1 })
                                 x359
                             with
                               (st224, x360)
                             in
                             p_apply st224 x357 x360)
                        currentAge1
  in
  let anon16 = lam x716.
      addi x716 1 in
  recursive
    let rec35 =
      lam i17.
        lam acc17.
          match geqi i17 0 with true
          then
            rec35 (subi i17 1) (cons (anon16 i17) acc17)
          else
            acc17
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
    lam st421.
      lam startRep1.
        lam finalRep12.
          lam startAge1.
            lam finalAge33.
              lam nodeLabel12.
                lam modelParams31.
                  lam x704.
                    let startState1 = get startRep1 (subi x704 1) in
                    let embeddedQMatrix51 =
                      match modelParams31 with ModelParams1 x1042
                      then
                        x1042.embeddedQMatrix
                      else
                        let #var"1118" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 207:4-207:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_map
                        st421
                        (lam x705.
                           mkExponential
                                   (get
                                      (match embeddedQMatrix51 with EmbeddedMarkovChainMatrix1 x1082
                                       then
                                         x1082.totalRates
                                       else
                                         let #var"1115" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 298:18-298:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                                         in
                                         exit 1)
                                      (subi (addi x705 1) 1))
                                )
                        startState1
                    with
                      (st422, x706)
                    in
                    match p_assume st422 (hrmStoreBranchTime nodeLabel12 x704) x706 with (st423, x707)
                    in
                    match
                      p_map
                        st423
                        (lam x708.
                           subf startAge1 x708)
                        x707
                    with
                      (st424, x709)
                    in
                    match
                      sampleHostHistoryRec
                        st424
                        startState1
                        (get finalRep12 (subi x704 1))
                        x709
                        finalAge33
                        x704
                        nodeLabel12
                        embeddedQMatrix51
                    with
                      (st425, bridge1)
                    in
                    match
                      p_map
                        st425
                        (lam x710.
                           match x710 with Bridge1 x1072
                           then
                             x1072.success
                           else
                             let #var"1116" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 310:19-310:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge1
                    with
                      (st426, x712)
                    in
                    match bool2real st426 x712 with (st427, x713)
                    in
                    let st428 =
                      p_weight
                        st427
                        (hrmStoreBridgeSuppWeight nodeLabel12 x704)
                        (lam x715.
                           externalLog
                            x715
                        )
                        x713
                    in
                    let foo51 = {} in
                    p_map
                      st428
                      (lam x714.
                         match x714 with Bridge1 x1062
                         then
                           x1062.events
                         else
                           let #var"1117" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 311:9-311:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge1
  in
  let anon18 =
    lam st413.
      lam startRep.
        lam finalRep11.
          lam startAge.
            lam finalAge32.
              lam nodeLabel11.
                lam modelParams3.
                  lam x692.
                    let startState = get startRep (subi x692 1) in
                    let embeddedQMatrix5 =
                      match modelParams3 with ModelParams1 x1041
                      then
                        x1041.embeddedQMatrix
                      else
                        let #var"1114" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 207:4-207:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_map
                        st413
                        (lam x693.
                           mkExponential
                                   (get
                                      (match embeddedQMatrix5 with EmbeddedMarkovChainMatrix1 x1081
                                       then
                                         x1081.totalRates
                                       else
                                         let #var"1111" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 298:18-298:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                                         in
                                         exit 1)
                                      (subi (addi x693 1) 1))
                                )
                        startState
                    with
                      (st414, x694)
                    in
                    match p_assume st414 (hrmStoreBranchTime nodeLabel11 x692) x694 with (st415, x695)
                    in
                    match
                      p_map
                        st415
                        (lam x696.
                           subf startAge x696)
                        x695
                    with
                      (st416, x697)
                    in
                    match
                      sampleHostHistoryRec1
                        st416
                        startState
                        (get finalRep11 (subi x692 1))
                        x697
                        finalAge32
                        x692
                        nodeLabel11
                        embeddedQMatrix5
                    with
                      (st417, bridge)
                    in
                    match
                      p_map
                        st417
                        (lam x698.
                           match x698 with Bridge1 x1071
                           then
                             x1071.success
                           else
                             let #var"1112" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 310:19-310:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge
                    with
                      (st418, x699)
                    in
                    match bool2real st418 x699 with (st419, x700)
                    in
                    let st420 =
                      p_weight
                        st419
                        (hrmStoreBridgeSuppWeight nodeLabel11 x692)
                        (lam x703.
                           externalLog
                            x703)
                        x700
                    in
                    let foo5 = {} in
                    p_map
                      st420
                      (lam x702.
                         match x702 with Bridge1 x1061
                         then
                           x1061.events
                         else
                           let #var"1113" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 311:9-311:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge
  in
  recursive
    let rec9 =
      lam st225.
        lam c26.
          lam c27.
            lam c28.
              lam c29.
                lam c30.
                  lam c31.
                    lam s9.
                      match s9 with [ _,
                          _ ] ++ _
                      then
                        match anon17 st225 c26 c27 c28 c29 c30 c31 (get s9 0) with (st226, x365)
                        in
                        match splitAt s9 1 with {#label"1" = x366}
                        in
                        match rec9 st226 c26 c27 c28 c29 c30 c31 x366 with (st227, x367)
                        in
                        (st227, cons x365 x367)
                      else match s9 with [ e13 ]
                      then
                        match splitAt s9 1 with {#label"1" = x368}
                        in
                        let slice12 = x368 in
                        match anon17 st225 c26 c27 c28 c29 c30 c31 e13 with (st228, x369)
                        in
                        (st228, [ x369 ])
                      else match s9 with ""
                      in
                      (st225, "")
    let rec10 =
      lam st229.
        lam c32.
          lam c33.
            lam c34.
              lam c35.
                lam c36.
                  lam c37.
                    lam s10.
                      match s10 with [ _,
                          _ ] ++ _
                      then
                        match
                          anon18 st229 c32 c33 c34 c35 c36 c37 (get s10 0)
                        with
                          (st230, x370)
                        in
                        match splitAt s10 1 with {#label"1" = x373}
                        in
                        match rec10 st230 c32 c33 c34 c35 c36 c37 x373 with (st231, x374)
                        in
                        (st231, cons x370 x374)
                      else match s10 with [ e14 ]
                      then
                        match splitAt s10 1 with {#label"1" = x375}
                        in
                        let slice13 = x375 in
                        match anon18 st229 c32 c33 c34 c35 c36 c37 e14 with (st232, x376)
                        in
                        (st232, [ x376 ])
                      else match s10 with ""
                      in
                      (st229, "")
  in
  let anon19 =
    lam h2.
      lam x690.
        lti
          (match
             isNaN1
               (match h2 with Event1 x1091
                then
                  x1091.eventTime
                else
                  let #var"1106" =
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
               (match x690 with Event1 x1131
                then
                  x1131.eventTime
                else
                  let #var"1107" =
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
                  let #var"1108" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 253:6-253:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
                  in
                  exit 1)
               (match x690 with Event1 x1151
                then
                  x1151.eventTime
                else
                  let #var"1109" =
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
      lam c38.
        lam l.
          lam r.
            lam seq1.
              match seq1 with [ _ ] ++ _
              then
                let s41 = get seq1 0 in
                match splitAt seq1 1 with {#label"1" = x377}
                in
                let seq2 = x377 in
                match anon19 c38 s41 with true
                then
                  work11 c38 (cons s41 l) r seq2
                else
                  work11 c38 l (cons s41 r) seq2
              else match seq1 with ""
              in
              (l, r)
    let work12 =
      lam c39.
        lam l1.
          lam r1.
            lam seq11.
              match seq11 with [ _ ] ++ _
              then
                let s42 = get seq11 0 in
                match splitAt seq11 1 with {#label"1" = x378}
                in
                let seq21 = x378 in
                match anon19 c39 s42 with true
                then
                  work12 c39 (cons s42 l1) r1 seq21
                else
                  work11 c39 l1 (cons s42 r1) seq21
              else match seq11 with ""
              in
              (l1, r1)
    let work13 =
      lam c40.
        lam l2.
          lam r2.
            lam seq12.
              match seq12 with [ _ ] ++ _
              then
                let s43 = get seq12 0 in
                match splitAt seq12 1 with {#label"1" = x379}
                in
                let seq22 = x379 in
                match anon19 c40 s43 with true
                then
                  work11 c40 (cons s43 l2) r2 seq22
                else
                  work13 c40 l2 (cons s43 r2) seq22
              else match seq12 with ""
              in
              (l2, r2)
    let work14 =
      lam c41.
        lam l3.
          lam r3.
            lam seq13.
              match seq13 with [ _ ] ++ _
              then
                let s44 = get seq13 0 in
                match splitAt seq13 1 with {#label"1" = x380}
                in
                let seq23 = x380 in
                match anon19 c41 s44 with true
                then
                  work12 c41 (cons s44 l3) r3 seq23
                else
                  work13 c41 l3 (cons s44 r3) seq23
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
          match lr with (#var"X2",)
          in
          match lr with {#label"1" = #var"X3"}
          in
          concat (quickSort #var"X2") (cons h (quickSort #var"X3"))
    let quickSort1 =
      lam st233.
        lam seq31.
          p_map
            st233
            (lam x383.
               match null x383 with true
               then
                 x383
               else
                 let h1 = head x383 in
                 let lr1 = work14 h1 "" "" (reverse (tail x383)) in
                 match lr1 with (#var"X4",)
                 in
                 match lr1 with {#label"1" = #var"X5"}
                 in
                 concat (quickSort #var"X4") (cons h1 (quickSort #var"X5")))
            seq31
  in
  recursive
    let rec212 =
      lam st234.
        lam c42.
          lam c43.
            lam c44.
              lam c45.
                lam c46.
                  lam c47.
                    lam acc18.
                      lam s213.
                        match s213 with [ _ ] ++ _
                        then
                          let x384 = get s213 0 in
                          match
                            p_map
                              st234
                              (lam x385.
                                 lam x386.
                                   addf x385 x386)
                              acc18
                          with
                            (st235, x387)
                          in
                          match
                            hostIndepLikelihood
                              st235
                              1
                              (get c42 (subi x384 1))
                              (get c43 (subi x384 1))
                              c44
                              c45
                              (get c47 (subi x384 1))
                              (match c46 with ModelParams1 x1191
                               then
                                 x1191.embeddedQMatrix
                               else
                                 let #var"153" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st236, x388)
                          in
                          match p_apply st236 x387 x388 with (st237, x389)
                          in
                          match splitAt s213 1 with {#label"1" = x390}
                          in
                          rec212 st237 c42 c43 c44 c45 c46 c47 x389 x390
                        else match s213 with ""
                        in
                        (st234, acc18)
    let rec213 =
      lam st238.
        lam c48.
          lam c49.
            lam c50.
              lam c51.
                lam c52.
                  lam c53.
                    lam acc19.
                      lam s214.
                        match s214 with [ _ ] ++ _
                        then
                          let x393 = get s214 0 in
                          match
                            p_map
                              st238
                              (lam x394.
                                 lam x395.
                                   addf x394 x395)
                              acc19
                          with
                            (st239, x396)
                          in
                          match
                            hostIndepLikelihood2
                              st239
                              1
                              (get c48 (subi x393 1))
                              (get c49 (subi x393 1))
                              c50
                              c51
                              (get c53 (subi x393 1))
                              (match c52 with ModelParams1 x1192
                               then
                                 x1192.embeddedQMatrix
                               else
                                 let #var"154" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st240, x397)
                          in
                          match p_apply st240 x396 x397 with (st241, x398)
                          in
                          match splitAt s214 1 with {#label"1" = x399}
                          in
                          rec213 st241 c48 c49 c50 c51 c52 c53 x398 x399
                        else match s214 with ""
                        in
                        (st238, acc19)
  in
  let anon20 = lam x689.
      addi x689 1 in
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
    let rec214 =
      lam st242.
        lam acc20.
          lam s215.
            match s215 with [ _ ] ++ _
            then
              match
                p_map
                  st242
                  (lam x400.
                     lam x403.
                       addf x400 x403)
                  acc20
              with
                (st243, x404)
              in
              match p_apply st243 x404 (get s215 0) with (st244, x405)
              in
              match splitAt s215 1 with {#label"1" = x406}
              in
              rec214 st244 x405 x406
            else match s215 with ""
            in
            (st242, acc20)
  in
  let fold2 =
    lam st411.
      lam init11.
        lam seq51.
          match seq51 with [ _ ] ++ _
          then
            match
              p_map
                st411
                (lam x686.
                   addf init11 x686)
                (get seq51 0)
            with
              (st412, x687)
            in
            match splitAt seq51 1 with {#label"1" = x688}
            in
            rec214 st412 x687 x688
          else match seq51 with ""
          in
          (st411, p_pure init11)
  in
  recursive
    let rec215 =
      lam st245.
        lam c54.
          lam acc23.
            lam s216.
              match s216 with [ _ ] ++ _
              then
                match acc23 with (field2, field3)
                in
                match
                  match field3 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st245
                        (lam x407.
                           addi x407 1)
                        (get field3 0)
                    with
                      (st246, x408)
                    in
                    match mtxGet1 st246 x408 (addi (get s216 0) 1) c54 with (st247, x409)
                    in
                    match log11 st247 x409 with (st248, x410)
                    in
                    match splitAt field3 1 with {#label"1" = x411}
                    in
                    (st248, (snoc field2 x410, x411))
                  else
                    let x412 = error "foldl2: Cannot happen!" in
                    match x412 with (x413,)
                    in
                    match x412 with {#label"1" = x414}
                    in
                    (st245, (map (lam x415.
                         p_pure x415) x413, map (lam x416.
                         p_pure x416) x414))
                with
                  (st249, x417)
                in
                match splitAt s216 1 with {#label"1" = x418}
                in
                rec215 st249 c54 x417 x418
              else match s216 with ""
              in
              (st245, acc23)
    let rec216 =
      lam st250.
        lam c55.
          lam acc24.
            lam s217.
              match s217 with [ _ ] ++ _
              then
                match acc24 with (field4, field5)
                in
                match
                  match field5 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st250
                        (lam x419.
                           addi x419 1)
                        (get field5 0)
                    with
                      (st251, x420)
                    in
                    match
                      p_map
                        st251
                        (lam x421.
                           addi x421 1)
                        (get s217 0)
                    with
                      (st252, x422)
                    in
                    match mtxGet2 st252 x420 x422 c55 with (st253, x423)
                    in
                    match log11 st253 x423 with (st254, x424)
                    in
                    match splitAt field5 1 with {#label"1" = x425}
                    in
                    (st254, (snoc field4 x424, x425))
                  else
                    let x426 = error "foldl2: Cannot happen!" in
                    match x426 with (x427,)
                    in
                    match x426 with {#label"1" = x428}
                    in
                    (st250, (map (lam x429.
                         p_pure x429) x427, map (lam x430.
                         p_pure x430) x428))
                with
                  (st255, x431)
                in
                match splitAt s217 1 with {#label"1" = x432}
                in
                rec216 st255 c55 x431 x432
              else match s217 with ""
              in
              (st250, acc24)
  in
  recursive
    let rec217 =
      lam st256.
        lam c56.
          lam acc25.
            lam s218.
              match s218 with [ _ ] ++ _
              then
                match acc25 with (field6, field7)
                in
                match
                  match field7 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st256
                        (lam x433.
                           addi x433 1)
                        (get s218 0)
                    with
                      (st257, x434)
                    in
                    match mtxGet1 st257 x434 (addi (get field7 0) 1) c56 with (st258, x435)
                    in
                    match log11 st258 x435 with (st259, x436)
                    in
                    match splitAt field7 1 with {#label"1" = x437}
                    in
                    (st259, (snoc field6 x436, x437))
                  else
                    let x438 = error "foldl2: Cannot happen!" in
                    match x438 with (x439,)
                    in
                    match x438 with {#label"1" = x440}
                    in
                    (st256, (map (lam x441.
                         p_pure x441) x439, x440))
                with
                  (st260, x442)
                in
                match splitAt s218 1 with {#label"1" = x443}
                in
                rec217 st260 c56 x442 x443
              else match s218 with ""
              in
              (st256, acc25)
    let rec218 =
      lam st261.
        lam c57.
          lam acc26.
            lam s219.
              match s219 with [ _ ] ++ _
              then
                match acc26 with (field8, field9)
                in
                match
                  match field9 with [ _ ] ++ _
                  then
                    match
                      p_map
                        st261
                        (lam x444.
                           addi x444 1)
                        (get s219 0)
                    with
                      (st262, x445)
                    in
                    match
                      p_map
                        st262
                        (lam x446.
                           addi x446 1)
                        (get field9 0)
                    with
                      (st263, x447)
                    in
                    match mtxGet2 st263 x445 x447 c57 with (st264, x448)
                    in
                    match log11 st264 x448 with (st265, x449)
                    in
                    match splitAt field9 1 with {#label"1" = x450}
                    in
                    (st265, (snoc field8 x449, x450))
                  else
                    let x451 = error "foldl2: Cannot happen!" in
                    match x451 with (x452,)
                    in
                    match x451 with {#label"1" = x453}
                    in
                    (st261, (map (lam x454.
                         p_pure x454) x452, map (lam x455.
                         p_pure x455) x453))
                with
                  (st266, x456)
                in
                match splitAt s219 1 with {#label"1" = x457}
                in
                rec218 st266 c57 x456 x457
              else match s219 with ""
              in
              (st261, acc26)
  in
  recursive
    let sampleTreeHistory =
      lam st267.
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
                          match tree2 with MsgLeaf x548
                          then
                            x548.interactions
                          else
                            let #var"168" =
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
                            let #var"167" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 127:6-127:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                            in
                            exit 1
                        in
                        match
                          rec9
                            st267
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
                               let #var"155" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:6-129:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create13 (addi (subi nHosts 1) 1))
                        with
                          (st268, unorderedBranch)
                        in
                        match paste0 st268 unorderedBranch with (st269, x458)
                        in
                        match quickSort1 st269 x458 with (st270, orderedEvents)
                        in
                        match length13 st270 orderedEvents with (st271, nEvents4)
                        in
                        match
                          allTimesValidBranch st271 parentRep orderedEvents 1 nEvents4 nHosts
                        with
                          (st272, x459)
                        in
                        match
                          p_bind
                            st272
                            hrmStoreSubmodel
                            (hrmInit {})
                            (lam st273.
                               lam x460.
                                 match
                                   match x460 with true
                                   then
                                     let s220 = create14 (addi (subi (length12 unorderedBranch) 1) 1)
                                     in
                                     match
                                       match s220 with [ _ ] ++ _
                                       then
                                         let x461 = get s220 0 in
                                         match
                                           hostIndepLikelihood
                                             st273
                                             1
                                             (get parentRep (subi x461 1))
                                             (get rep1 (subi x461 1))
                                             parentAge
                                             finalAge3
                                             (get unorderedBranch (subi x461 1))
                                             (match modelParams11 with ModelParams1 x1193
                                              then
                                                x1193.embeddedQMatrix
                                              else
                                                let #var"156" =
                                                  print
                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                                in
                                                exit 1)
                                         with
                                           (st274, x462)
                                         in
                                         match
                                           p_map
                                             st274
                                             (lam x463.
                                                addf 0. x463)
                                             x462
                                         with
                                           (st275, x464)
                                         in
                                         match splitAt s220 1 with {#label"1" = x465}
                                         in
                                         rec212
                                           st275
                                           parentRep
                                           rep1
                                           parentAge
                                           finalAge3
                                           modelParams11
                                           unorderedBranch
                                           x464
                                           x465
                                       else match s220 with ""
                                       in
                                       (st273, p_pure 0.)
                                     with
                                       (st276, x466)
                                     in
                                     match
                                       p_map
                                         st276
                                         (lam x467.
                                            lam x468.
                                              subf x467 x468)
                                         x466
                                     with
                                       (st277, x469)
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
                                                     st277
                                                     (lam x470.
                                                        addi x470 1)
                                                     (get field11 0)
                                                 with
                                                   (st278, x471)
                                                 in
                                                 match
                                                   mtxGet1 st278 x471 (addi (get rep1 0) 1) branchKernel
                                                 with
                                                   (st279, x472)
                                                 in
                                                 match log11 st279 x472 with (st280, x473)
                                                 in
                                                 match splitAt field11 1 with {#label"1" = x474}
                                                 in
                                                 (st280, (snoc field10 x473, x474))
                                               else
                                                 let x475 = error "foldl2: Cannot happen!" in
                                                 match x475 with (x476,)
                                                 in
                                                 match x475 with {#label"1" = x477}
                                                 in
                                                 (st277, (map
                                                   (lam x478.
                                                      p_pure x478)
                                                   x476, map
                                                   (lam x479.
                                                      p_pure x479)
                                                   x477))
                                             with
                                               (st281, x480)
                                             in
                                             match splitAt rep1 1 with {#label"1" = x481}
                                             in
                                             rec215 st281 branchKernel x480 x481
                                           else match rep1 with ""
                                           in
                                           (st277, acc27)
                                         with
                                           (st282, x482)
                                         in
                                         match x482 with (field12, field13)
                                         in
                                         (st282, field12)
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
                                                     st277
                                                     (lam x483.
                                                        addi x483 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st283, x484)
                                                 in
                                                 match
                                                   mtxGet1 st283 x484 (addi (get field15 0) 1) branchKernel
                                                 with
                                                   (st284, x485)
                                                 in
                                                 match log11 st284 x485 with (st285, x486)
                                                 in
                                                 match splitAt field15 1 with {#label"1" = x487}
                                                 in
                                                 (st285, (snoc field14 x486, x487))
                                               else
                                                 let x488 = error "foldl2: Cannot happen!" in
                                                 match x488 with (x489,)
                                                 in
                                                 match x488 with {#label"1" = x490}
                                                 in
                                                 (st277, (map
                                                   (lam x491.
                                                      p_pure x491)
                                                   x489, x490))
                                             with
                                               (st286, x492)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x493}
                                             in
                                             rec217 st286 branchKernel x492 x493
                                           else match parentRep with ""
                                           in
                                           (st277, acc28)
                                         with
                                           (st287, x494)
                                         in
                                         match x494 with (field16, field17)
                                         in
                                         (st287, field16)
                                     with
                                       (st288, x495)
                                     in
                                     match fold2 st288 0. x495 with (st289, x496)
                                     in
                                     match p_apply st289 x469 x496 with (st290, x497)
                                     in
                                     match
                                       p_bind
                                         st290
                                         hrmStoreSubmodel
                                         (hrmInit {})
                                         (lam st291.
                                            lam x498.
                                              match gti 1 x498 with true
                                              then
                                                match
                                                  getTotalRate st291 parentRep modelParams11 nHosts
                                                with
                                                  (st292, x499)
                                                in
                                                p_map
                                                  st292
                                                  (lam x500.
                                                     mulf (negf (subf parentAge finalAge3)) x500)
                                                  x499
                                              else match
                                                p_map
                                                  st291
                                                  (lam x501.
                                                     get x501 (subi 1 1))
                                                  orderedEvents
                                              with
                                                (st293, nextEvent2)
                                              in
                                              match
                                                p_map
                                                  st293
                                                  (lam x502.
                                                     match x502 with Event1 x3110
                                                     then
                                                       x3110.eventTime
                                                     else
                                                       let #var"157" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st294, newAge2)
                                              in
                                              match
                                                getTotalRate st294 parentRep modelParams11 nHosts
                                              with
                                                (st295, totalLeavingRate12)
                                              in
                                              match
                                                p_map
                                                  st295
                                                  (lam x503.
                                                     match x503 with Event1 x1323
                                                     then
                                                       x1323.host
                                                     else
                                                       let #var"158" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st296, hostIndex12)
                                              in
                                              match
                                                p_map
                                                  st296
                                                  (lam x504.
                                                     lam x505.
                                                       lam st297.
                                                         match
                                                           gti
                                                             (match x504 with Event1 x1303
                                                              then
                                                                x1303.fromState
                                                              else
                                                                let #var"159" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x505
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st297 parentRep hostIndex12 modelParams11
                                                         else
                                                           getGainRate2 st297 parentRep hostIndex12 modelParams11)
                                                  nextEvent2
                                              with
                                                (st298, x506)
                                              in
                                              match
                                                p_map
                                                  st298
                                                  (lam x507.
                                                     match x507 with Event1 x1313
                                                     then
                                                       x1313.toState
                                                     else
                                                       let #var"160" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                       in
                                                       exit 1)
                                                  nextEvent2
                                              with
                                                (st299, x508)
                                              in
                                              match
                                                p_subApply st299 hrmStoreSubmodel (hrmInit {}) x506 x508
                                              with
                                                (st300, x509)
                                              in
                                              match p_join st300 x509 with (st301, x510)
                                              in
                                              match
                                                p_map
                                                  st301
                                                  (lam x511.
                                                     lam x512.
                                                       divf x511 x512)
                                                  x510
                                              with
                                                (st302, x513)
                                              in
                                              match p_apply st302 x513 totalLeavingRate12 with (st303, x514)
                                              in
                                              match log11 st303 x514 with (st304, x515)
                                              in
                                              match
                                                p_map
                                                  st304
                                                  (lam x516.
                                                     lam x517.
                                                       lam x518.
                                                         addf (subf x516 x517) x518)
                                                  x515
                                              with
                                                (st305, x519)
                                              in
                                              match
                                                p_map
                                                  st305
                                                  (lam x520.
                                                     lam x521.
                                                       mulf (subf parentAge x520) x521)
                                                  newAge2
                                              with
                                                (st306, x522)
                                              in
                                              match p_apply st306 x522 totalLeavingRate12 with (st307, x523)
                                              in
                                              match p_apply st307 x519 x523 with (st308, x524)
                                              in
                                              match
                                                updateRepertoire st308 parentRep nextEvent2 nHosts
                                              with
                                                (st309, x525)
                                              in
                                              match
                                                fullModelWeight
                                                  st309
                                                  (addi 1 1)
                                                  x525
                                                  rep1
                                                  newAge2
                                                  finalAge3
                                                  orderedEvents
                                                  x498
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st310, x526)
                                              in
                                              p_apply st310 x524 x526)
                                         nEvents4
                                     with
                                       (st311, x527)
                                     in
                                     (st311, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = x497,
                                         logModelDensity = x527,
                                         success = true })
                                   else
                                     (st273, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = p_pure (log1 0.),
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st312, x528)
                                 in
                                 match x528 with CorrectedBranchSample1 x529
                                 in
                                 match x529 with {history = x530}
                                 in
                                 match
                                   p_map
                                     st312
                                     (lam x531.
                                        lam x532.
                                          lam x533.
                                            match x529 with {success = x534}
                                            in
                                            CorrectedBranchSample1
                                              { history = x531,
                                                logSamplingDensity = x532,
                                                logModelDensity = x533,
                                                success = x534 })
                                     x530
                                 with
                                   (st313, x535)
                                 in
                                 match x529 with {logSamplingDensity = x536}
                                 in
                                 match p_apply st313 x535 x536 with (st314, x537)
                                 in
                                 match x529 with {logModelDensity = x538}
                                 in
                                 p_apply st314 x537 x538)
                            x459
                        with
                          (st315, branchSample)
                        in
                        match
                          p_map
                            st315
                            (lam x539.
                               lam x540.
                                   (subf
                                      (match x539 with CorrectedBranchSample1 x4610
                                       then
                                         x4610.logModelDensity
                                       else
                                         let #var"161" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 135:15-135:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x540))
                            branchSample
                        with
                          (st316, x541)
                        in
                        match
                          p_map
                            st316
                            (lam x542.
                               match x542 with CorrectedBranchSample1 x4710
                               then
                                 x4710.logSamplingDensity
                               else
                                 let #var"163" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 135:46-135:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st317, x543)
                        in
                        match p_apply st317 x541 x543 with (st318, x544)
                        in
                        let st319 =
                          p_weight
                            st318
                            (hrmStoreLikrWeight (match tree2 with MsgLeaf carried26
                                             then
                                               carried26.label
                                             else match tree2 with MsgNode carried27
                                             then
                                               carried27.label
                                             else
                                               let #var"162" =
                                                 print
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 135:90-135:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1))
                            (/-temp-/lam x547.
                               x547)
                            x544
                        in
                        let foo = {} in
                        match
                          p_map
                            st319
                            (lam x545.
                               match x545 with CorrectedBranchSample1 x4510
                               then
                                 x4510.history
                               else
                                 let #var"164" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 141:16-141:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st320, x546)
                        in
                        (st320, HistoryLeaf
                          { age =
                              match tree2 with MsgLeaf carried28
                              then
                                carried28.age
                              else match tree2 with MsgNode carried29
                              then
                                carried29.age
                              else
                                let #var"165" =
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
                                let #var"166" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 139:14-139:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            history = x546,
                            repertoire = rep1 })
                      else
                        let samplingProb =
                          mtxElemMul
                            (match tree2 with MsgLeaf carried52
                             then
                               carried52.outMsg
                             else match tree2 with MsgNode carried53
                             then
                               carried53.outMsg
                             else
                               let #var"192" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 144:34-144:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                               in
                               exit 1)
                            preorderMsg
                        in
                        match
                          suggestNodeRep
                            st267
                            samplingProb
                            nHosts
                            (match tree2 with MsgLeaf carried34
                             then
                               carried34.label
                             else match tree2 with MsgNode carried35
                             then
                               carried35.label
                             else
                               let #var"169" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 145:51-145:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                               in
                               exit 1)
                        with
                          (st321, rep2)
                        in
                        match any1 st321 rep2 with (st322, x549)
                        in
                        match bool2real st322 x549 with (st323, x550)
                        in
                        let st324 =
                          p_weight
                            st323
                            (hrmStoreBranchSuppWeight (match tree2 with MsgLeaf carried50
                                           then
                                             carried50.label
                                           else match tree2 with MsgNode carried51
                                           then
                                             carried51.label
                                           else
                                             let #var"191" =
                                               print
                                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 147:43-147:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                             in
                                             exit 1))
                            (lam x655.
                               externalLog
                                    x655)
                            x550
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
                            let #var"190" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 155:6-155:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                            in
                            exit 1
                        in
                        match
                          rec10
                            st324
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
                               let #var"170" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:6-157:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create13 (addi (subi nHosts 1) 1))
                        with
                          (st325, unorderedBranch1)
                        in
                        match paste0 st325 unorderedBranch1 with (st326, x551)
                        in
                        match quickSort1 st326 x551 with (st327, orderedEvents1)
                        in
                        match length13 st327 orderedEvents1 with (st328, nEvents41)
                        in
                        match
                          allTimesValidBranch st328 parentRep orderedEvents1 1 nEvents41 nHosts
                        with
                          (st329, x552)
                        in
                        match
                          p_bind
                            st329
                            hrmStoreSubmodel
                            (hrmInit {})
                            (lam st330.
                               lam x553.
                                 match
                                   match x553 with true
                                   then
                                     let s221 = create14 (addi (subi (length12 unorderedBranch1) 1) 1)
                                     in
                                     match
                                       match s221 with [ _ ] ++ _
                                       then
                                         let x554 = get s221 0 in
                                         match
                                           hostIndepLikelihood2
                                             st330
                                             1
                                             (get parentRep (subi x554 1))
                                             (get rep2 (subi x554 1))
                                             parentAge
                                             finalAge31
                                             (get unorderedBranch1 (subi x554 1))
                                             (match modelParams11 with ModelParams1 x1194
                                              then
                                                x1194.embeddedQMatrix
                                              else
                                                let #var"171" =
                                                  print
                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                                in
                                                exit 1)
                                         with
                                           (st331, x555)
                                         in
                                         match
                                           p_map
                                             st331
                                             (lam x556.
                                                addf 0. x556)
                                             x555
                                         with
                                           (st332, x557)
                                         in
                                         match splitAt s221 1 with {#label"1" = x558}
                                         in
                                         rec213
                                           st332
                                           parentRep
                                           rep2
                                           parentAge
                                           finalAge31
                                           modelParams11
                                           unorderedBranch1
                                           x557
                                           x558
                                       else match s221 with ""
                                       in
                                       (st330, p_pure 0.)
                                     with
                                       (st333, x559)
                                     in
                                     match
                                       p_map
                                         st333
                                         (lam x560.
                                            lam x561.
                                              subf x560 x561)
                                         x559
                                     with
                                       (st334, x562)
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
                                                     st334
                                                     (lam x563.
                                                        addi x563 1)
                                                     (get field19 0)
                                                 with
                                                   (st335, x564)
                                                 in
                                                 match
                                                   p_map
                                                     st335
                                                     (lam x565.
                                                        addi x565 1)
                                                     (get rep2 0)
                                                 with
                                                   (st336, x566)
                                                 in
                                                 match mtxGet2 st336 x564 x566 branchKernel with (st337, x567)
                                                 in
                                                 match log11 st337 x567 with (st338, x568)
                                                 in
                                                 match splitAt field19 1 with {#label"1" = x569}
                                                 in
                                                 (st338, (snoc field18 x568, x569))
                                               else
                                                 let x570 = error "foldl2: Cannot happen!" in
                                                 match x570 with (x571,)
                                                 in
                                                 match x570 with {#label"1" = x572}
                                                 in
                                                 (st334, (map
                                                   (lam x573.
                                                      p_pure x573)
                                                   x571, map
                                                   (lam x574.
                                                      p_pure x574)
                                                   x572))
                                             with
                                               (st339, x575)
                                             in
                                             match splitAt rep2 1 with {#label"1" = x576}
                                             in
                                             rec216 st339 branchKernel x575 x576
                                           else match rep2 with ""
                                           in
                                           (st334, acc29)
                                         with
                                           (st340, x577)
                                         in
                                         match x577 with (field20, field21)
                                         in
                                         (st340, field20)
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
                                                     st334
                                                     (lam x578.
                                                        addi x578 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st341, x579)
                                                 in
                                                 match
                                                   p_map
                                                     st341
                                                     (lam x580.
                                                        addi x580 1)
                                                     (get field23 0)
                                                 with
                                                   (st342, x581)
                                                 in
                                                 match mtxGet2 st342 x579 x581 branchKernel with (st343, x582)
                                                 in
                                                 match log11 st343 x582 with (st344, x583)
                                                 in
                                                 match splitAt field23 1 with {#label"1" = x584}
                                                 in
                                                 (st344, (snoc field22 x583, x584))
                                               else
                                                 let x585 = error "foldl2: Cannot happen!" in
                                                 match x585 with (x586,)
                                                 in
                                                 match x585 with {#label"1" = x587}
                                                 in
                                                 (st334, (map
                                                   (lam x588.
                                                      p_pure x588)
                                                   x586, map
                                                   (lam x589.
                                                      p_pure x589)
                                                   x587))
                                             with
                                               (st345, x590)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x591}
                                             in
                                             rec218 st345 branchKernel x590 x591
                                           else match parentRep with ""
                                           in
                                           (st334, acc30)
                                         with
                                           (st346, x592)
                                         in
                                         match x592 with (field24, field25)
                                         in
                                         (st346, field24)
                                     with
                                       (st347, x593)
                                     in
                                     match fold2 st347 0. x593 with (st348, x594)
                                     in
                                     match p_apply st348 x562 x594 with (st349, x595)
                                     in
                                     match
                                       p_bind
                                         st349
                                         hrmStoreSubmodel
                                         (hrmInit {})
                                         (lam st350.
                                            lam x596.
                                              match gti 1 x596 with true
                                              then
                                                match
                                                  getTotalRate st350 parentRep modelParams11 nHosts
                                                with
                                                  (st351, x597)
                                                in
                                                p_map
                                                  st351
                                                  (lam x598.
                                                     mulf (negf (subf parentAge finalAge31)) x598)
                                                  x597
                                              else match
                                                p_map
                                                  st350
                                                  (lam x599.
                                                     get x599 (subi 1 1))
                                                  orderedEvents1
                                              with
                                                (st352, nextEvent3)
                                              in
                                              match
                                                p_map
                                                  st352
                                                  (lam x600.
                                                     match x600 with Event1 x3111
                                                     then
                                                       x3111.eventTime
                                                     else
                                                       let #var"172" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent3
                                              with
                                                (st353, newAge3)
                                              in
                                              match
                                                getTotalRate st353 parentRep modelParams11 nHosts
                                              with
                                                (st354, totalLeavingRate13)
                                              in
                                              match
                                                p_map
                                                  st354
                                                  (lam x601.
                                                     match x601 with Event1 x1324
                                                     then
                                                       x1324.host
                                                     else
                                                       let #var"173" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                       in
                                                       exit 1)
                                                  nextEvent3
                                              with
                                                (st355, hostIndex13)
                                              in
                                              match
                                                p_map
                                                  st355
                                                  (lam x602.
                                                     lam x603.
                                                       lam st356.
                                                         match
                                                           gti
                                                             (match x602 with Event1 x1304
                                                              then
                                                                x1304.fromState
                                                              else
                                                                let #var"174" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x603
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st356 parentRep hostIndex13 modelParams11
                                                         else
                                                           getGainRate2 st356 parentRep hostIndex13 modelParams11)
                                                  nextEvent3
                                              with
                                                (st357, x604)
                                              in
                                              match
                                                p_map
                                                  st357
                                                  (lam x605.
                                                     match x605 with Event1 x1314
                                                     then
                                                       x1314.toState
                                                     else
                                                       let #var"175" =
                                                         print
                                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                       in
                                                       exit 1)
                                                  nextEvent3
                                              with
                                                (st358, x606)
                                              in
                                              match
                                                p_subApply st358 hrmStoreSubmodel (hrmInit {}) x604 x606
                                              with
                                                (st359, x607)
                                              in
                                              match p_join st359 x607 with (st360, x608)
                                              in
                                              match
                                                p_map
                                                  st360
                                                  (lam x609.
                                                     lam x610.
                                                       divf x609 x610)
                                                  x608
                                              with
                                                (st361, x611)
                                              in
                                              match p_apply st361 x611 totalLeavingRate13 with (st362, x612)
                                              in
                                              match log11 st362 x612 with (st363, x613)
                                              in
                                              match
                                                p_map
                                                  st363
                                                  (lam x614.
                                                     lam x615.
                                                       lam x616.
                                                         addf (subf x614 x615) x616)
                                                  x613
                                              with
                                                (st364, x617)
                                              in
                                              match
                                                p_map
                                                  st364
                                                  (lam x618.
                                                     lam x619.
                                                       mulf (subf parentAge x618) x619)
                                                  newAge3
                                              with
                                                (st365, x620)
                                              in
                                              match p_apply st365 x620 totalLeavingRate13 with (st366, x621)
                                              in
                                              match p_apply st366 x617 x621 with (st367, x622)
                                              in
                                              match
                                                updateRepertoire st367 parentRep nextEvent3 nHosts
                                              with
                                                (st368, x623)
                                              in
                                              match
                                                fullModelWeight1
                                                  st368
                                                  (addi 1 1)
                                                  x623
                                                  rep2
                                                  newAge3
                                                  finalAge31
                                                  orderedEvents1
                                                  x596
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st369, x624)
                                              in
                                              p_apply st369 x622 x624)
                                         nEvents41
                                     with
                                       (st370, x625)
                                     in
                                     (st370, CorrectedBranchSample1
                                       { history = orderedEvents1,
                                         logSamplingDensity = x595,
                                         logModelDensity = x625,
                                         success = true })
                                   else
                                     (st330, CorrectedBranchSample1
                                       { history = orderedEvents1,
                                         logSamplingDensity = p_pure (log1 0.),
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st371, x626)
                                 in
                                 match x626 with CorrectedBranchSample1 x627
                                 in
                                 match x627 with {history = x628}
                                 in
                                 match
                                   p_map
                                     st371
                                     (lam x629.
                                        lam x630.
                                          lam x631.
                                            match x627 with {success = x632}
                                            in
                                            CorrectedBranchSample1
                                              { history = x629,
                                                logSamplingDensity = x630,
                                                logModelDensity = x631,
                                                success = x632 })
                                     x628
                                 with
                                   (st372, x633)
                                 in
                                 match x627 with {logSamplingDensity = x634}
                                 in
                                 match p_apply st372 x633 x634 with (st373, x635)
                                 in
                                 match x627 with {logModelDensity = x636}
                                 in
                                 p_apply st373 x635 x636)
                            x552
                        with
                          (st374, branchSample1)
                        in
                        match
                          p_map
                            st374
                            (lam x637.
                               lam x638.
                                 lam x639.
                                   subf
                                     (subf
                                        (match x637 with CorrectedBranchSample1 x701
                                         then
                                           x701.logModelDensity
                                         else
                                           let #var"176" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 163:14-163:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                           in
                                           exit 1)
                                        x638)
                                     x639)
                            branchSample1
                        with
                          (st375, x640)
                        in
                        match
                          p_map
                            st375
                            (lam x641.
                               match x641 with CorrectedBranchSample1 x711
                               then
                                 x711.logSamplingDensity
                               else
                                 let #var"177" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 163:45-163:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample1
                        with
                          (st376, x642)
                        in
                        match p_apply st376 x640 x642 with (st377, x643)
                        in
                        match
                          getRepertoireSamplingDensity st377 rep2 samplingProb nHosts
                        with
                          (st378, x644)
                        in
                        match
                          p_map
                            st378
                            (lam x645. x645)
                            x644
                        with
                          (st379, x646)
                        in
                        match p_apply st379 x643 x646 with (st380, x647)
                        in
                        let st381 =
                          p_weight
                            st380
                            (hrmStoreLikrWeight (match tree2 with MsgLeaf carried38
                                           then
                                             carried38.label
                                           else match tree2 with MsgNode carried39
                                           then
                                             carried39.label
                                           else
                                             let #var"178" =
                                               print
                                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 163:113-163:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                             in
                                             exit 1))
                            (/-temp-/lam x654.
                               x654)
                            x647
                        in
                      let fetchLabel = lam n. match n with MsgNode n then n.label else match n with MsgLeaf n in n.label in
                      match p_export
                        st381
                        (hrmStoreLocTopo
                          ( match tree2 with MsgNode n in n.label
                          , match tree2 with MsgNode n in fetchLabel n.left
                          , match tree2 with MsgNode n in fetchLabel n.right
                          , false
                          )
                          ) (p_pure true) with st381 in
                        let foo2 = {} in
                        match observationMessage1 st381 rep2 1 nHosts with (st382, x648)
                        in
                        match mtxCreate1 st382 nHosts 3 x648 with (st383, newMsg)
                        in
                        match
                          sampleTreeHistory
                            st383
                            (match tree2 with MsgNode x649
                             then
                               x649.left
                             else
                               let #var"179" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 172:6-172:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                               in
                               exit 1)
                            nHosts
                            (mtxMul
                               newMsg
                               (match tree2 with MsgNode x691
                                then
                                  x691.leftKernel
                                else
                                  let #var"180" =
                                    print
                                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 167:33-167:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                                  in
                                  exit 1))
                            rep2
                            (match tree2 with MsgLeaf carried40
                             then
                               carried40.age
                             else match tree2 with MsgNode carried41
                             then
                               carried41.age
                             else
                               let #var"181" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 172:39-172:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                               in
                               exit 1)
                            modelParams11
                            (match tree2 with MsgNode x671
                             then
                               x671.leftKernel
                             else
                               let #var"182" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 172:62-172:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                               in
                               exit 1)
                        with
                          (st384, x650)
                        in

                        match
                          sampleTreeHistory
                            st384
                            (match tree2 with MsgNode x6010
                             then
                               x6010.right
                             else
                               let #var"183" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 175:6-175:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                               in
                               exit 1)
                            nHosts
                            (mtxMul
                               newMsg
                               (match tree2 with MsgNode x681
                                then
                                  x681.rightKernel
                                else
                                  let #var"184" =
                                    print
                                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 168:34-168:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                                  in
                                  exit 1))
                            rep2
                            (match tree2 with MsgLeaf carried42
                             then
                               carried42.age
                             else match tree2 with MsgNode carried43
                             then
                               carried43.age
                             else
                               let #var"185" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 175:41-175:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                               in
                               exit 1)
                            modelParams11
                            (match tree2 with MsgNode x6310
                             then
                               x6310.rightKernel
                             else
                               let #var"186" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 175:64-175:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                               in
                               exit 1)
                        with
                          (st385, x651)
                        in
                        match
                          p_map
                            st385
                            (lam x652.
                               match x652 with CorrectedBranchSample1 x5910
                               then
                                 x5910.history
                               else
                                 let #var"187" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 182:16-182:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                                 in
                                 exit 1)
                            branchSample1
                        with
                          (st386, x653)
                        in
                        (st386, HistoryNode
                          { age =
                              match tree2 with MsgLeaf carried44
                              then
                                carried44.age
                              else match tree2 with MsgNode carried45
                              then
                                carried45.age
                              else
                                let #var"188" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 179:12-179:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                let #var"189" =
                                  print
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 180:14-180:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            left = x650,
                            right = x651,
                            history = x653,
                            repertoire = rep2 })
  in
  let input1 =
  { symbiontTree = Node
    { age = 10.0
    , label = 7
    , left = Node
      { label = 5
      , age = 5.0
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
      { label = 6
      , age = 5.0
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
  , interactions = [[2, 0], [1, 2], [2, 1], [2, 1]]
  , hostDistances = [[1., 1.], [1., 1.]]
  , dMean = 1.
  }
  in
  match input1 with {symbiontTree = #var"X6"}
  in
  let symbiontTree = #var"X6" in
  match input1 with {hostDistances = #var"X7"}
  in
  let hostDistances = #var"X7" in
  let nHosts1 = length11 hostDistances in
  match
    p_assume
      st hrmStoreLambda (p_pure (mkDirichlet [ 1., 1., 1., 1. ]))
  with
    (st387, lambda)
  in
  match
    p_assume st387 hrmStoreMu (p_pure (mkExponential 10.))
  with
    (st388, mu)
  in
  match
    p_assume st388 hrmStoreBeta (p_pure (mkExponential 1.))
  with
    (st389, beta)
  in
  match
    p_map
      st389
      (lam x656.
         subf 0. (get x656 (subi 1 1)))
      lambda
  with
    (st390, x657)
  in
  match
    p_map st390 (lam x658.
         get x658 (subi 1 1)) lambda
  with
    (st391, x659)
  in
  match
    p_map st391 (lam x660.
         get x660 (subi 2 1)) lambda
  with
    (st392, x661)
  in
  match
    p_map
      st392
      (lam x662.
         lam x663.
           subf 0. (addf (get x662 (subi 2 1)) x663))
      lambda
  with
    (st393, x664)
  in
  match
    p_map st393 (lam x665.
         get x665 (subi 3 1)) lambda
  with
    (st394, x666)
  in
  match p_apply st394 x664 x666 with (st395, x667)
  in
  match
    p_map st395 (lam x668.
         get x668 (subi 3 1)) lambda
  with
    (st396, x669)
  in
  match
    p_map st396 (lam x670.
         get x670 (subi 4 1)) lambda
  with
    (st397, x672)
  in
  match
    p_map
      st397
      (lam x673.
         subf 0. (get x673 (subi 4 1)))
      lambda
  with
    (st398, x674)
  in
  match
    mtxCreate1
      st398
      3
      3
      [ x657,
        x659,
        p_pure 0.,
        x661,
        x667,
        x669,
        p_pure 0.,
        x672,
        x674 ]
  with
    (st399, mtx4)
  in
  match mtx4 with {m = #var"X8"}
  in
  let m2 = #var"X8" in
  match mtx4 with {n = #var"X9"}
  in
  let n3 = #var"X9" in
  match mtx4 with {arr = #var"X10"}
  in
  let b14 = matMakeUninit (externalExtArrKind #var"X10") m2 n3 in
  let mn = muli m2 n3 in
  match mtx4 with {arr = #var"X11"}
  in
  match b14 with {arr = #var"X12"}
  in
  let #var"1110" = externalCblasCopy mn #var"X11" 1 #var"X12" 1
  in
  match
    p_map
      st399
      (lam x675.
         match b14 with {arr = #var"X13"}
         in
         externalCblasScal mn x675 #var"X13" 1)
      mu
  with
    (st400, #var"1210")
  in
  let qMatrix2 = b14 in
  match input1 with {interactions = #var"X14"}
  in
  let postorderTree = postorderTraverse symbiontTree qMatrix2 #var"X14" nHosts1
  in
  let rootSamplingProb =
    mtxElemMul
      (match postorderTree with MsgLeaf carried66
       then
         carried66.outMsg
       else match postorderTree with MsgNode carried67
       then
         carried67.outMsg
       else
         let #var"1105" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 39:36-39:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n"
         in
         exit 1)
      (mtxCreate nHosts1 3 (ones (muli 3 nHosts1)))
  in
  match
    suggestNodeRep
      st400
      rootSamplingProb
      nHosts1
      (match postorderTree with MsgLeaf carried54
       then
         carried54.label
       else match postorderTree with MsgNode carried55
       then
         carried55.label
       else
         let #var"193" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 40:57-40:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
         in
         exit 1)
  with
    (st401, rootRep)
  in
  match any1 st401 rootRep with (st402, x676)
  in
  match bool2real st402 x676 with (st403, x677)
  in
  let st404 =
    p_weight
      st403
      (hrmStoreBranchSuppWeight (match postorderTree with MsgLeaf carried64
                     then
                       carried64.label
                     else match postorderTree with MsgNode carried65
                     then
                       carried65.label
                     else
                       let #var"1104" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 42:45-42:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1))
      (lam x685.
         externalLog
            x685
      )
      x677
  in
  let foo3 = {} in
  match
    getRepertoireSamplingDensity st404 rootRep rootSamplingProb nHosts1
  with
    (st405, x678)
  in
  let st406 =
    p_weight
      st405
      (hrmStoreLikrWeight (match postorderTree with MsgLeaf carried62
                     then
                       carried62.label
                     else match postorderTree with MsgNode carried63
                    in
                       carried63.label
      ))
      (lam x684.
           (subf
              (negf
                 (log1
                    (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1)))))
              x684)
      )
      x678
  in
  let foo4 = {} in
  match observationMessage1 st406 rootRep 1 nHosts1 with (st407, x679)
  in
  match mtxCreate1 st407 nHosts1 3 x679 with (st408, newMsg1)
  in
  match input1 with {dMean = #var"X15"}
  in
  let q2 = negf (mtxGet 2 2 qMatrix2) in
  let modelParams2 =
    ModelParams1
      { beta = beta,
        meanDist = #var"X15",
        hostMetric =
          mtxCreate
            (length11 hostDistances)
            (length1 (get hostDistances (subi 1 1)))
            (match hostDistances with [ _ ] ++ _
             then
               match splitAt hostDistances 1 with {#label"1" = x683}
               in
               rec2 (concat "" (get hostDistances 0)) x683
             else match hostDistances with ""
             in
             ""),
        embeddedQMatrix =
          EmbeddedMarkovChainMatrix1
            { totalRates =
                [ negf (mtxGet 1 1 qMatrix2),
                  q2,
                  negf (mtxGet 3 3 qMatrix2) ],
              transitionProbs =
                [ [ 0., 1., 0. ],
                  [ divf (mtxGet 2 1 qMatrix2) q2,
                    0.,
                    divf (mtxGet 2 3 qMatrix2) q2 ],
                  [ 0., 1., 0. ] ],
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
      let #var"1102" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 65:16-65:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  let fetchLabel = lam n. match n with MsgNode n then n.label else match n with MsgLeaf n in n.label in
  match p_export
    st408
    (hrmStoreLocTopo
      ( match postorderTree with MsgNode n in n.label
      , match postorderTree with MsgNode n in fetchLabel n.left
      , match postorderTree with MsgNode n in fetchLabel n.right
      , true
      )
    ) (p_pure true) with st408 in
  match
    sampleTreeHistory
      st408
      (match postorderTree with MsgNode x901
       then
         x901.left
       else
         let #var"194" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 67:4-67:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
         in
         exit 1)
      nHosts1
      (mtxMul
         newMsg1
         (match postorderTree with MsgNode x951
          then
            x951.leftKernel
          else
            let #var"195" =
              print
                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 53:31-53:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
            in
            exit 1))
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x911
       then
         x911.leftKernel
       else
         let #var"196" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 67:72-67:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
         in
         exit 1)
  with
    (st409, x680)
  in
  match
    sampleTreeHistory
      st409
      (match postorderTree with MsgNode x881
       then
         x881.right
       else
         let #var"197" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 71:4-71:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
         in
         exit 1)
      nHosts1
      (mtxMul
         newMsg1
         (match postorderTree with MsgNode x941
          then
            x941.rightKernel
          else
            let #var"198" =
              print
                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 54:32-54:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
            in
            exit 1))
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x891
       then
         x891.rightKernel
       else
         let #var"199" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 71:74-71:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
         in
         exit 1)
  with
    (st410, x682)
  in
  match p_map st410 (lam mu. lam beta. lam lambda. {mu = mu, beta = beta, lambda = lambda}) mu with (st, partres) in
  match p_apply st partres beta with (st, partres) in
  match p_apply st partres lambda with (st410, res) in
  p_export
    st410
    hrmStoreExport
    res 