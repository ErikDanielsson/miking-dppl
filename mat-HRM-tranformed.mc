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
    lam st1016.
      lam a88.
        lam b30.
          p_select
            st1016
            (lam x1679.
               match x1679 with true
               then
                 b30
               else
                 p_pure false)
            a88
  in
  let pow = lam x1713.
      lam y2.
        externalPow x1713 y2
  in
  let pow1 =
    lam st1015.
      lam x1712.
        lam y1.
          p_map
            st1015 (lam x1678.
               externalPow x1712 x1678) y1
  in
  let pow2 =
    lam st1013.
      lam x1711.
        lam y.
          match
            p_map
              st1013
              (lam x1675.
                 lam x1676.
                   externalPow x1675 x1676)
              x1711
          with
            (st1014, x1677)
          in
          p_apply st1014 x1677 y
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
    let rec12 =
      lam st11.
        lam c2.
          lam i2.
            lam s12.
              match s12 with [ _,
                  _ ] ++ _
              then
                match
                  p_map
                    st11
                    (lam x17.
                       externalExtArrSet x17 i2 (get s12 0))
                    c2
                with
                  (st12, x18)
                in
                match splitAt s12 1 with {#label"1" = x19}
                in
                match rec12 st12 c2 (addi i2 1) x19 with (st13, x20)
                in
                (st13, cons x18 x20)
              else match s12 with [ e2 ]
              then
                match splitAt s12 1 with {#label"1" = x21}
                in
                let slice2 = x21 in
                match
                  p_map
                    st11
                    (lam x22.
                       externalExtArrSet x22 i2 e2)
                    c2
                with
                  (st14, x23)
                in
                (st14, [ x23 ])
              else match s12 with ""
              in
              (st11, "")
  in
  let matErrorToString =
    lam err3.
      match err3 with DimensionMismatch carried75
      in
      "Dimension mismatch"
  in
  let matMakeUninit =
    lam st1011.
      lam kind1.
        lam m41.
          lam n53.
            match
              p_map
                st1011
                (lam x1673.
                   externalExtArrMakeUninit kind1 (muli m41 x1673))
                n53
            with
              (st1012, x1674)
            in
            (st1012, { arr = x1674, n = n53, m = m41 })
  in
  let matMakeUninit1 =
    lam st1006.
      lam kind.
        lam m4.
          lam n52.
            match
              p_map
                st1006
                (lam x1665.
                   lam x1666.
                     externalExtArrMakeUninit x1665 x1666)
                kind
            with
              (st1007, x1667)
            in
            match
              p_map
                st1007
                (lam x1668.
                   lam x1669.
                     muli x1668 x1669)
                m4
            with
              (st1008, x1670)
            in
            match p_apply st1008 x1670 n52 with (st1009, x1671)
            in
            match p_apply st1009 x1667 x1671 with (st1010, x1672)
            in
            (st1010, { arr = x1672, n = n52, m = m4 })
  in
  let matGetExn =
    lam a67.
      lam i161.
        lam j1.
          match a67 with {arr = #var"X91"}
          in
          match a67 with {n = #var"X92"}
          in
          externalExtArrGet #var"X91" (addi (muli i161 #var"X92") j1)
  in
  let matHasSameShape2 =
    lam st1003.
      lam a611.
        lam b211.
          match
            p_map
              st1003
              (lam x1661.
                 match x1661 with {m = #var"X87"}
                 in
                 match b211 with {m = #var"X88"}
                 in
                 eqi #var"X87" #var"X88")
              a611
          with
            (st1004, x1662)
          in
          match
            p_map
              st1004
              (lam x1663.
                 match x1663 with {n = #var"X89"}
                 in
                 match b211 with {n = #var"X90"}
                 in
                 eqi #var"X89" #var"X90")
              a611
          with
            (st1005, x1664)
          in
          and st1005 x1662 x1664
  in
  let matHasSameShape21 =
    lam st996.
      lam a61.
        lam b21.
          match
            p_map
              st996
              (lam x1649.
                 lam x1650.
                   match x1649 with {m = #var"X85"}
                   in
                   eqi #var"X85" x1650)
              a61
          with
            (st997, x1651)
          in
          match
            p_map st997 (lam x1652.
                 x1652.m) b21
          with
            (st998, x1653)
          in
          match p_apply st998 x1651 x1653 with (st999, x1654)
          in
          match
            p_map
              st999
              (lam x1655.
                 lam x1656.
                   match x1655 with {n = #var"X86"}
                   in
                   eqi #var"X86" x1656)
              a61
          with
            (st1000, x1657)
          in
          match
            p_map st1000 (lam x1658.
                 x1658.n) b21
          with
            (st1001, x1659)
          in
          match p_apply st1001 x1657 x1659 with (st1002, x1660)
          in
          and st1002 x1654 x1660
  in
  let exp1 = lam x15910.
      externalExp x15910 in
  let log1 = lam x15811.
      externalLog x15811 in
  let log11 =
    lam st995.
      lam x15810.
        p_map st995 (lam x1648.
             externalLog x1648) x15810
  in
  let cons1 = lam e112.
      lam s83.
        cons e112 s83 in
  let cons11 =
    lam st991.
      lam e111.
        lam s82.
          match e111 with Event1 x1638
          in
          match x1638 with {toState = x1639}
          in
          match
            p_map
              st991
              (lam x1640.
                 lam x1641.
                   match x1638 with {host = x1642}
                   in
                   match x1638 with {eventTime = x1643}
                   in
                   Event1
                     { host = x1642,
                       toState = x1640,
                       eventTime = x1643,
                       fromState = x1641 })
              x1639
          with
            (st992, x1644)
          in
          match x1638 with {fromState = x1645}
          in
          match p_apply st992 x1644 x1645 with (st993, x1646)
          in
          match p_map st993 cons x1646 with (st994, x1647)
          in
          p_apply st994 x1647 s82
  in
  let cons12 = lam e110.
      lam s81.
        cons e110 s81 in
  let anon = lam elem11.
      lam x1637.
        elem11 in
  recursive
    let rec3 =
      lam c3.
        lam i11.
          lam acc11.
            match geqi i11 0 with true
            then
              rec3 c3 (subi i11 1) (cons (anon c3 i11) acc11)
            else
              acc11
  in
  let rep =
    lam count.
      lam elem1.
        let i115 = subi count 1 in
        match geqi i115 0 with true
        then
          rec3 elem1 (subi i115 1) (cons (anon elem1 i115) "")
        else
          ""
  in
  let paste0 =
    lam st985.
      lam l51.
        match l51 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st985
              (lam st986.
                 lam x1631.
                   (st986, x1631))
              ""
          with
            (st987, x1632)
          in
          match p_map st987 concat x1632 with (st988, x1633)
          in
          match p_apply st988 x1633 (get l51 0) with (st989, x1634)
          in
          match splitAt l51 1 with {#label"1" = x1635}
          in
          rec22 st989 x1634 x1635
        else match l51 with ""
        in
        p_traverseSeq
          st985
          (lam st990.
             lam x1636.
               (st990, x1636))
          ""
  in
  let paste01 =
    lam st979.
      lam l5.
        match l5 with [ _ ] ++ _
        then
          match
            p_traverseSeq
              st979
              (lam st980.
                 lam x1625.
                   (st980, x1625))
              ""
          with
            (st981, x1626)
          in
          match p_map st981 concat x1626 with (st982, x1627)
          in
          match p_apply st982 x1627 (get l5 0) with (st983, x1628)
          in
          match splitAt l5 1 with {#label"1" = x1629}
          in
          rec23 st983 x1628 x1629
        else match l5 with ""
        in
        p_traverseSeq
          st979
          (lam st984.
             lam x1630.
               (st984, x1630))
          ""
  in
  let slice3 =
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
  let length13 = lam st978.
      lam l31.
        p_map st978 length l31
  in
  let anon1 =
    lam x1622.
      lam x1623.
        lam x1624.
          match x1624 with true
          then
            snoc x1622 (addi x1623 1)
          else
            x1622
  in
  recursive
    let work =
      lam acc21.
        lam i21.
          lam s3.
            match s3 with [ e3 ] ++ rest
            then
              work
                (match e3 with true
                 then
                   snoc acc21 (addi i21 1)
                 else
                   acc21)
                (addi i21 1)
                rest
            else
              acc21
    let work1 =
      lam st15.
        lam acc22.
          lam i22.
            lam s31.
              match s31 with [ e4 ] ++ rest1
              then
                match
                  p_bind
                    st15
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st16.
                       lam x24.
                         match x24 with true
                         then
                           p_map
                             st16
                             (lam x25.
                                snoc x25 (addi i22 1))
                             acc22
                         else
                           (st16, acc22))
                    e4
                with
                  (st17, x26)
                in
                work1 st17 x26 (addi i22 1) rest1
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
    lam st975.
      lam s62.
        match s62 with [ e24 ] ++ rest3
        then
          match
            p_map
              st975
              (lam x1619.
                 match x1619 with true
                 then
                   snoc "" (addi 0 1)
                 else
                   "")
              e24
          with
            (st976, x1620)
          in
          work1 st976 x1620 (addi 0 1) rest3
        else
          p_traverseSeq
            st975
            (lam st977.
               lam x1621.
                 (st977, x1621))
            ""
  in
  let whichTrue2 =
    lam st974.
      lam s61.
        p_map
          st974
          (lam x1618.
             match x1618 with [ e23 ] ++ rest2
             then
               work (anon1 "" 0 e23) (addi 0 1) rest2
             else
               "")
          s61
  in
  let bool2real =
    lam st973.
      lam v.
        p_map
          st973
          (lam x1617.
             match x1617 with true
             then
               1.
             else
               0.)
          v
  in
  let mtxCreate =
    lam rows1.
      lam cols12.
        lam data2.
          let a702 = externalExtArrMakeUninit extArrKindFloat64 (length data2)
          in
          let #var"1914" = rec1 a702 0 data2 in
          let #var"1712" = {} in
          let a632 = a702 in
          match eqi (muli rows1 cols12) (externalExtArrLength a632) with true
          then
            { arr = a632, n = cols12, m = rows1 }
          else
            error "matFromArrExn: dimensions mismatch"
  in
  let mtxCreate1 =
    lam st971.
      lam rows.
        lam cols11.
          lam data1.
            let a701 = externalExtArrMakeUninit extArrKindFloat64 (length data1)
            in
            match rec11 st971 a701 0 data1 with (st972, #var"1913")
            in
            let #var"1711" = {} in
            let a631 = a701 in
            p_map
              st972
              (lam x1616.
                 match eqi (muli rows x1616) (externalExtArrLength a631) with true
                 then
                   { arr = a631, n = x1616, m = rows }
                 else
                   error "matFromArrExn: dimensions mismatch")
              cols11
  in
  let mtxGet =
    lam st968.
      lam row15.
        lam col4.
          lam mtx64.
            match mtx64 with {arr = #var"X83"}
            in
            match
              p_map
                st968
                (lam x1611.
                   lam x1612.
                     externalExtArrGet x1611 x1612)
                #var"X83"
            with
              (st969, x1613)
            in
            match mtx64 with {n = #var"X84"}
            in
            match
              p_map
                st969
                (lam x1614.
                   addi (muli (subi row15 1) x1614) (subi col4 1))
                #var"X84"
            with
              (st970, x1615)
            in
            p_apply st970 x1613 x1615
  in
  let mtxGet1 =
    lam st965.
      lam row14.
        lam col3.
          lam mtx63.
            match
              p_map
                st965
                (lam x1606.
                   lam x1607.
                     match x1606 with {arr = #var"X81"}
                     in
                     externalExtArrGet #var"X81" x1607)
                mtx63
            with
              (st966, x1608)
            in
            match
              p_map
                st966
                (lam x1609.
                   match x1609 with {n = #var"X82"}
                   in
                   addi (muli (subi row14 1) #var"X82") (subi col3 1))
                mtx63
            with
              (st967, x1610)
            in
            p_apply st967 x1608 x1610
  in
  let mtxGet2 =
    lam st959.
      lam row13.
        lam col2.
          lam mtx62.
            match
              p_map
                st959
                (lam x1595.
                   lam x1596.
                     match x1595 with {arr = #var"X80"}
                     in
                     externalExtArrGet #var"X80" x1596)
                mtx62
            with
              (st960, x1597)
            in
            match
              p_map st960 (lam x1598.
                   subi x1598 1) row13
            with
              (st961, x1599)
            in
            match
              p_map
                st961
                (lam x1600.
                   lam x1601.
                     addi (muli x1600 x1601) (subi col2 1))
                x1599
            with
              (st962, x1602)
            in
            match
              p_map st962 (lam x1603.
                   x1603.n) mtx62
            with
              (st963, x1604)
            in
            match p_apply st963 x1602 x1604 with (st964, x1605)
            in
            p_apply st964 x1597 x1605
  in
  let mtxGet3 =
    lam st952.
      lam row12.
        lam col1.
          lam mtx61.
            match mtx61 with {arr = #var"X78"}
            in
            match
              p_map
                st952
                (lam x1582.
                   lam x1583.
                     externalExtArrGet x1582 x1583)
                #var"X78"
            with
              (st953, x1584)
            in
            match
              p_map st953 (lam x1585.
                   subi x1585 1) row12
            with
              (st954, x1586)
            in
            match
              p_map
                st954
                (lam x1587.
                   lam x1588.
                     lam x1589.
                       addi (muli x1587 x1588) x1589)
                x1586
            with
              (st955, x1590)
            in
            match mtx61 with {n = #var"X79"}
            in
            match p_apply st955 x1590 #var"X79" with (st956, x1591)
            in
            match
              p_map st956 (lam x1592.
                   subi x1592 1) col1
            with
              (st957, x1593)
            in
            match p_apply st957 x1591 x1593 with (st958, x1594)
            in
            p_apply st958 x1584 x1594
  in
  let mtxGet4 =
    lam st944.
      lam row11.
        lam col.
          lam mtx6.
            match
              p_map
                st944
                (lam x1567.
                   lam x1568.
                     match x1567 with {arr = #var"X77"}
                     in
                     externalExtArrGet #var"X77" x1568)
                mtx6
            with
              (st945, x1569)
            in
            match
              p_map st945 (lam x1570.
                   subi x1570 1) row11
            with
              (st946, x1571)
            in
            match
              p_map
                st946
                (lam x1572.
                   lam x1573.
                     lam x1574.
                       addi (muli x1572 x1573) x1574)
                x1571
            with
              (st947, x1575)
            in
            match
              p_map st947 (lam x1576.
                   x1576.n) mtx6
            with
              (st948, x1577)
            in
            match p_apply st948 x1575 x1577 with (st949, x1578)
            in
            match
              p_map st949 (lam x1579.
                   subi x1579 1) col
            with
              (st950, x1580)
            in
            match p_apply st950 x1578 x1580 with (st951, x1581)
            in
            p_apply st951 x1569 x1581
  in
  let anon2 =
    lam new5.
      lam mtx55.
        lam row5.
          lam x1565.
            lam x1566.
              match new5 with {arr = #var"X75"}
              in
              match new5 with {n = #var"X76"}
              in
              externalExtArrSet
                #var"X75"
                (addi (muli 0 #var"X76") x1565)
                (matGetExn mtx55 (subi row5 1) (subi x1566 1))
  in
  let anon3 =
    lam st941.
      lam new4.
        lam mtx54.
          lam row4.
            lam x1558.
              lam x1559.
                match new4 with {arr = #var"X73"}
                in
                match
                  p_map
                    st941
                    (lam x1560.
                       lam x1561.
                         externalExtArrSet x1560 x1561 (matGetExn mtx54 (subi row4 1) (subi x1559 1)))
                    #var"X73"
                with
                  (st942, x1562)
                in
                match new4 with {n = #var"X74"}
                in
                match
                  p_map
                    st942
                    (lam x1563.
                       addi (muli 0 x1563) x1558)
                    #var"X74"
                with
                  (st943, x1564)
                in
                p_apply st943 x1562 x1564
  in
  let anon4 =
    lam st935.
      lam new3.
        lam mtx53.
          lam row3.
            lam x1545.
              lam x1546.
                match new3 with {arr = #var"X69"}
                in
                match
                  p_map
                    st935
                    (lam x1547.
                       lam x1548.
                         lam x1549.
                           externalExtArrSet x1547 x1548 x1549)
                    #var"X69"
                with
                  (st936, x1550)
                in
                match new3 with {n = #var"X70"}
                in
                match
                  p_map
                    st936
                    (lam x1551.
                       addi (muli 0 x1551) x1545)
                    #var"X70"
                with
                  (st937, x1552)
                in
                match p_apply st937 x1550 x1552 with (st938, x1553)
                in
                match
                  p_map st938 (lam x1554.
                       subi x1554 1) row3
                with
                  (st939, x1555)
                in
                match
                  p_map
                    st939
                    (lam x1556.
                       match mtx53 with {arr = #var"X71"}
                       in
                       match mtx53 with {n = #var"X72"}
                       in
                       externalExtArrGet #var"X71" (addi (muli x1556 #var"X72") (subi x1546 1)))
                    x1555
                with
                  (st940, x1557)
                in
                p_apply st940 x1553 x1557
  in
  recursive
    let rec13 =
      lam c4.
        lam c5.
          lam c6.
            lam i3.
              lam s13.
                match s13 with [ _,
                    _ ] ++ _
                then
                  match splitAt s13 1 with {#label"1" = x27}
                  in
                  cons
                    (anon2 c4 c5 c6 i3 (get s13 0))
                    (rec13 c4 c5 c6 (addi i3 1) x27)
                else match s13 with [ e5 ]
                then
                  match splitAt s13 1 with {#label"1" = x28}
                  in
                  let slice4 = x28 in
                  [ anon2 c4 c5 c6 i3 e5 ]
                else match s13 with ""
                in
                ""
    let rec14 =
      lam st18.
        lam c7.
          lam c8.
            lam c9.
              lam i4.
                lam s14.
                  match s14 with [ _,
                      _ ] ++ _
                  then
                    match anon3 st18 c7 c8 c9 i4 (get s14 0) with (st19, x29)
                    in
                    match splitAt s14 1 with {#label"1" = x30}
                    in
                    match rec14 st19 c7 c8 c9 (addi i4 1) x30 with (st20, x31)
                    in
                    (st20, cons x29 x31)
                  else match s14 with [ e6 ]
                  then
                    match splitAt s14 1 with {#label"1" = x32}
                    in
                    let slice5 = x32 in
                    match anon3 st18 c7 c8 c9 i4 e6 with (st21, x33)
                    in
                    (st21, [ x33 ])
                  else match s14 with ""
                  in
                  (st18, "")
    let rec15 =
      lam st22.
        lam c10.
          lam c11.
            lam c12.
              lam i5.
                lam s15.
                  match s15 with [ _,
                      _ ] ++ _
                  then
                    match anon4 st22 c10 c11 c12 i5 (get s15 0) with (st23, x34)
                    in
                    match splitAt s15 1 with {#label"1" = x35}
                    in
                    match rec15 st23 c10 c11 c12 (addi i5 1) x35 with (st24, x36)
                    in
                    (st24, cons x34 x36)
                  else match s15 with [ e7 ]
                  then
                    match splitAt s15 1 with {#label"1" = x37}
                    in
                    let slice6 = x37 in
                    match anon4 st22 c10 c11 c12 i5 e7 with (st25, x38)
                    in
                    (st25, [ x38 ])
                  else match s15 with ""
                  in
                  (st22, "")
  in
  let mtxRowCols =
    lam mtx52.
      lam row2.
        lam cols2.
          let n51 = length cols2 in
          match mtx52 with {arr = #var"X68"}
          in
          let new2 =
            { arr =
                externalExtArrMakeUninit (externalExtArrKind #var"X68") (muli 1 n51),
              n = n51,
              m = 1 }
          in
          let #var"1912" = rec13 new2 mtx52 row2 0 cols2 in
          let #var"92" = {} in
          new2
  in
  let mtxRowCols1 =
    lam st925.
      lam mtx51.
        lam row1.
          lam cols1.
            match mtx51 with {arr = #var"X67"}
            in
            match p_map st925 length cols1 with (st926, x1536)
            in
            match
              matMakeUninit st926 (externalExtArrKind #var"X67") 1 x1536
            with
              (st927, new1)
            in
            match
              p_bind
                st927
                hrmStoreSubmodel
                (hrmInit {})
                (lam st928.
                   lam x1537.
                     match
                       match x1537 with [ _,
                           _ ] ++ _
                       then
                         match anon3 st928 new1 mtx51 row1 0 (get x1537 0) with (st929, x1538)
                         in
                         match splitAt x1537 1 with {#label"1" = x1539}
                         in
                         match rec14 st929 new1 mtx51 row1 (addi 0 1) x1539 with (st930, x1540)
                         in
                         (st930, cons x1538 x1540)
                       else match x1537 with [ e20 ]
                       then
                         match splitAt x1537 1 with {#label"1" = x1541}
                         in
                         let slice19 = x1541 in
                         match anon3 st928 new1 mtx51 row1 0 e20 with (st931, x1542)
                         in
                         (st931, [ x1542 ])
                       else match x1537 with ""
                       in
                       (st928, "")
                     with
                       (st932, x1543)
                     in
                     p_traverseSeq
                       st932
                       (lam st933.
                          lam x1544.
                            (st933, x1544))
                       x1543)
                cols1
            with
              (st934, #var"1911")
            in
            let #var"91" = {} in
            (st934, new1)
  in
  let mtxRowCols2 =
    lam st915.
      lam mtx5.
        lam row.
          lam cols.
            match mtx5 with {arr = #var"X66"}
            in
            match p_map st915 length cols with (st916, x1525)
            in
            match
              matMakeUninit st916 (externalExtArrKind #var"X66") 1 x1525
            with
              (st917, new)
            in
            match
              p_bind
                st917
                hrmStoreSubmodel
                (hrmInit {})
                (lam st918.
                   lam x1526.
                     match
                       match x1526 with [ _,
                           _ ] ++ _
                       then
                         match anon4 st918 new mtx5 row 0 (get x1526 0) with (st919, x1527)
                         in
                         match splitAt x1526 1 with {#label"1" = x1528}
                         in
                         match rec15 st919 new mtx5 row (addi 0 1) x1528 with (st920, x1529)
                         in
                         (st920, cons x1527 x1529)
                       else match x1526 with [ e19 ]
                       then
                         match splitAt x1526 1 with {#label"1" = x1530}
                         in
                         let slice18 = x1530 in
                         match anon4 st918 new mtx5 row 0 e19 with (st921, x1533)
                         in
                         (st921, [ x1533 ])
                       else match x1526 with ""
                       in
                       (st918, "")
                     with
                       (st922, x1534)
                     in
                     p_traverseSeq
                       st922
                       (lam st923.
                          lam x1535.
                            (st923, x1535))
                       x1534)
                cols
            with
              (st924, #var"1910")
            in
            let #var"9" = {} in
            (st924, new)
  in
  let mtxSclrMul =
    lam st905.
      lam scalar.
        lam mtx41.
          match mtx41 with {m = #var"X60"}
          in
          let m21 = #var"X60" in
          match mtx41 with {n = #var"X61"}
          in
          let n31 = #var"X61" in
          match mtx41 with {arr = #var"X62"}
          in
          match
            p_map
              st905
              (lam x1510.
                 externalExtArrKind x1510)
              #var"X62"
          with
            (st906, x1511)
          in
          match matMakeUninit1 st906 x1511 m21 n31 with (st907, b141)
          in
          match
            p_map
              st907
              (lam x1512.
                 lam x1513.
                   muli x1512 x1513)
              m21
          with
            (st908, x1514)
          in
          match p_apply st908 x1514 n31 with (st909, mn1)
          in
          match
            p_map
              st909
              (lam x1515.
                 lam x1516.
                   lam x1517.
                     externalCblasCopy x1515 x1516 1 x1517 1)
              mn1
          with
            (st910, x1518)
          in
          match mtx41 with {arr = #var"X63"}
          in
          match p_apply st910 x1518 #var"X63" with (st911, x1519)
          in
          match b141 with {arr = #var"X64"}
          in
          match p_apply st911 x1519 #var"X64" with (st912, #var"1164")
          in
          match
            p_map
              st912
              (lam x1520.
                 lam x1523.
                   externalCblasScal x1520 scalar x1523 1)
              mn1
          with
            (st913, x1524)
          in
          match b141 with {arr = #var"X65"}
          in
          match p_apply st913 x1524 #var"X65" with (st914, #var"1211")
          in
          (st914, b141)
  in
  let mtxTrans =
    lam st887.
      lam mtx3.
        match
          p_map
            st887
            (lam x1483.
               match x1483 with {arr = #var"X53"}
               in
               externalExtArrKind #var"X53")
            mtx3
        with
          (st888, x1484)
        in
        match
          p_map st888 (lam x1485.
               x1485.n) mtx3
        with
          (st889, x1486)
        in
        match
          p_map st889 (lam x1487.
               x1487.m) mtx3
        with
          (st890, x1488)
        in
        match matMakeUninit1 st890 x1484 x1486 x1488 with (st891, b17)
        in
        match
          p_map
            st891
            (lam x1489.
               lam x1490.
                 match x1489 with {m = #var"X54"}
                 in
                 eqi #var"X54" x1490)
            mtx3
        with
          (st892, x1491)
        in
        match b17 with {n = #var"X55"}
        in
        match p_apply st892 x1491 #var"X55" with (st893, x1492)
        in
        match
          p_map
            st893
            (lam x1493.
               lam x1494.
                 match x1493 with {n = #var"X56"}
                 in
                 eqi #var"X56" x1494)
            mtx3
        with
          (st894, x1495)
        in
        match b17 with {m = #var"X57"}
        in
        match p_apply st894 x1495 #var"X57" with (st895, x1496)
        in
        match and st895 x1492 x1496 with (st896, x1497)
        in
        match
          p_subMap
            st896
            hrmStoreSubmodel
            (hrmInit {})
            (lam x1498.
               lam st897.
                 match x1498 with true
                 then
                   match
                     p_map
                       st897
                       (lam x1499.
                          lam x1500.
                            lam x1501.
                              lam x1502.
                                match x1499 with {m = #var"X58"}
                                in
                                externalMatTranspose #var"X58" x1500 x1501 x1502)
                       mtx3
                   with
                     (st898, x1503)
                   in
                   match
                     p_map st898 (lam x1504.
                          x1504.n) mtx3
                   with
                     (st899, x1505)
                   in
                   match p_apply st899 x1503 x1505 with (st900, x1506)
                   in
                   match
                     p_map st900 (lam x1507.
                          x1507.arr) mtx3
                   with
                     (st901, x1508)
                   in
                   match p_apply st901 x1506 x1508 with (st902, x1509)
                   in
                   match b17 with {arr = #var"X59"}
                   in
                   match p_apply st902 x1509 #var"X59" with (st903, #var"1610")
                   in
                   (st903, Right
                     {})
                 else
                   (st897, Left
                     (DimensionMismatch
                        {})))
            x1497
        with
          (st904, #var"1410")
        in
        (st904, b17)
  in
  let mtxExp =
    lam st876.
      lam mtx2.
        match mtx2 with {m = #var"X48"}
        in
        match
          p_map
            st876
            (lam x1460.
               lam x1461.
                 lam st877.
                   match
                     match eqi x1460 x1461 with true
                     then
                       match mtx2 with {m = #var"X49"}
                       in
                       match
                         p_map
                           st877
                           (lam x1462.
                              lam x1463.
                                lam x1464.
                                  externalMatExp x1462 x1463 x1464)
                           #var"X49"
                       with
                         (st878, x1465)
                       in
                       match mtx2 with {n = #var"X50"}
                       in
                       match p_apply st878 x1465 #var"X50" with (st879, x1466)
                       in
                       match mtx2 with {arr = #var"X51"}
                       in
                       match p_apply st879 x1466 #var"X51" with (st880, x1467)
                       in
                       (st880, Right
                         { mtx2 with arr = x1467 })
                     else
                       (st877, Left
                         (NotSquare
                            {}))
                   with
                     (st881, n6)
                   in
                   match n6 with Right x1468
                   then
                     match x1468 with {arr = x1469}
                     in
                     match
                       p_map
                         st881
                         (lam x1470.
                            lam x1471.
                              lam x1472.
                                Right
                                  { arr = x1470, n = x1471, m = x1472 })
                         x1469
                     with
                       (st882, x1473)
                     in
                     match x1468 with {n = x1474}
                     in
                     match p_apply st882 x1473 x1474 with (st883, x1475)
                     in
                     match x1468 with {m = x1476}
                     in
                     p_apply st883 x1475 x1476
                   else match n6 with Left x1477
                   in
                   (st881, p_pure (Left
                        x1477)))
            #var"X48"
        with
          (st884, x1478)
        in
        match mtx2 with {n = #var"X52"}
        in
        match
          p_subApply st884 hrmStoreSubmodel (hrmInit {}) x1478 #var"X52"
        with
          (st885, x1479)
        in
        match p_join st885 x1479 with (st886, x1480)
        in
        p_map
          st886
          (lam x1482.
             match x1482 with Left carried72
             then
               match carried72 with NotSquare carried73
               in
               error "Not square"
             else match x1482 with Right carried74
             in
             carried74)
          x1480
  in
  let eitherEither =
    lam st875.
      lam e22.
        p_map
          st875
          (lam x1459.
             match x1459 with Left carried70
             then
               error (matErrorToString carried70)
             else match x1459 with Right carried71
             in
             carried71)
          e22
  in
  let mtxMul =
    lam st855.
      lam a371.
        lam b51.
          match
            p_map st855 (lam x1408.
                 x1408.m) a371
          with
            (st856, m11)
          in
          match b51 with {n = #var"X43"}
          in
          let n21 = #var"X43" in
          match
            p_map st856 (lam x1409.
                 x1409.n) a371
          with
            (st857, x1410)
          in
          match
            p_map
              st857
              (lam x1415.
                 lam x1416.
                   lam st858.
                     match
                       match eqi x1415 x1416 with true
                       then
                         match b51 with {arr = #var"X44"}
                         in
                         match
                           p_map
                             st858
                             (lam x1417.
                                externalExtArrKind x1417)
                             #var"X44"
                         with
                           (st859, x1418)
                         in
                         match matMakeUninit1 st859 x1418 m11 n21 with (st860, c211)
                         in
                         match
                           p_map
                             st860
                             (lam x1419.
                                lam x1420.
                                  lam x1425.
                                    lam x1426.
                                      lam x1427.
                                        lam x1428.
                                          lam x1429.
                                            externalCblasGemm
                                              cblasRowMajor
                                              cblasNoTrans
                                              cblasNoTrans
                                              x1419
                                              x1420
                                              x1415
                                              1.
                                              x1425
                                              x1415
                                              x1426
                                              x1427
                                              0.
                                              x1428
                                              x1429)
                             m11
                         with
                           (st861, x1430)
                         in
                         match p_apply st861 x1430 n21 with (st862, x1435)
                         in
                         match
                           p_map
                             st862
                             (lam x1436.
                                x1436.arr)
                             a371
                         with
                           (st863, x1437)
                         in
                         match p_apply st863 x1435 x1437 with (st864, x1438)
                         in
                         match b51 with {arr = #var"X45"}
                         in
                         match p_apply st864 x1438 #var"X45" with (st865, x1439)
                         in
                         match p_apply st865 x1439 n21 with (st866, x1440)
                         in
                         match c211 with {arr = #var"X46"}
                         in
                         match p_apply st866 x1440 #var"X46" with (st867, x1445)
                         in
                         match p_apply st867 x1445 n21 with (st868, #var"101")
                         in
                         (st868, Right
                           c211)
                       else
                         (st858, Left
                           (DimensionMismatch
                              {}))
                     with
                       (st869, n5)
                     in
                     match n5 with Right x1446
                     then
                       match x1446 with {arr = x1447}
                       in
                       match
                         p_map
                           st869
                           (lam x1448.
                              lam x1449.
                                lam x1450.
                                  Right
                                    { arr = x1448, n = x1449, m = x1450 })
                           x1447
                       with
                         (st870, x1451)
                       in
                       match x1446 with {n = x1452}
                       in
                       match p_apply st870 x1451 x1452 with (st871, x1453)
                       in
                       match x1446 with {m = x1454}
                       in
                       p_apply st871 x1453 x1454
                     else match n5 with Left x1455
                     in
                     (st869, p_pure (Left
                          x1455)))
              x1410
          with
            (st872, x1456)
          in
          match b51 with {m = #var"X47"}
          in
          match
            p_subApply st872 hrmStoreSubmodel (hrmInit {}) x1456 #var"X47"
          with
            (st873, x1457)
          in
          match p_join st873 x1457 with (st874, x1458)
          in
          eitherEither st874 x1458
  in
  let mtxMul1 =
    lam st832.
      lam a37.
        lam b5.
          match
            p_map st832 (lam x1348.
                 x1348.m) a37
          with
            (st833, m1)
          in
          match
            p_map st833 (lam x1349.
                 x1349.n) b5
          with
            (st834, n2)
          in
          match
            p_map st834 (lam x1350.
                 x1350.n) a37
          with
            (st835, x1355)
          in
          match
            p_map
              st835
              (lam x1356.
                 lam x1357.
                   lam st836.
                     match
                       match eqi x1356 x1357 with true
                       then
                         match
                           p_map
                             st836
                             (lam x1358.
                                match x1358 with {arr = #var"X41"}
                                in
                                externalExtArrKind #var"X41")
                             b5
                         with
                           (st837, x1359)
                         in
                         match matMakeUninit1 st837 x1359 m1 n2 with (st838, c210)
                         in
                         match
                           p_map
                             st838
                             (lam x1360.
                                lam x1361.
                                  lam x1362.
                                    lam x1363.
                                      lam x1364.
                                        lam x1365.
                                          lam x1366.
                                            externalCblasGemm
                                              cblasRowMajor
                                              cblasNoTrans
                                              cblasNoTrans
                                              x1360
                                              x1361
                                              x1356
                                              1.
                                              x1362
                                              x1356
                                              x1363
                                              x1364
                                              0.
                                              x1365
                                              x1366)
                             m1
                         with
                           (st839, x1367)
                         in
                         match p_apply st839 x1367 n2 with (st840, x1368)
                         in
                         match
                           p_map
                             st840
                             (lam x1369.
                                x1369.arr)
                             a37
                         with
                           (st841, x1370)
                         in
                         match p_apply st841 x1368 x1370 with (st842, x1375)
                         in
                         match
                           p_map
                             st842
                             (lam x1376.
                                x1376.arr)
                             b5
                         with
                           (st843, x1377)
                         in
                         match p_apply st843 x1375 x1377 with (st844, x1378)
                         in
                         match p_apply st844 x1378 n2 with (st845, x1379)
                         in
                         match c210 with {arr = #var"X42"}
                         in
                         match p_apply st845 x1379 #var"X42" with (st846, x1380)
                         in
                         match p_apply st846 x1380 n2 with (st847, #var"10")
                         in
                         (st847, Right
                           c210)
                       else
                         (st836, Left
                           (DimensionMismatch
                              {}))
                     with
                       (st848, n4)
                     in
                     match n4 with Right x1385
                     then
                       match x1385 with {arr = x1386}
                       in
                       match
                         p_map
                           st848
                           (lam x1387.
                              lam x1388.
                                lam x1389.
                                  Right
                                    { arr = x1387, n = x1388, m = x1389 })
                           x1386
                       with
                         (st849, x1390)
                       in
                       match x1385 with {n = x1395}
                       in
                       match p_apply st849 x1390 x1395 with (st850, x1396)
                       in
                       match x1385 with {m = x1397}
                       in
                       p_apply st850 x1396 x1397
                     else match n4 with Left x1398
                     in
                     (st848, p_pure (Left
                          x1398)))
              x1355
          with
            (st851, x1399)
          in
          match
            p_map st851 (lam x1400.
                 x1400.m) b5
          with
            (st852, x1405)
          in
          match
            p_subApply st852 hrmStoreSubmodel (hrmInit {}) x1399 x1405
          with
            (st853, x1406)
          in
          match p_join st853 x1406 with (st854, x1407)
          in
          eitherEither st854 x1407
  in
  let eitherEither1 =
    lam st831.
      lam e21.
        p_map
          st831
          (lam x1347.
             match x1347 with Left carried68
             then
               error (matErrorToString carried68)
             else match x1347 with Right carried69
             in
             carried69)
          e21
  in
  let mtxElemMul =
    lam st803.
      lam a361.
        lam b41.
          match matHasSameShape21 st803 a361 b41 with (st804, x1285)
          in
          match
            p_bind
              st804
              hrmStoreSubmodel
              (hrmInit {})
              (lam st805.
                 lam x1286.
                   match
                     match x1286 with true
                     then
                       match
                         p_map
                           st805
                           (lam x1287.
                              match x1287 with {arr = #var"X34"}
                              in
                              externalExtArrKind #var"X34")
                           a361
                       with
                         (st806, x1288)
                       in
                       match
                         p_map
                           st806 (lam x1289.
                              x1289.m) a361
                       with
                         (st807, x1290)
                       in
                       match
                         p_map
                           st807 (lam x1291.
                              x1291.n) a361
                       with
                         (st808, x1292)
                       in
                       match matMakeUninit1 st808 x1288 x1290 x1292 with (st809, c311)
                       in
                       match matHasSameShape21 st809 a361 b41 with (st810, x1293)
                       in
                       match
                         p_map
                           st810
                           (lam x1294.
                              lam x1295.
                                match x1294 with {m = #var"X35"}
                                in
                                eqi #var"X35" x1295)
                           b41
                       with
                         (st811, x1296)
                       in
                       match c311 with {m = #var"X36"}
                       in
                       match p_apply st811 x1296 #var"X36" with (st812, x1297)
                       in
                       match
                         p_map
                           st812
                           (lam x1298.
                              lam x1299.
                                match x1298 with {n = #var"X37"}
                                in
                                eqi #var"X37" x1299)
                           b41
                       with
                         (st813, x1300)
                       in
                       match c311 with {n = #var"X38"}
                       in
                       match p_apply st813 x1300 #var"X38" with (st814, x1305)
                       in
                       match and st814 x1297 x1305 with (st815, x1306)
                       in
                       match and st815 x1293 x1306 with (st816, x1307)
                       in
                       match
                         p_subMap
                           st816
                           hrmStoreSubmodel
                           (hrmInit {})
                           (lam x1308.
                              lam st817.
                                match x1308 with true
                                then
                                  match
                                    p_map
                                      st817
                                      (lam x1309.
                                         lam x1310.
                                           lam x1315.
                                             lam x1316.
                                               lam x1317.
                                                 match x1309 with {m = #var"X39"}
                                                 in
                                                 externalMatElemMul #var"X39" x1310 x1315 x1316 x1317)
                                      a361
                                  with
                                    (st818, x1318)
                                  in
                                  match
                                    p_map
                                      st818
                                      (lam x1319.
                                         x1319.n)
                                      a361
                                  with
                                    (st819, x1320)
                                  in
                                  match p_apply st819 x1318 x1320 with (st820, x1325)
                                  in
                                  match
                                    p_map
                                      st820
                                      (lam x1326.
                                         x1326.arr)
                                      a361
                                  with
                                    (st821, x1327)
                                  in
                                  match p_apply st821 x1325 x1327 with (st822, x1328)
                                  in
                                  match
                                    p_map
                                      st822
                                      (lam x1329.
                                         x1329.arr)
                                      b41
                                  with
                                    (st823, x1330)
                                  in
                                  match p_apply st823 x1328 x1330 with (st824, x1331)
                                  in
                                  match c311 with {arr = #var"X40"}
                                  in
                                  match p_apply st824 x1331 #var"X40" with (st825, #var"1511")
                                  in
                                  (st825, Right
                                    {})
                                else
                                  (st817, Left
                                    (DimensionMismatch
                                       {})))
                           x1307
                       with
                         (st826, #var"1311")
                       in
                       (st826, Right
                         c311)
                     else
                       (st805, Left
                         (DimensionMismatch
                            {}))
                   with
                     (st827, n1)
                   in
                   match n1 with Right x1332
                   then
                     match x1332 with {arr = x1333}
                     in
                     match
                       p_map
                         st827
                         (lam x1334.
                            lam x1335.
                              lam x1336.
                                Right
                                  { arr = x1334, n = x1335, m = x1336 })
                         x1333
                     with
                       (st828, x1337)
                     in
                     match x1332 with {n = x1338}
                     in
                     match p_apply st828 x1337 x1338 with (st829, x1339)
                     in
                     match x1332 with {m = x1340}
                     in
                     p_apply st829 x1339 x1340
                   else match n1 with Left x1345
                   in
                   (st827, p_pure (Left
                        x1345)))
              x1285
          with
            (st830, x1346)
          in
          eitherEither1 st830 x1346
  in
  recursive
    let work2 =
      lam bound.
        lam c13.
          lam i31.
            lam acc31.
              match lti i31 bound with true
              then
                match c13 with {arr = #var"X"}
                in
                work2
                  bound
                  c13
                  (addi i31 1)
                  (addf acc31 (externalExtArrGet #var"X" i31))
              else
                acc31
    let work21 =
      lam st26.
        lam bound1.
          lam c14.
            lam i32.
              lam acc32.
                match lti i32 bound1 with true
                then
                  match
                    p_map
                      st26
                      (lam x39.
                         lam x40.
                           addf x39 x40)
                      acc32
                  with
                    (st27, x41)
                  in
                  match c14 with {arr = #var"X1"}
                  in
                  match
                    p_map
                      st27
                      (lam x42.
                         externalExtArrGet x42 i32)
                      #var"X1"
                  with
                    (st28, x43)
                  in
                  match p_apply st28 x41 x43 with (st29, x44)
                  in
                  work21 st29 bound1 c14 (addi i32 1) x44
                else
                  (st26, acc32)
  in
  let mtxMean =
    lam mtx11.
      match mtx11 with {m = #var"X30"}
      in
      match mtx11 with {n = #var"X31"}
      in
      match mtx11 with {m = #var"X32"}
      in
      match mtx11 with {n = #var"X33"}
      in
      divf
        (work2 (muli #var"X30" #var"X31") mtx11 0 0.)
        (int2float (muli #var"X32" #var"X33"))
  in
  let mtxMean1 =
    lam st796.
      lam mtx1.
        match mtx1 with {n = #var"X25"}
        in
        match
          p_map
            st796
            (lam x1274.
               match mtx1 with {m = #var"X26"}
               in
               muli #var"X26" x1274)
            #var"X25"
        with
          (st797, x1275)
        in
        match
          p_bind
            st797
            hrmStoreSubmodel
            (hrmInit {})
            (lam st798.
               lam x1276.
                 match lti 0 x1276 with true
                 then
                   match mtx1 with {arr = #var"X27"}
                   in
                   match
                     p_map
                       st798
                       (lam x1277.
                          addf 0. (externalExtArrGet x1277 0))
                       #var"X27"
                   with
                     (st799, x1278)
                   in
                   work21 st799 x1276 mtx1 (addi 0 1) x1278
                 else
                   (st798, p_pure 0.))
            x1275
        with
          (st800, x1279)
        in
        match
          p_map
            st800
            (lam x1280.
               lam x1281.
                 divf x1280 x1281)
            x1279
        with
          (st801, x1282)
        in
        match mtx1 with {n = #var"X28"}
        in
        match
          p_map
            st801
            (lam x1283.
               match mtx1 with {m = #var"X29"}
               in
               int2float (muli #var"X29" x1283))
            #var"X28"
        with
          (st802, x1284)
        in
        p_apply st802 x1282 x1284
  in
  let anon5 =
    lam index1.
      lam x1273.
        match eqi (subi index1 1) x1273 with true
        then
          1.
        else
          0.
  in
  recursive
    let rec =
      lam c15.
        lam s.
          match s with [ _,
              _ ] ++ _
          then
            match splitAt s 1 with {#label"1" = x45}
            in
            cons (anon5 c15 (get s 0)) (rec c15 x45)
          else match s with [ e8 ]
          then
            match splitAt s 1 with {#label"1" = x46}
            in
            let slice7 = x46 in
            [ anon5 c15 e8 ]
          else match s with ""
          in
          ""
  in
  recursive
    let unfoldr =
      lam c16.
        lam b0.
          let fb =
            match leqi c16 b0 with true
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
            cons field (unfoldr c16 field1)
          else match fb with None carried1
          in
          ""
  in
  let kroneckerDelta =
    lam index.
      lam length2.
        rec index (unfoldr length2 0)
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
            p_map st30 (lam x47.
                 eqi x47 2) (head seq)
          with
            (st31, x48)
          in
          p_bind
            st31
            hrmStoreSubmodel
            (hrmInit {})
            (lam st32.
               lam x49.
                 match x49 with true
                 then
                   (st32, p_pure true)
                 else
                   any st32 (tail seq))
            x48
  in
  let any1 = lam st795.
      lam l21.
        any st795 l21 in
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
    lam st777.
      lam currRep81.
        lam event31.
          lam nhosts81.
            match
              p_map
                st777
                (lam x1251.
                   match x1251 with Event1 x1532
                   then
                     x1532.host
                   else
                     let #var"1162" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event31
            with
              (st778, hostIndex42)
            in
            match
              p_traverseSeq
                st778
                (lam st779.
                   lam x1252.
                     (st779, x1252))
                currRep81
            with
              (st780, x1253)
            in
            match
              p_map
                st780
                (lam x1254.
                   subsequence x1254 (subi 1 1))
                x1253
            with
              (st781, x1255)
            in
            match
              p_map
                st781
                (lam x1256.
                   subi x1256 1)
                hostIndex42
            with
              (st782, x1257)
            in
            match p_apply st782 x1255 x1257 with (st783, x1258)
            in
            match
              p_map
                st783
                (lam x1259.
                   match x1259 with Event1 x1522
                   then
                     x1522.toState
                   else
                     let #var"1163" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event31
            with
              (st784, x1260)
            in
            match
              p_traverseSeq
                st784
                (lam st785.
                   lam x1261.
                     (st785, x1261))
                [ x1260 ]
            with
              (st786, x1262)
            in
            match
              p_map
                st786
                (lam x1263.
                   addi x1263 1)
                hostIndex42
            with
              (st787, first1)
            in
            match
              p_traverseSeq
                st787
                (lam st788.
                   lam x1264.
                     (st788, x1264))
                currRep81
            with
              (st789, x1265)
            in
            match p_map st789 subsequence x1265 with (st790, x1266)
            in
            match
              p_map st790 (lam x1267.
                   subi x1267 1) first1
            with
              (st791, x1268)
            in
            match p_apply st791 x1266 x1268 with (st792, x1269)
            in
            match
              p_map
                st792
                (lam x1270.
                   subi (addi nhosts81 1) x1270)
                first1
            with
              (st793, x1271)
            in
            match p_apply st793 x1269 x1271 with (st794, x1272)
            in
            paste01
              st794
              [ x1258,
                x1262,
                x1272 ]
  in
  let updateRepertoire1 =
    lam st763.
      lam currRep8.
        lam event3.
          lam nhosts8.
            match
              p_map
                st763
                (lam x1233.
                   match x1233 with Event1 x1531
                   then
                     x1531.host
                   else
                     let #var"1160" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
                     in
                     exit 1)
                event3
            with
              (st764, hostIndex41)
            in
            match
              p_map
                st764
                (lam x1234.
                   subsequence x1234 (subi 1 1))
                currRep8
            with
              (st765, x1235)
            in
            match
              p_map
                st765
                (lam x1236.
                   subi x1236 1)
                hostIndex41
            with
              (st766, x1237)
            in
            match p_apply st766 x1235 x1237 with (st767, x1238)
            in
            match
              p_map
                st767
                (lam x1239.
                   match x1239 with Event1 x1521
                   then
                     x1521.toState
                   else
                     let #var"1161" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                     in
                     exit 1)
                event3
            with
              (st768, x1240)
            in
            match
              p_traverseSeq
                st768
                (lam st769.
                   lam x1241.
                     (st769, x1241))
                [ x1240 ]
            with
              (st770, x1242)
            in
            match
              p_map
                st770
                (lam x1243.
                   addi x1243 1)
                hostIndex41
            with
              (st771, first)
            in
            match p_map st771 subsequence currRep8 with (st772, x1244)
            in
            match
              p_map st772 (lam x1245.
                   subi x1245 1) first
            with
              (st773, x1246)
            in
            match p_apply st773 x1244 x1246 with (st774, x1247)
            in
            match
              p_map
                st774
                (lam x1248.
                   subi (addi nhosts8 1) x1248)
                first
            with
              (st775, x1249)
            in
            match p_apply st775 x1247 x1249 with (st776, x1250)
            in
            paste01
              st776
              [ x1238,
                x1242,
                x1250 ]
  in
  recursive
    let observationMessage =
      lam obsRepertoire.
        lam i41.
          lam max.
            match leqi i41 max with true
            then
              let interaction = get obsRepertoire (subi i41 1) in
              let stateMsg =
                match
                  match geqi interaction 0 with true
                  then
                    leqi interaction 2
                  else
                    false
                with
                  true
                then
                  kroneckerDelta (addi interaction 1) 3
                else
                  rep 3 1.
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
      lam st33.
        lam obsRepertoire1.
          lam i42.
            lam max1.
              match leqi i42 max1 with true
              then
                match
                  p_map
                    st33
                    (lam x50.
                       match
                         match geqi x50 0 with true
                         then
                           leqi x50 2
                         else
                           false
                       with
                         true
                       then
                         kroneckerDelta (addi x50 1) 3
                       else
                         rep 3 1.)
                    (get obsRepertoire1 (subi i42 1))
                with
                  (st34, stateMsg1)
                in
                match
                  p_map
                    st34
                    (lam x51.
                       get x51 (subi 1 1))
                    stateMsg1
                with
                  (st35, x52)
                in
                match
                  p_map
                    st35
                    (lam x53.
                       get x53 (subi 2 1))
                    stateMsg1
                with
                  (st36, x54)
                in
                match
                  p_map
                    st36
                    (lam x55.
                       get x55 (subi 3 1))
                    stateMsg1
                with
                  (st37, x56)
                in
                match
                  observationMessage1 st37 obsRepertoire1 (addi i42 1) max1
                with
                  (st38, x57)
                in
                (st38, cons12 x52 (cons12 x54 (cons12 x56 x57)))
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
                    st39
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
                  (st40, left)
                in
                match
                  postorderTraverse
                    st40
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
                  (st42, x58)
                in
                match mtxExp st42 x58 with (st43, leftKernel)
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
                  (st44, x59)
                in
                match mtxExp st44 x59 with (st45, rightKernel)
                in
                match mtxTrans st45 leftKernel with (st46, x60)
                in
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
                       let #var"19" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:25-30:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n"
                       in
                       p_pure (exit 1))
                    x60
                with
                  (st47, leftInMsg)
                in
                match mtxTrans st47 rightKernel with (st48, x61)
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
                       let #var"110" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 31:26-31:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n"
                       in
                       p_pure (exit 1))
                    x61
                with
                  (st49, rightInMsg)
                in
                match mtxElemMul st49 leftInMsg rightInMsg with (st50, x62)
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
                    outMsg = x62,
                    leftInMsg = leftInMsg,
                    rightInMsg = rightInMsg })
  in
  let mtx3ToSeq =
    lam st750.
      lam mtx.
        lam i114.
          match mtxGet1 st750 i114 1 mtx with (st751, p111)
          in
          match mtxGet1 st751 i114 2 mtx with (st752, p210)
          in
          match mtxGet1 st752 i114 3 mtx with (st753, p310)
          in
          match
            p_map
              st753
              (lam x1216.
                 lam x1217.
                   lam x1218.
                     addf (addf x1216 x1217) x1218)
              p111
          with
            (st754, x1219)
          in
          match p_apply st754 x1219 p210 with (st755, x1220)
          in
          match p_apply st755 x1220 p310 with (st756, s51)
          in
          match
            p_map
              st756
              (lam x1221.
                 lam x1222.
                   divf x1221 x1222)
              p111
          with
            (st757, x1223)
          in
          match p_apply st757 x1223 s51 with (st758, x1224)
          in
          match
            p_map
              st758
              (lam x1225.
                 lam x1226.
                   divf x1225 x1226)
              p210
          with
            (st759, x1227)
          in
          match p_apply st759 x1227 s51 with (st760, x1228)
          in
          match
            p_map
              st760
              (lam x1229.
                 lam x1230.
                   divf x1229 x1230)
              p310
          with
            (st761, x1231)
          in
          match p_apply st761 x1231 s51 with (st762, x1232)
          in
          (st762, [ x1224,
            x1228,
            x1232 ])
  in
  recursive
    let rec24 =
      lam st51.
        lam c17.
          lam c18.
            lam acc4.
              lam s24.
                match s24 with [ _ ] ++ _
                then
                  let x63 = get s24 0 in
                  match
                    p_map
                      st51
                      (lam x64.
                         lam x65.
                           addf x64 x65)
                      acc4
                  with
                    (st52, x66)
                  in
                  match mtx3ToSeq st52 c18 x63 with (st53, params)
                  in
                  match
                    p_bind
                      st53
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st54.
                         lam x67.
                           match
                             match geqi x67 0 with true
                             then
                               lti x67 (length12 params)
                             else
                               false
                           with
                             true
                           then
                             log11 st54 (get params (subi (addi x67 1) 1))
                           else
                             (st54, p_pure (log1 0.)))
                      (get c17 (subi x63 1))
                  with
                    (st55, x68)
                  in
                  match p_apply st55 x66 x68 with (st56, x69)
                  in
                  match splitAt s24 1 with {#label"1" = x70}
                  in
                  rec24 st56 c17 c18 x69 x70
                else match s24 with ""
                in
                (st51, acc4)
  in
  let anon6 = lam x1215.
      addi x1215 1 in
  recursive
    let rec31 =
      lam i12.
        lam acc12.
          match geqi i12 0 with true
          then
            rec31 (subi i12 1) (cons (anon6 i12) acc12)
          else
            acc12
  in
  let getRepertoireSamplingDensity =
    lam st745.
      lam x1481.
        lam samplingProb1.
          lam nhosts7.
            let i113 = subi (addi (subi nhosts7 1) 1) 1 in
            let s226 =
              match geqi i113 0 with true
              then
                rec31 (subi i113 1) (cons (anon6 i113) "")
              else
                ""
            in
            match s226 with [ _ ] ++ _
            then
              let x1209 = get s226 0 in
              match mtx3ToSeq st745 samplingProb1 x1209 with (st746, params1)
              in
              match
                p_bind
                  st746
                  hrmStoreSubmodel
                  (hrmInit {})
                  (lam st747.
                     lam x1210.
                       match
                         match geqi x1210 0 with true
                         then
                           lti x1210 (length12 params1)
                         else
                           false
                       with
                         true
                       then
                         log11 st747 (get params1 (subi (addi x1210 1) 1))
                       else
                         (st747, p_pure (log1 0.)))
                  (get x1481 (subi x1209 1))
              with
                (st748, x1211)
              in
              match
                p_map st748 (lam x1212.
                     addf 0. x1212) x1211
              with
                (st749, x1213)
              in
              match splitAt s226 1 with {#label"1" = x1214}
              in
              rec24 st749 x1481 samplingProb1 x1213 x1214
            else match s226 with ""
            in
            (st745, p_pure 0.)
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
                     lam x71.
                       match eqi x71 2 with true
                       then
                         p_map
                           st58 (lam x72.
                              addi x72 1) acc5
                       else
                         (st58, acc5))
                  (get s25 0)
              with
                (st59, x73)
              in
              match splitAt s25 1 with {#label"1" = x74}
              in
              rec25 st59 x73 x74
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
                  (lam x75.
                     match eqi x75 2 with true
                     then
                       addi init1 1
                     else
                       init1)
                  (get seq5 0)
              with
                (st61, x76)
              in
              match splitAt seq5 1 with {#label"1" = x77}
              in
              rec25 st61 x76 x77
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
                        [ slice3 currRep 1 hostIndex4,
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
                          slice3 currRep (addi hostIndex4 1) (addi nhosts2 1) ]
                      in
                      let currRep1 =
                        match s26 with [ _ ] ++ _
                        then
                          match splitAt s26 1 with {#label"1" = x83}
                          in
                          rec21 (concat "" (get s26 0)) x83
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
                          (lam x78.
                             get x78 (subi eventIndex1 1))
                          eventSeq
                      with
                        (st63, x79)
                      in
                      p_bind
                        st63
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st64.
                           lam x80.
                             match
                               eqi
                                 (match x80 with Event1 x301
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
                               match fold st64 0 currRep1 with (st65, x81)
                               in
                               p_bind
                                 st65
                                 hrmStoreSubmodel
                                 (hrmInit {})
                                 (lam st66.
                                    lam x82.
                                      match eqi x82 1 with true
                                      then
                                        (st66, p_pure false)
                                      else
                                        ifCont3 st66 currRep1 eventSeq eventIndex1 nEvents nhosts2 x80 0)
                                 x81
                             else
                               ifCont3 st64 currRep1 eventSeq eventIndex1 nEvents nhosts2 x80 0)
                        x79
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
                       lam x84.
                         match gti eventIndex11 x84 with true
                         then
                           (st68, p_pure true)
                         else match
                           p_map
                             st68
                             (lam x85.
                                get x85 (subi eventIndex11 1))
                             eventSeq1
                         with
                           (st69, x86)
                         in
                         p_bind
                           st69
                           hrmStoreSubmodel
                           (hrmInit {})
                           (lam st70.
                              lam x87.
                                match
                                  eqi
                                    (match x87 with Event1 x302
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
                                  match fold st70 0 currRep11 with (st71, x88)
                                  in
                                  p_bind
                                    st71
                                    hrmStoreSubmodel
                                    (hrmInit {})
                                    (lam st72.
                                       lam x89.
                                         match eqi x89 1 with true
                                         then
                                           (st72, p_pure false)
                                         else
                                           ifCont3 st72 currRep11 eventSeq1 eventIndex11 x84 nhosts3 x87 0)
                                    x88
                                else
                                  ifCont3 st70 currRep11 eventSeq1 eventIndex11 x84 nhosts3 x87 0)
                           x86)
                    nEvents1
  in
  let anon7 =
    lam x1208.
      match eqi x1208 2 with true
      then
        true
      else
        eqi x1208 1
  in
  let anon8 =
    lam st744.
      lam x1206.
        p_map
          st744
          (lam x1207.
             match eqi x1207 2 with true
             then
               true
             else
               eqi x1207 1)
          x1206
  in
  recursive
    let rec4 =
      lam s4.
        match s4 with [ _,
            _ ] ++ _
        then
          match splitAt s4 1 with {#label"1" = x90}
          in
          cons (anon7 (get s4 0)) (rec4 x90)
        else match s4 with [ e9 ]
        then
          match splitAt s4 1 with {#label"1" = x91}
          in
          let slice8 = x91 in
          [ anon7 e9 ]
        else match s4 with ""
        in
        ""
    let rec5 =
      lam st73.
        lam s5.
          match s5 with [ _,
              _ ] ++ _
          then
            match anon8 st73 (get s5 0) with (st74, x92)
            in
            match splitAt s5 1 with {#label"1" = x93}
            in
            match rec5 st74 x93 with (st75, x94)
            in
            (st75, cons x92 x94)
          else match s5 with [ e10 ]
          then
            match splitAt s5 1 with {#label"1" = x95}
            in
            let slice9 = x95 in
            match anon8 st73 e10 with (st76, x96)
            in
            (st76, [ x96 ])
          else match s5 with ""
          in
          (st73, "")
  in
  let sapply = lam st743.
      lam s72.
        rec5 st743 s72
  in
  let anon9 = lam x1205.
      eqi x1205 2 in
  let anon10 =
    lam st742.
      lam x1203.
        p_map st742 (lam x1204.
             eqi x1204 2) x1203
  in
  recursive
    let rec6 =
      lam s6.
        match s6 with [ _,
            _ ] ++ _
        then
          match splitAt s6 1 with {#label"1" = x97}
          in
          cons (anon9 (get s6 0)) (rec6 x97)
        else match s6 with [ e11 ]
        then
          match splitAt s6 1 with {#label"1" = x98}
          in
          let slice10 = x98 in
          [ anon9 e11 ]
        else match s6 with ""
        in
        ""
    let rec7 =
      lam st77.
        lam s7.
          match s7 with [ _,
              _ ] ++ _
          then
            match anon10 st77 (get s7 0) with (st78, x99)
            in
            match splitAt s7 1 with {#label"1" = x100}
            in
            match rec7 st78 x100 with (st79, x101)
            in
            (st79, cons x99 x101)
          else match s7 with [ e12 ]
          then
            match splitAt s7 1 with {#label"1" = x102}
            in
            let slice11 = x102 in
            match anon10 st77 e12 with (st80, x103)
            in
            (st80, [ x103 ])
          else match s7 with ""
          in
          (st77, "")
  in
  let sapply1 = lam st741.
      lam s71.
        rec7 st741 s71
  in
  let getGainRate =
    lam st733.
      lam repertoire14.
        lam hostIndex33.
          lam modelParams123.
            let fromState53 = get repertoire14 (subi hostIndex33 1) in
            match
              mtxGet
                st733
                (addi fromState53 1)
                (addi (addi fromState53 1) 1)
                (match
                   match modelParams123 with ModelParams1 x1444
                   then
                     x1444.embeddedQMatrix
                   else
                     let #var"1152" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1434
                 then
                   x1434.mat
                 else
                   let #var"1153" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   let x1183 = exit 1 in
                   match x1183 with {arr = x1184}
                   in
                   match x1183 with {n = x1185}
                   in
                   match x1183 with {m = x1186}
                   in
                   { arr = p_pure x1184, n = p_pure x1185, m = p_pure x1186 })
            with
              (st734, baseRate13)
            in
            match eqi fromState53 0 with true
            then
              match
                p_map
                  st734
                  (lam x1187.
                     lam x1188.
                       mulf x1187 x1188)
                  baseRate13
              with
                (st735, x1189)
              in
              match
                p_map
                  st735
                  (lam x1190.
                     negf x1190)
                  (match modelParams123 with ModelParams1 x1384
                   then
                     x1384.beta
                   else
                     let #var"1154" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                     in
                     p_pure (exit 1))
              with
                (st736, x1195)
              in
              match
                pow1
                  st736
                  (divf
                     (mtxMean
                        (mtxRowCols
                           (match modelParams123 with ModelParams1 x1394
                            then
                              x1394.hostMetric
                            else
                              let #var"1155" =
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
                        let #var"1156" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                        in
                        exit 1))
                  x1195
              with
                (st737, x1196)
              in
              p_apply st737 x1189 x1196
            else match
              p_map
                st734
                (lam x1197.
                   lam x1198.
                     mulf x1197 x1198)
                baseRate13
            with
              (st738, x1199)
            in
            match
              p_map
                st738
                (lam x1200.
                   negf x1200)
                (match modelParams123 with ModelParams1 x1414
                 then
                   x1414.beta
                 else
                   let #var"1157" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                   in
                   p_pure (exit 1))
            with
              (st739, x1201)
            in
            match
              pow1
                st739
                (divf
                   (mtxMean
                      (mtxRowCols
                         (match modelParams123 with ModelParams1 x1424
                          then
                            x1424.hostMetric
                          else
                            let #var"1158" =
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
                      let #var"1159" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                      in
                      exit 1))
                x1201
            with
              (st740, x1202)
            in
            p_apply st740 x1199 x1202
  in
  let getGainRate1 =
    lam st712.
      lam repertoire13.
        lam hostIndex32.
          lam modelParams122.
            let fromState52 = get repertoire13 (subi hostIndex32 1) in
            match
              p_map
                st712
                (lam x1149.
                   addi x1149 1)
                fromState52
            with
              (st713, x1150)
            in
            match
              p_map
                st713
                (lam x1152.
                   addi (addi x1152 1) 1)
                fromState52
            with
              (st714, x1153)
            in
            match
              mtxGet3
                st714
                x1150
                x1153
                (match
                   match modelParams122 with ModelParams1 x1443
                   then
                     x1443.embeddedQMatrix
                   else
                     let #var"1144" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1433
                 then
                   x1433.mat
                 else
                   let #var"1145" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   let x1154 = exit 1 in
                   match x1154 with {arr = x1155}
                   in
                   match x1154 with {n = x1156}
                   in
                   match x1154 with {m = x1157}
                   in
                   { arr = p_pure x1155, n = p_pure x1156, m = p_pure x1157 })
            with
              (st715, baseRate12)
            in
            p_bind
              st715
              hrmStoreSubmodel
              (hrmInit {})
              (lam st716.
                 lam x1158.
                   match eqi x1158 0 with true
                   then
                     match
                       p_map
                         st716
                         (lam x1159.
                            lam x1160.
                              mulf x1159 x1160)
                         baseRate12
                     with
                       (st717, x1161)
                     in
                     match sapply st717 repertoire13 with (st718, x1162)
                     in
                     match whichTrue1 st718 x1162 with (st719, x1163)
                     in
                     match
                       mtxRowCols1
                         st719
                         (match modelParams122 with ModelParams1 x1393
                          then
                            x1393.hostMetric
                          else
                            let #var"1146" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex32
                         x1163
                     with
                       (st720, x1164)
                     in
                     match mtxMean1 st720 x1164 with (st721, x1165)
                     in
                     match
                       p_map
                         st721
                         (lam x1166.
                            divf
                              x1166
                              (match modelParams122 with ModelParams1 x1373
                               then
                                 x1373.meanDist
                               else
                                 let #var"1147" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x1165
                     with
                       (st722, x1167)
                     in
                     match
                       p_map
                         st722
                         (lam x1168.
                            negf x1168)
                         (match modelParams122 with ModelParams1 x1383
                          then
                            x1383.beta
                          else
                            let #var"1148" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st723, x1169)
                     in
                     match pow2 st723 x1167 x1169 with (st724, x1170)
                     in
                     p_apply st724 x1161 x1170
                   else match
                     p_map
                       st716
                       (lam x1171.
                          lam x1172.
                            mulf x1171 x1172)
                       baseRate12
                   with
                     (st725, x1173)
                   in
                   match sapply1 st725 repertoire13 with (st726, x1174)
                   in
                   match whichTrue1 st726 x1174 with (st727, x1175)
                   in
                   match
                     mtxRowCols1
                       st727
                       (match modelParams122 with ModelParams1 x1423
                        then
                          x1423.hostMetric
                        else
                          let #var"1149" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex32
                       x1175
                   with
                     (st728, x1176)
                   in
                   match mtxMean1 st728 x1176 with (st729, x1177)
                   in
                   match
                     p_map
                       st729
                       (lam x1178.
                          divf
                            x1178
                            (match modelParams122 with ModelParams1 x1403
                             then
                               x1403.meanDist
                             else
                               let #var"1150" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1177
                   with
                     (st730, x1179)
                   in
                   match
                     p_map
                       st730
                       (lam x1180.
                          negf x1180)
                       (match modelParams122 with ModelParams1 x1413
                        then
                          x1413.beta
                        else
                          let #var"1151" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st731, x1181)
                   in
                   match pow2 st731 x1179 x1181 with (st732, x1182)
                   in
                   p_apply st732 x1173 x1182)
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
                   lam x1109.
                     (st687, x1109))
                repertoire12
            with
              (st688, x1110)
            in
            match p_map st688 get x1110 with (st689, x1111)
            in
            match
              p_map
                st689
                (lam x1112.
                   subi x1112 1)
                hostIndex31
            with
              (st690, x1113)
            in
            match p_apply st690 x1111 x1113 with (st691, fromState51)
            in
            match
              p_map
                st691
                (lam x1114.
                   addi x1114 1)
                fromState51
            with
              (st692, x1115)
            in
            match p_map st692 (lam f. printLn (join ["FromState ", int2string f]))  fromState51 with (st692, _) in
            match
              p_map
                st692
                (lam x1116.
                   addi (addi x1116 1) 1)
                fromState51
            with
              (st693, x1117)
            in
            match
              mtxGet3
                st693
                x1115
                x1117
                (match
                   match modelParams121 with ModelParams1 x1442
                   then
                     x1442.embeddedQMatrix
                   else
                     let #var"1136" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1432
                 then
                   x1432.mat
                 else
                   let #var"1137" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   let x1118 = exit 1 in
                   match x1118 with {arr = x1119}
                   in
                   match x1118 with {n = x1120}
                   in
                   match x1118 with {m = x1121}
                   in
                   { arr = p_pure x1119, n = p_pure x1120, m = p_pure x1121 })
            with
              (st694, baseRate11)
            in
            p_bind
              st694
              hrmStoreSubmodel
              (hrmInit {})
              (lam st695.
                 lam x1122.
                   match eqi x1122 0 with true
                   then
                     match
                       p_map
                         st695
                         (lam x1123.
                            lam x1124.
                              mulf x1123 x1124)
                         baseRate11
                     with
                       (st696, x1125)
                     in
                     match sapply st696 repertoire12 with (st697, x1126)
                     in
                     match whichTrue1 st697 x1126 with (st698, x1127)
                     in
                     match
                       mtxRowCols2
                         st698
                         (match modelParams121 with ModelParams1 x1392
                          then
                            x1392.hostMetric
                          else
                            let #var"1138" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex31
                         x1127
                     with
                       (st699, x1128)
                     in
                     match mtxMean1 st699 x1128 with (st700, x1129)
                     in
                     match
                       p_map
                         st700
                         (lam x1130.
                            divf
                              x1130
                              (match modelParams121 with ModelParams1 x1372
                               then
                                 x1372.meanDist
                               else
                                 let #var"1139" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x1129
                     with
                       (st701, x1132)
                     in
                     match
                       p_map
                         st701
                         (lam x1133.
                            negf x1133)
                         (match modelParams121 with ModelParams1 x1382
                          then
                            x1382.beta
                          else
                            let #var"1140" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st702, x1134)
                     in
                     match pow2 st702 x1132 x1134 with (st703, x1135)
                     in
                     p_apply st703 x1125 x1135
                   else match
                     p_map
                       st695
                       (lam x1136.
                          lam x1137.
                            mulf x1136 x1137)
                       baseRate11
                   with
                     (st704, x1138)
                   in
                   match sapply1 st704 repertoire12 with (st705, x1139)
                   in
                   match whichTrue1 st705 x1139 with (st706, x1140)
                   in
                   match
                     mtxRowCols2
                       st706
                       (match modelParams121 with ModelParams1 x1422
                        then
                          x1422.hostMetric
                        else
                          let #var"1141" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex31
                       x1140
                   with
                     (st707, x1142)
                   in
                   match mtxMean1 st707 x1142 with (st708, x1143)
                   in
                   match
                     p_map
                       st708
                       (lam x1144.
                          divf
                            x1144
                            (match modelParams121 with ModelParams1 x1402
                             then
                               x1402.meanDist
                             else
                               let #var"1142" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1143
                   with
                     (st709, x1145)
                   in
                   match
                     p_map
                       st709
                       (lam x1146.
                          negf x1146)
                       (match modelParams121 with ModelParams1 x1412
                        then
                          x1412.beta
                        else
                          let #var"1143" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st710, x1147)
                   in
                   match pow2 st710 x1145 x1147 with (st711, x1148)
                   in
                   p_apply st711 x1138 x1148)
              fromState51
  in
  let getGainRate3 =
    lam st662.
      lam repertoire11.
        lam hostIndex3.
          lam modelParams12.
            match p_map st662 get repertoire11 with (st663, x1060)
            in
            match
              p_map
                st663 (lam x1063.
                   subi x1063 1) hostIndex3
            with
              (st664, x1064)
            in
            match p_apply st664 x1060 x1064 with (st665, fromState5)
            in
            match
              p_map
                st665 (lam x1065.
                   addi x1065 1) fromState5
            with
              (st666, x1066)
            in
            match
              p_map
                st666
                (lam x1067.
                   addi (addi x1067 1) 1)
                fromState5
            with
              (st667, x1068)
            in
            match
              mtxGet3
                st667
                x1066
                x1068
                (match
                   match modelParams12 with ModelParams1 x1441
                   then
                     x1441.embeddedQMatrix
                   else
                     let #var"1128" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1431
                 then
                   x1431.mat
                 else
                   let #var"1129" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   let x1069 = exit 1 in
                   match x1069 with {arr = x1070}
                   in
                   match x1069 with {n = x1073}
                   in
                   match x1069 with {m = x1074}
                   in
                   { arr = p_pure x1070, n = p_pure x1073, m = p_pure x1074 })
            with
              (st668, baseRate1)
            in
            p_bind
              st668
              hrmStoreSubmodel
              (hrmInit {})
              (lam st669.
                 lam x1075.
                   match eqi x1075 0 with true
                   then
                     match
                       p_map
                         st669
                         (lam x1076.
                            lam x1077.
                              mulf x1076 x1077)
                         baseRate1
                     with
                       (st670, x1078)
                     in
                     match
                       p_map
                         st670
                         (lam x1079.
                            match x1079 with [ _,
                                _ ] ++ _
                            then
                              match splitAt x1079 1 with {#label"1" = x1080}
                              in
                              cons (anon7 (get x1079 0)) (rec4 x1080)
                            else match x1079 with [ e17 ]
                            then
                              match splitAt x1079 1 with {#label"1" = x1083}
                              in
                              let slice16 = x1083 in
                              [ anon7 e17 ]
                            else match x1079 with ""
                            in
                            "")
                         repertoire11
                     with
                       (st671, x1084)
                     in
                     match whichTrue2 st671 x1084 with (st672, x1085)
                     in
                     match
                       mtxRowCols2
                         st672
                         (match modelParams12 with ModelParams1 x1391
                          then
                            x1391.hostMetric
                          else
                            let #var"1130" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                            in
                            exit 1)
                         hostIndex3
                         x1085
                     with
                       (st673, x1086)
                     in
                     match mtxMean1 st673 x1086 with (st674, x1087)
                     in
                     match
                       p_map
                         st674
                         (lam x1088.
                            divf
                              x1088
                              (match modelParams12 with ModelParams1 x1371
                               then
                                 x1371.meanDist
                               else
                                 let #var"1131" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                                 in
                                 exit 1))
                         x1087
                     with
                       (st675, x1089)
                     in
                     match
                       p_map
                         st675
                         (lam x1090.
                            negf x1090)
                         (match modelParams12 with ModelParams1 x1381
                          then
                            x1381.beta
                          else
                            let #var"1132" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                            in
                            p_pure (exit 1))
                     with
                       (st676, x1092)
                     in
                     match pow2 st676 x1089 x1092 with (st677, x1093)
                     in
                     p_apply st677 x1078 x1093
                   else match
                     p_map
                       st669
                       (lam x1094.
                          lam x1095.
                            mulf x1094 x1095)
                       baseRate1
                   with
                     (st678, x1096)
                   in
                   match
                     p_map
                       st678
                       (lam x1097.
                          match x1097 with [ _,
                              _ ] ++ _
                          then
                            match splitAt x1097 1 with {#label"1" = x1098}
                            in
                            cons (anon9 (get x1097 0)) (rec6 x1098)
                          else match x1097 with [ e18 ]
                          then
                            match splitAt x1097 1 with {#label"1" = x1099}
                            in
                            let slice17 = x1099 in
                            [ anon9 e18 ]
                          else match x1097 with ""
                          in
                          "")
                       repertoire11
                   with
                     (st679, x1100)
                   in
                   match whichTrue2 st679 x1100 with (st680, x1101)
                   in
                   match
                     mtxRowCols2
                       st680
                       (match modelParams12 with ModelParams1 x1421
                        then
                          x1421.hostMetric
                        else
                          let #var"1133" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                          in
                          exit 1)
                       hostIndex3
                       x1101
                   with
                     (st681, x1102)
                   in
                   match mtxMean1 st681 x1102 with (st682, x1103)
                   in
                   match
                     p_map
                       st682
                       (lam x1104.
                          divf
                            x1104
                            (match modelParams12 with ModelParams1 x1401
                             then
                               x1401.meanDist
                             else
                               let #var"1134" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                               in
                               exit 1))
                       x1103
                   with
                     (st683, x1105)
                   in
                   match
                     p_map
                       st683
                       (lam x1106.
                          negf x1106)
                       (match modelParams12 with ModelParams1 x1411
                        then
                          x1411.beta
                        else
                          let #var"1135" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                          in
                          p_pure (exit 1))
                   with
                     (st684, x1107)
                   in
                   match pow2 st684 x1105 x1107 with (st685, x1108)
                   in
                   p_apply st685 x1096 x1108)
              fromState5
  in
  let anon11 =
    lam x1058.
      lam x1059.
        match eqi x1059 2 with true
        then
          addi x1058 1
        else
          x1058
  in
  recursive
    let rec26 =
      lam acc6.
        lam s27.
          match s27 with [ _ ] ++ _
          then
            match splitAt s27 1 with {#label"1" = x104}
            in
            rec26 (anon11 acc6 (get s27 0)) x104
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
                     lam x105.
                       match eqi x105 2 with true
                       then
                         p_map
                           st82
                           (lam x106.
                              addi x106 1)
                           acc7
                       else
                         (st82, acc7))
                  (get s28 0)
              with
                (st83, x107)
              in
              match splitAt s28 1 with {#label"1" = x108}
              in
              rec27 st83 x107 x108
            else match s28 with ""
            in
            (st81, acc7)
  in
  let fold1 =
    lam st660.
      lam init12.
        lam seq52.
          match seq52 with [ _ ] ++ _
          then
            match
              p_map
                st660
                (lam x1055.
                   match eqi x1055 2 with true
                   then
                     addi init12 1
                   else
                     init12)
                (get seq52 0)
            with
              (st661, x1056)
            in
            match splitAt seq52 1 with {#label"1" = x1057}
            in
            rec27 st661 x1056 x1057
          else match seq52 with ""
          in
          (st660, p_pure init12)
  in
  let getLossRate =
    lam st659.
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
              (st659, p_pure 0.)
            else
              mtxGet
                st659
                (addi fromState33 1)
                (addi (subi fromState33 1) 1)
                (match
                   match modelParams103 with ModelParams1 x1354
                   then
                     x1354.embeddedQMatrix
                   else
                     let #var"1126" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                     in
                     exit 1
                 with
                   EmbeddedMarkovChainMatrix1 x1344
                 then
                   x1344.mat
                 else
                   let #var"1127" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                   in
                   let x1051 = exit 1 in
                   match x1051 with {arr = x1052}
                   in
                   match x1051 with {n = x1053}
                   in
                   match x1051 with {m = x1054}
                   in
                   { arr = p_pure x1052, n = p_pure x1053, m = p_pure x1054 })
  in
  let getLossRate1 =
    lam st652.
      lam repertoire2.
        lam hostIndex22.
          lam modelParams102.
            let fromState32 = get repertoire2 (subi hostIndex22 1) in
            match
              p_bind
                st652
                hrmStoreSubmodel
                (hrmInit {})
                (lam st653.
                   lam x1036.
                     match eqi x1036 2 with true
                     then
                       match fold1 st653 0 repertoire2 with (st654, x1037)
                       in
                       p_map
                         st654
                         (lam x1038.
                            eqi x1038 1)
                         x1037
                     else
                       (st653, p_pure false))
                fromState32
            with
              (st655, x1039)
            in
            p_bind
              st655
              hrmStoreSubmodel
              (hrmInit {})
              (lam st656.
                 lam x1040.
                   match x1040 with true
                   then
                     (st656, p_pure 0.)
                   else match
                     p_map
                       st656
                       (lam x1043.
                          addi x1043 1)
                       fromState32
                   with
                     (st657, x1044)
                   in
                   match
                     p_map
                       st657
                       (lam x1045.
                          addi (subi x1045 1) 1)
                       fromState32
                   with
                     (st658, x1046)
                   in
                   mtxGet3
                     st658
                     x1044
                     x1046
                     (match
                        match modelParams102 with ModelParams1 x1353
                        then
                          x1353.embeddedQMatrix
                        else
                          let #var"1124" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1343
                      then
                        x1343.mat
                      else
                        let #var"1125" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        let x1047 = exit 1 in
                        match x1047 with {arr = x1048}
                        in
                        match x1047 with {n = x1049}
                        in
                        match x1047 with {m = x1050}
                        in
                        { arr = p_pure x1048, n = p_pure x1049, m = p_pure x1050 }))
              x1039
  in
  let getLossRate2 =
    lam st640.
      lam repertoire1.
        lam hostIndex21.
          lam modelParams101.
            match
              p_traverseSeq
                st640
                (lam st641.
                   lam x1018.
                     (st641, x1018))
                repertoire1
            with
              (st642, x1019)
            in
            match p_map st642 get x1019 with (st643, x1020)
            in
            match
              p_map
                st643
                (lam x1021.
                   subi x1021 1)
                hostIndex21
            with
              (st644, x1022)
            in
            match p_apply st644 x1020 x1022 with (st645, fromState31)
            in
            match
              p_bind
                st645
                hrmStoreSubmodel
                (hrmInit {})
                (lam st646.
                   lam x1023.
                     match eqi x1023 2 with true
                     then
                       match fold1 st646 0 repertoire1 with (st647, x1024)
                       in
                       p_map
                         st647
                         (lam x1025.
                            eqi x1025 1)
                         x1024
                     else
                       (st646, p_pure false))
                fromState31
            with
              (st648, x1026)
            in
            p_bind
              st648
              hrmStoreSubmodel
              (hrmInit {})
              (lam st649.
                 lam x1027.
                   match x1027 with true
                   then
                     (st649, p_pure 0.)
                   else match
                     p_map
                       st649
                       (lam x1028.
                          addi x1028 1)
                       fromState31
                   with
                     (st650, x1029)
                   in
                   match
                     p_map
                       st650
                       (lam x1030.
                          addi (subi x1030 1) 1)
                       fromState31
                   with
                     (st651, x1031)
                   in
                   mtxGet3
                     st651
                     x1029
                     x1031
                     (match
                        match modelParams101 with ModelParams1 x1352
                        then
                          x1352.embeddedQMatrix
                        else
                          let #var"1122" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1342
                      then
                        x1342.mat
                      else
                        let #var"1123" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        let x1032 = exit 1 in
                        match x1032 with {arr = x1033}
                        in
                        match x1032 with {n = x1034}
                        in
                        match x1032 with {m = x1035}
                        in
                        { arr = p_pure x1033, n = p_pure x1034, m = p_pure x1035 }))
              x1026
  in
  let getLossRate3 =
    lam st630.
      lam repertoire.
        lam hostIndex2.
          lam modelParams10.
            match p_map st630 get repertoire with (st631, x1000)
            in
            match
              p_map
                st631 (lam x1001.
                   subi x1001 1) hostIndex2
            with
              (st632, x1002)
            in
            match p_apply st632 x1000 x1002 with (st633, fromState3)
            in
            match
              p_bind
                st633
                hrmStoreSubmodel
                (hrmInit {})
                (lam st634.
                   lam x1003.
                     match eqi x1003 2 with true
                     then
                       match
                         p_map
                           st634
                           (lam x1004.
                              match x1004 with [ _ ] ++ _
                              then
                                match splitAt x1004 1 with {#label"1" = x1005}
                                in
                                rec26 (anon11 0 (get x1004 0)) x1005
                              else match x1004 with ""
                              in
                              0)
                           repertoire
                       with
                         (st635, x1006)
                       in
                       p_map
                         st635
                         (lam x1007.
                            eqi x1007 1)
                         x1006
                     else
                       (st634, p_pure false))
                fromState3
            with
              (st636, x1008)
            in
            p_bind
              st636
              hrmStoreSubmodel
              (hrmInit {})
              (lam st637.
                 lam x1009.
                   match x1009 with true
                   then
                     (st637, p_pure 0.)
                   else match
                     p_map
                       st637
                       (lam x1010.
                          addi x1010 1)
                       fromState3
                   with
                     (st638, x1011)
                   in
                   match
                     p_map
                       st638
                       (lam x1012.
                          addi (subi x1012 1) 1)
                       fromState3
                   with
                     (st639, x1013)
                   in
                   mtxGet3
                     st639
                     x1011
                     x1013
                     (match
                        match modelParams10 with ModelParams1 x1351
                        then
                          x1351.embeddedQMatrix
                        else
                          let #var"1120" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                          in
                          exit 1
                      with
                        EmbeddedMarkovChainMatrix1 x1341
                      then
                        x1341.mat
                      else
                        let #var"1121" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                        in
                        let x1014 = exit 1 in
                        match x1014 with {arr = x1015}
                        in
                        match x1014 with {n = x1016}
                        in
                        match x1014 with {m = x1017}
                        in
                        { arr = p_pure x1015, n = p_pure x1016, m = p_pure x1017 }))
              x1008
  in
  recursive
    let rec28 =
      lam st84.
        lam c19.
          lam c20.
            lam acc8.
              lam s29.
                match s29 with [ _ ] ++ _
                then
                  let x109 = get s29 0 in
                  match
                    p_bind
                      st84
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st85.
                         lam x110.
                           match eqi x110 2 with true
                           then
                             (st85, acc8)
                           else match
                             p_map
                               st85
                               (lam x111.
                                  lam x112.
                                    addf x111 x112)
                               acc8
                           with
                             (st86, x113)
                           in
                           match getGainRate1 st86 c19 x109 c20 with (st87, x114)
                           in
                           p_apply st87 x113 x114)
                      (get c19 (subi x109 1))
                  with
                    (st88, x115)
                  in
                  match splitAt s29 1 with {#label"1" = x116}
                  in
                  rec28 st88 c19 c20 x115 x116
                else match s29 with ""
                in
                (st84, acc8)
    let rec29 =
      lam st89.
        lam c21.
          lam c22.
            lam acc9.
              lam s210.
                match s210 with [ _ ] ++ _
                then
                  let x117 = get s210 0 in
                  match
                    p_bind
                      st89
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st90.
                         lam x118.
                           match eqi (get x118 (subi x117 1)) 2 with true
                           then
                             (st90, acc9)
                           else match
                             p_map
                               st90
                               (lam x119.
                                  lam x120.
                                    addf x119 x120)
                               acc9
                           with
                             (st91, x121)
                           in
                           match getGainRate st91 x118 x117 c22 with (st92, x122)
                           in
                           p_apply st92 x121 x122)
                      c21
                  with
                    (st93, x123)
                  in
                  match splitAt s210 1 with {#label"1" = x124}
                  in
                  rec29 st93 c21 c22 x123 x124
                else match s210 with ""
                in
                (st89, acc9)
  in
  let anon12 = lam x999.
      addi x999 1 in
  recursive
    let rec32 =
      lam i13.
        lam acc13.
          match geqi i13 0 with true
          then
            rec32 (subi i13 1) (cons (anon12 i13) acc13)
          else
            acc13
  in
  let create1 =
    lam l73.
      let i112 = subi l73 1 in
      match geqi i112 0 with true
      then
        rec32 (subi i112 1) (cons (anon12 i112) "")
      else
        ""
  in
  recursive
    let rec210 =
      lam st94.
        lam c23.
          lam c24.
            lam acc10.
              lam s211.
                match s211 with [ _ ] ++ _
                then
                  let x125 = get s211 0 in
                  match
                    p_bind
                      st94
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st95.
                         lam x126.
                           match eqi x126 0 with true
                           then
                             (st95, acc10)
                           else match
                             p_map
                               st95
                               (lam x127.
                                  lam x128.
                                    addf x127 x128)
                               acc10
                           with
                             (st96, x129)
                           in
                           match getLossRate1 st96 c23 x125 c24 with (st97, x130)
                           in
                           p_apply st97 x129 x130)
                      (get c23 (subi x125 1))
                  with
                    (st98, x131)
                  in
                  match splitAt s211 1 with {#label"1" = x132}
                  in
                  rec210 st98 c23 c24 x131 x132
                else match s211 with ""
                in
                (st94, acc10)
    let rec211 =
      lam st99.
        lam c25.
          lam c26.
            lam acc14.
              lam s212.
                match s212 with [ _ ] ++ _
                then
                  let x133 = get s212 0 in
                  match
                    p_bind
                      st99
                      hrmStoreSubmodel
                      (hrmInit {})
                      (lam st100.
                         lam x134.
                           match eqi (get x134 (subi x133 1)) 0 with true
                           then
                             (st100, acc14)
                           else match
                             p_map
                               st100
                               (lam x135.
                                  lam x136.
                                    addf x135 x136)
                               acc14
                           with
                             (st101, x137)
                           in
                           match getLossRate st101 x134 x133 c26 with (st102, x138)
                           in
                           p_apply st102 x137 x138)
                      c25
                  with
                    (st103, x139)
                  in
                  match splitAt s212 1 with {#label"1" = x140}
                  in
                  rec211 st103 c25 c26 x139 x140
                else match s212 with ""
                in
                (st99, acc14)
  in
  let anon13 = lam x998.
      addi x998 1 in
  recursive
    let rec33 =
      lam i14.
        lam acc15.
          match geqi i14 0 with true
          then
            rec33 (subi i14 1) (cons (anon13 i14) acc15)
          else
            acc15
  in
  let create11 =
    lam l72.
      let i111 = subi l72 1 in
      match geqi i111 0 with true
      then
        rec33 (subi i111 1) (cons (anon13 i111) "")
      else
        ""
  in
  let getTotalRate =
    lam st620.
      lam currRep51.
        lam modelParams81.
          lam nhosts61.
            let s224 = create1 (addi (subi nhosts61 1) 1) in
            match
              match s224 with [ _ ] ++ _
              then
                let x981 = get s224 0 in
                match
                  p_bind
                    st620
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st621.
                       lam x982.
                         match eqi x982 2 with true
                         then
                           (st621, p_pure 0.)
                         else match getGainRate1 st621 currRep51 x981 modelParams81 with (st622, x983)
                         in
                         p_map
                           st622
                           (lam x984.
                              addf 0. x984)
                           x983)
                    (get currRep51 (subi x981 1))
                with
                  (st623, x985)
                in
                match splitAt s224 1 with {#label"1" = x986}
                in
                rec28 st623 currRep51 modelParams81 x985 x986
              else match s224 with ""
              in
              (st620, p_pure 0.)
            with
              (st624, x987)
            in
            match
              p_map
                st624
                (lam x988.
                   lam x989.
                     addf x988 x989)
                x987
            with
              (st625, x990)
            in
            let s225 = create11 (addi (subi nhosts61 1) 1) in
            match
              match s225 with [ _ ] ++ _
              then
                let x991 = get s225 0 in
                match
                  p_bind
                    st625
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st626.
                       lam x992.
                         match eqi x992 0 with true
                         then
                           (st626, p_pure 0.)
                         else match getLossRate1 st626 currRep51 x991 modelParams81 with (st627, x993)
                         in
                         p_map
                           st627
                           (lam x994.
                              addf 0. x994)
                           x993)
                    (get currRep51 (subi x991 1))
                with
                  (st628, x995)
                in
                match splitAt s225 1 with {#label"1" = x996}
                in
                rec210 st628 currRep51 modelParams81 x995 x996
              else match s225 with ""
              in
              (st625, p_pure 0.)
            with
              (st629, x997)
            in
            p_apply st629 x990 x997
  in
  let getTotalRate1 =
    lam st610.
      lam currRep5.
        lam modelParams8.
          lam nhosts6.
            let s222 = create1 (addi (subi nhosts6 1) 1) in
            match
              match s222 with [ _ ] ++ _
              then
                let x964 = get s222 0 in
                match
                  p_bind
                    st610
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st611.
                       lam x965.
                         match eqi (get x965 (subi x964 1)) 2 with true
                         then
                           (st611, p_pure 0.)
                         else match getGainRate st611 x965 x964 modelParams8 with (st612, x966)
                         in
                         p_map
                           st612
                           (lam x967.
                              addf 0. x967)
                           x966)
                    currRep5
                with
                  (st613, x968)
                in
                match splitAt s222 1 with {#label"1" = x969}
                in
                rec29 st613 currRep5 modelParams8 x968 x969
              else match s222 with ""
              in
              (st610, p_pure 0.)
            with
              (st614, x970)
            in
            match
              p_map
                st614
                (lam x971.
                   lam x972.
                     addf x971 x972)
                x970
            with
              (st615, x973)
            in
            let s223 = create11 (addi (subi nhosts6 1) 1) in
            match
              match s223 with [ _ ] ++ _
              then
                let x974 = get s223 0 in
                match
                  p_bind
                    st615
                    hrmStoreSubmodel
                    (hrmInit {})
                    (lam st616.
                       lam x975.
                         match eqi (get x975 (subi x974 1)) 0 with true
                         then
                           (st616, p_pure 0.)
                         else match getLossRate st616 x975 x974 modelParams8 with (st617, x976)
                         in
                         p_map
                           st617
                           (lam x977.
                              addf 0. x977)
                           x976)
                    currRep5
                with
                  (st618, x978)
                in
                match splitAt s223 1 with {#label"1" = x979}
                in
                rec211 st618 currRep5 modelParams8 x978 x979
              else match s223 with ""
              in
              (st615, p_pure 0.)
            with
              (st619, x980)
            in
            p_apply st619 x973 x980
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
                                (lam x141.
                                   lam x142.
                                     mulf (negf (subf x141 finalAge)) x142)
                                currAge
                            with
                              (st105, x143)
                            in
                            match
                              getTotalRate1 st105 currRep3 modelParams nhosts5
                            with
                              (st106, x144)
                            in
                            p_apply st106 x143 x144
                          else match
                            p_map
                              st104
                              (lam x145.
                                 get x145 (subi nextIndex 1))
                              eventSeq3
                          with
                            (st107, nextEvent)
                          in
                          match
                            p_map
                              st107
                              (lam x146.
                                 match x146 with Event1 x311
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
                              (lam x147.
                                 match x147 with Event1 x1321
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
                            (st110, hostIndex1)
                          in
                          match
                            p_map
                              st110
                              (lam x148.
                                 lam x149.
                                   lam st111.
                                     match
                                       gti
                                         (match x148 with Event1 x1301
                                          then
                                            x1301.fromState
                                          else
                                            let #var"119" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x149
                                     with
                                       true
                                     then
                                       getLossRate3 st111 currRep3 hostIndex1 modelParams
                                     else
                                       getGainRate3 st111 currRep3 hostIndex1 modelParams)
                              nextEvent
                          with
                            (st112, x150)
                          in
                          match
                            p_map
                              st112
                              (lam x151.
                                 match x151 with Event1 x1311
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
                            (st113, x154)
                          in
                          match
                            p_subApply st113 hrmStoreSubmodel (hrmInit {}) x150 x154
                          with
                            (st114, x155)
                          in
                          match p_join st114 x155 with (st115, x156)
                          in
                          match
                            p_map
                              st115
                              (lam x157.
                                 lam x158.
                                   divf x157 x158)
                              x156
                          with
                            (st116, x159)
                          in
                          match p_apply st116 x159 totalLeavingRate1 with (st117, x160)
                          in
                          match log11 st117 x160 with (st118, x161)
                          in
                          match
                            p_map
                              st118
                              (lam x162.
                                 lam x163.
                                   lam x164.
                                     addf (subf x162 x163) x164)
                              x161
                          with
                            (st119, x165)
                          in
                          match
                            p_map
                              st119
                              (lam x166.
                                 lam x167.
                                   lam x168.
                                     mulf (subf x166 x167) x168)
                              currAge
                          with
                            (st120, x169)
                          in
                          match p_apply st120 x169 newAge with (st121, x170)
                          in
                          match p_apply st121 x170 totalLeavingRate1 with (st122, x171)
                          in
                          match p_apply st122 x165 x171 with (st123, x172)
                          in
                          match
                            updateRepertoire1 st123 currRep3 nextEvent nhosts5
                          with
                            (st124, x173)
                          in
                          match
                            fullModelWeight
                              st124
                              (addi nextIndex 1)
                              x173
                              finalRep
                              newAge
                              finalAge
                              eventSeq3
                              nEvents3
                              nhosts5
                              modelParams
                          with
                            (st125, x174)
                          in
                          p_apply st125 x172 x174
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
                                (lam x175.
                                   lam x176.
                                     mulf (negf (subf x175 finalAge1)) x176)
                                currAge1
                            with
                              (st127, x177)
                            in
                            match
                              getTotalRate1 st127 currRep31 modelParams1 nhosts51
                            with
                              (st128, x178)
                            in
                            p_apply st128 x177 x178
                          else match
                            p_map
                              st126
                              (lam x179.
                                 get x179 (subi nextIndex1 1))
                              eventSeq31
                          with
                            (st129, nextEvent1)
                          in
                          match
                            p_map
                              st129
                              (lam x180.
                                 match x180 with Event1 x312
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
                              (lam x181.
                                 match x181 with Event1 x1322
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
                            (st132, hostIndex11)
                          in
                          match
                            p_map
                              st132
                              (lam x182.
                                 lam x183.
                                   lam st133.
                                     match
                                       gti
                                         (match x182 with Event1 x1302
                                          then
                                            x1302.fromState
                                          else
                                            let #var"123" =
                                              print
                                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                            in
                                            exit 1)
                                         x183
                                     with
                                       true
                                     then
                                       getLossRate3 st133 currRep31 hostIndex11 modelParams1
                                     else
                                       getGainRate3 st133 currRep31 hostIndex11 modelParams1)
                              nextEvent1
                          with
                            (st134, x184)
                          in
                          match
                            p_map
                              st134
                              (lam x185.
                                 match x185 with Event1 x1312
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
                            (st135, x186)
                          in
                          match
                            p_subApply st135 hrmStoreSubmodel (hrmInit {}) x184 x186
                          with
                            (st136, x187)
                          in
                          match p_join st136 x187 with (st137, x188)
                          in
                          match
                            p_map
                              st137
                              (lam x189.
                                 lam x190.
                                   divf x189 x190)
                              x188
                          with
                            (st138, x191)
                          in
                          match p_apply st138 x191 totalLeavingRate11 with (st139, x192)
                          in
                          match log11 st139 x192 with (st140, x193)
                          in
                          match
                            p_map
                              st140
                              (lam x194.
                                 lam x195.
                                   lam x196.
                                     addf (subf x194 x195) x196)
                              x193
                          with
                            (st141, x197)
                          in
                          match
                            p_map
                              st141
                              (lam x198.
                                 lam x199.
                                   lam x200.
                                     mulf (subf x198 x199) x200)
                              currAge1
                          with
                            (st142, x201)
                          in
                          match p_apply st142 x201 newAge1 with (st143, x202)
                          in
                          match p_apply st143 x202 totalLeavingRate11 with (st144, x203)
                          in
                          match p_apply st144 x197 x203 with (st145, x204)
                          in
                          match
                            updateRepertoire1 st145 currRep31 nextEvent1 nhosts51
                          with
                            (st146, x205)
                          in
                          match
                            fullModelWeight1
                              st146
                              (addi nextIndex1 1)
                              x205
                              finalRep1
                              newAge1
                              finalAge1
                              eventSeq31
                              nEvents31
                              nhosts51
                              modelParams1
                          with
                            (st147, x206)
                          in
                          p_apply st147 x204 x206
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
                      match length13 st148 eventSeq4 with (st149, x207)
                      in
                      p_bind
                        st149
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st150.
                           lam x208.
                             match gti nextIndex11 x208 with true
                             then
                               match
                                 p_traverseSeq
                                   st150
                                   (lam st151.
                                      lam x209.
                                        (st151, x209))
                                   (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x321
                                    then
                                      x321.totalRates
                                    else
                                      let #var"125" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x210.
                                           p_pure x210)
                                        (exit 1))
                               with
                                 (st152, x211)
                               in
                               match
                                 p_map
                                   st152
                                   (lam x212.
                                      lam x213.
                                        mulf (negf (subf currAge11 finalAge11)) (get x212 x213))
                                   x211
                               with
                                 (st153, x214)
                               in
                               match
                                 p_map
                                   st153
                                   (lam x215.
                                      subi (addi x215 1) 1)
                                   currState
                               with
                                 (st154, x216)
                               in
                               p_apply st154 x214 x216
                             else match
                               p_map
                                 st150
                                 (lam x217.
                                    get x217 (subi nextIndex11 1))
                                 eventSeq4
                             with
                               (st155, nextEvent11)
                             in
                             match
                               p_map
                                 st155
                                 (lam x218.
                                    match x218 with Event1 x361
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
                               (st156, nextState)
                             in
                             match
                               p_map
                                 st156
                                 (lam x219.
                                    match x219 with Event1 x351
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
                               (st157, nextAge)
                             in
                             match
                               p_traverseSeq
                                 st157
                                 (lam st158.
                                    lam x220.
                                      p_traverseSeq
                                        st158
                                        (lam st159.
                                           lam x222.
                                             (st159, x222))
                                        x220)
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x331
                                  then
                                    x331.transitionProbs
                                  else
                                    let #var"128" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x223.
                                         map
                                           (lam x224.
                                              p_pure x224)
                                           x223)
                                      (exit 1))
                             with
                               (st160, x225)
                             in
                             match
                               p_map
                                 st160
                                 (lam x226.
                                    lam x227.
                                      get (get x226 x227))
                                 x225
                             with
                               (st161, x228)
                             in
                             match
                               p_map
                                 st161
                                 (lam x229.
                                    subi (addi x229 1) 1)
                                 currState
                             with
                               (st162, x230)
                             in
                             match p_apply st162 x228 x230 with (st163, x232)
                             in
                             match
                               p_map
                                 st163
                                 (lam x233.
                                    subi (addi x233 1) 1)
                                 nextState
                             with
                               (st164, x234)
                             in
                             match p_apply st164 x232 x234 with (st165, x235)
                             in
                             match log11 st165 x235 with (st166, x236)
                             in
                             match
                               p_map
                                 st166
                                 (lam x237.
                                    lam x238.
                                      lam x239.
                                        addf (subf x237 x238) x239)
                                 x236
                             with
                               (st167, x240)
                             in
                             match
                               p_map
                                 st167
                                 (lam x241.
                                    lam x242.
                                      mulf (subf currAge11 x241) x242)
                                 nextAge
                             with
                               (st168, x243)
                             in
                             match
                               p_traverseSeq
                                 st168
                                 (lam st169.
                                    lam x244.
                                      (st169, x244))
                                 (match embeddedQMatrix with EmbeddedMarkovChainMatrix1 x341
                                  then
                                    x341.totalRates
                                  else
                                    let #var"129" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x245.
                                         p_pure x245)
                                      (exit 1))
                             with
                               (st170, x246)
                             in
                             match p_map st170 get x246 with (st171, x247)
                             in
                             match
                               p_map
                                 st171
                                 (lam x248.
                                    subi (addi x248 1) 1)
                                 currState
                             with
                               (st172, x249)
                             in
                             match p_apply st172 x247 x249 with (st173, x250)
                             in
                             match p_apply st173 x243 x250 with (st174, x251)
                             in
                             match p_apply st174 x240 x251 with (st175, x252)
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
                               (st176, x253)
                             in
                             p_apply st176 x252 x253)
                        x207
    let hostIndepLikelihood1 =
      lam st177.
        lam nextIndex12.
          lam currState1.
            lam finalState1.
              lam currAge12.
                lam finalAge12.
                  lam eventSeq41.
                    lam embeddedQMatrix1.
                      match length13 st177 eventSeq41 with (st178, x254)
                      in
                      p_bind
                        st178
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st179.
                           lam x255.
                             match gti nextIndex12 x255 with true
                             then
                               match
                                 p_map
                                   st179
                                   (lam x256.
                                      lam x257.
                                        mulf (negf (subf x256 finalAge12)) x257)
                                   currAge12
                               with
                                 (st180, x258)
                               in
                               match
                                 p_traverseSeq
                                   st180
                                   (lam st181.
                                      lam x259.
                                        (st181, x259))
                                   (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x322
                                    then
                                      x322.totalRates
                                    else
                                      let #var"130" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x260.
                                           p_pure x260)
                                        (exit 1))
                               with
                                 (st182, x261)
                               in
                               match p_map st182 get x261 with (st183, x262)
                               in
                               match
                                 p_map
                                   st183
                                   (lam x263.
                                      subi (addi x263 1) 1)
                                   currState1
                               with
                                 (st184, x264)
                               in
                               match p_apply st184 x262 x264 with (st185, x265)
                               in
                               p_apply st185 x258 x265
                             else match
                               p_map
                                 st179
                                 (lam x266.
                                    get x266 (subi nextIndex12 1))
                                 eventSeq41
                             with
                               (st186, nextEvent12)
                             in
                             match
                               p_map
                                 st186
                                 (lam x267.
                                    match x267 with Event1 x362
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
                               (st187, nextState1)
                             in
                             match
                               p_map
                                 st187
                                 (lam x268.
                                    match x268 with Event1 x352
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
                               (st188, nextAge1)
                             in
                             match
                               p_traverseSeq
                                 st188
                                 (lam st189.
                                    lam x269.
                                      p_traverseSeq
                                        st189
                                        (lam st190.
                                           lam x270.
                                             (st190, x270))
                                        x269)
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x332
                                  then
                                    x332.transitionProbs
                                  else
                                    let #var"133" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x271.
                                         map
                                           (lam x272.
                                              p_pure x272)
                                           x271)
                                      (exit 1))
                             with
                               (st191, x273)
                             in
                             match
                               p_map
                                 st191
                                 (lam x274.
                                    lam x275.
                                      get (get x274 x275))
                                 x273
                             with
                               (st192, x276)
                             in
                             match
                               p_map
                                 st192
                                 (lam x277.
                                    subi (addi x277 1) 1)
                                 currState1
                             with
                               (st193, x278)
                             in
                             match p_apply st193 x276 x278 with (st194, x279)
                             in
                             match
                               p_map
                                 st194
                                 (lam x280.
                                    subi (addi x280 1) 1)
                                 nextState1
                             with
                               (st195, x281)
                             in
                             match p_apply st195 x279 x281 with (st196, x282)
                             in
                             match log11 st196 x282 with (st197, x283)
                             in
                             match
                               p_map
                                 st197
                                 (lam x284.
                                    lam x285.
                                      lam x286.
                                        addf (subf x284 x285) x286)
                                 x283
                             with
                               (st198, x287)
                             in
                             match
                               p_map
                                 st198
                                 (lam x288.
                                    lam x289.
                                      lam x290.
                                        mulf (subf x288 x289) x290)
                                 currAge12
                             with
                               (st199, x291)
                             in
                             match p_apply st199 x291 nextAge1 with (st200, x292)
                             in
                             match
                               p_traverseSeq
                                 st200
                                 (lam st201.
                                    lam x293.
                                      (st201, x293))
                                 (match embeddedQMatrix1 with EmbeddedMarkovChainMatrix1 x342
                                  then
                                    x342.totalRates
                                  else
                                    let #var"134" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x294.
                                         p_pure x294)
                                      (exit 1))
                             with
                               (st202, x295)
                             in
                             match p_map st202 get x295 with (st203, x296)
                             in
                             match
                               p_map
                                 st203
                                 (lam x297.
                                    subi (addi x297 1) 1)
                                 currState1
                             with
                               (st204, x298)
                             in
                             match p_apply st204 x296 x298 with (st205, x299)
                             in
                             match p_apply st205 x292 x299 with (st206, x300)
                             in
                             match p_apply st206 x287 x300 with (st207, x303)
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
                               (st208, x304)
                             in
                             p_apply st208 x303 x304)
                        x254
    let hostIndepLikelihood2 =
      lam st209.
        lam nextIndex13.
          lam currState2.
            lam finalState2.
              lam currAge13.
                lam finalAge13.
                  lam eventSeq42.
                    lam embeddedQMatrix2.
                      match length13 st209 eventSeq42 with (st210, x305)
                      in
                      p_bind
                        st210
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st211.
                           lam x306.
                             match gti nextIndex13 x306 with true
                             then
                               match
                                 p_traverseSeq
                                   st211
                                   (lam st212.
                                      lam x307.
                                        (st212, x307))
                                   (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x323
                                    then
                                      x323.totalRates
                                    else
                                      let #var"135" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x308.
                                           p_pure x308)
                                        (exit 1))
                               with
                                 (st213, x309)
                               in
                               match
                                 p_map
                                   st213
                                   (lam x310.
                                      lam x313.
                                        mulf (negf (subf currAge13 finalAge13)) (get x310 x313))
                                   x309
                               with
                                 (st214, x314)
                               in
                               match
                                 p_map
                                   st214
                                   (lam x315.
                                      subi (addi x315 1) 1)
                                   currState2
                               with
                                 (st215, x316)
                               in
                               p_apply st215 x314 x316
                             else match
                               p_map
                                 st211
                                 (lam x317.
                                    get x317 (subi nextIndex13 1))
                                 eventSeq42
                             with
                               (st216, nextEvent13)
                             in
                             match
                               p_map
                                 st216
                                 (lam x318.
                                    match x318 with Event1 x363
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
                               (st217, nextState2)
                             in
                             match
                               p_map
                                 st217
                                 (lam x319.
                                    match x319 with Event1 x353
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
                               (st218, nextAge2)
                             in
                             match
                               p_traverseSeq
                                 st218
                                 (lam st219.
                                    lam x320.
                                      p_traverseSeq
                                        st219
                                        (lam st220.
                                           lam x324.
                                             (st220, x324))
                                        x320)
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x333
                                  then
                                    x333.transitionProbs
                                  else
                                    let #var"138" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x325.
                                         map
                                           (lam x326.
                                              p_pure x326)
                                           x325)
                                      (exit 1))
                             with
                               (st221, x327)
                             in
                             match
                               p_map
                                 st221
                                 (lam x328.
                                    lam x329.
                                      get (get x328 x329))
                                 x327
                             with
                               (st222, x330)
                             in
                             match
                               p_map
                                 st222
                                 (lam x334.
                                    subi (addi x334 1) 1)
                                 currState2
                             with
                               (st223, x335)
                             in
                             match p_apply st223 x330 x335 with (st224, x336)
                             in
                             match
                               p_map
                                 st224
                                 (lam x337.
                                    subi (addi x337 1) 1)
                                 nextState2
                             with
                               (st225, x338)
                             in
                             match p_apply st225 x336 x338 with (st226, x339)
                             in
                             match log11 st226 x339 with (st227, x340)
                             in
                             match
                               p_map
                                 st227
                                 (lam x343.
                                    lam x344.
                                      lam x345.
                                        addf (subf x343 x344) x345)
                                 x340
                             with
                               (st228, x346)
                             in
                             match
                               p_map
                                 st228
                                 (lam x347.
                                    lam x348.
                                      mulf (subf currAge13 x347) x348)
                                 nextAge2
                             with
                               (st229, x349)
                             in
                             match
                               p_traverseSeq
                                 st229
                                 (lam st230.
                                    lam x350.
                                      (st230, x350))
                                 (match embeddedQMatrix2 with EmbeddedMarkovChainMatrix1 x3410
                                  then
                                    x3410.totalRates
                                  else
                                    let #var"139" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x354.
                                         p_pure x354)
                                      (exit 1))
                             with
                               (st231, x355)
                             in
                             match p_map st231 get x355 with (st232, x356)
                             in
                             match
                               p_map
                                 st232
                                 (lam x357.
                                    subi (addi x357 1) 1)
                                 currState2
                             with
                               (st233, x358)
                             in
                             match p_apply st233 x356 x358 with (st234, x359)
                             in
                             match p_apply st234 x349 x359 with (st235, x360)
                             in
                             match p_apply st235 x346 x360 with (st236, x364)
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
                               (st237, x365)
                             in
                             p_apply st237 x364 x365)
                        x305
    let hostIndepLikelihood3 =
      lam st238.
        lam nextIndex14.
          lam currState3.
            lam finalState3.
              lam currAge14.
                lam finalAge14.
                  lam eventSeq43.
                    lam embeddedQMatrix3.
                      match length13 st238 eventSeq43 with (st239, x366)
                      in
                      p_bind
                        st239
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st240.
                           lam x367.
                             match gti nextIndex14 x367 with true
                             then
                               match
                                 p_map
                                   st240
                                   (lam x368.
                                      lam x369.
                                        mulf (negf (subf x368 finalAge14)) x369)
                                   currAge14
                               with
                                 (st241, x370)
                               in
                               match
                                 p_traverseSeq
                                   st241
                                   (lam st242.
                                      lam x371.
                                        (st242, x371))
                                   (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3210
                                    then
                                      x3210.totalRates
                                    else
                                      let #var"140" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                      in
                                      map
                                        (lam x372.
                                           p_pure x372)
                                        (exit 1))
                               with
                                 (st243, x373)
                               in
                               match p_map st243 get x373 with (st244, x374)
                               in
                               match
                                 p_map
                                   st244
                                   (lam x375.
                                      subi (addi x375 1) 1)
                                   currState3
                               with
                                 (st245, x376)
                               in
                               match p_apply st245 x374 x376 with (st246, x377)
                               in
                               p_apply st246 x370 x377
                             else match
                               p_map
                                 st240
                                 (lam x378.
                                    get x378 (subi nextIndex14 1))
                                 eventSeq43
                             with
                               (st247, nextEvent14)
                             in
                             match
                               p_map
                                 st247
                                 (lam x379.
                                    match x379 with Event1 x3610
                                    then
                                      x3610.toState
                                    else
                                      let #var"141" =
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
                                 (lam x380.
                                    match x380 with Event1 x3510
                                    then
                                      x3510.eventTime
                                    else
                                      let #var"142" =
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
                                    lam x381.
                                      p_traverseSeq
                                        st250
                                        (lam st251.
                                           lam x382.
                                             (st251, x382))
                                        x381)
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3310
                                  then
                                    x3310.transitionProbs
                                  else
                                    let #var"143" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                                    in
                                    map
                                      (lam x383.
                                         map
                                           (lam x384.
                                              p_pure x384)
                                           x383)
                                      (exit 1))
                             with
                               (st252, x385)
                             in
                             match
                               p_map
                                 st252
                                 (lam x386.
                                    lam x387.
                                      get (get x386 x387))
                                 x385
                             with
                               (st253, x388)
                             in
                             match
                               p_map
                                 st253
                                 (lam x389.
                                    subi (addi x389 1) 1)
                                 currState3
                             with
                               (st254, x390)
                             in
                             match p_apply st254 x388 x390 with (st255, x391)
                             in
                             match
                               p_map
                                 st255
                                 (lam x392.
                                    subi (addi x392 1) 1)
                                 nextState3
                             with
                               (st256, x393)
                             in
                             match p_apply st256 x391 x393 with (st257, x394)
                             in
                             match log11 st257 x394 with (st258, x395)
                             in
                             match
                               p_map
                                 st258
                                 (lam x396.
                                    lam x397.
                                      lam x398.
                                        addf (subf x396 x397) x398)
                                 x395
                             with
                               (st259, x399)
                             in
                             match
                               p_map
                                 st259
                                 (lam x400.
                                    lam x401.
                                      lam x402.
                                        mulf (subf x400 x401) x402)
                                 currAge14
                             with
                               (st260, x403)
                             in
                             match p_apply st260 x403 nextAge3 with (st261, x404)
                             in
                             match
                               p_traverseSeq
                                 st261
                                 (lam st262.
                                    lam x405.
                                      (st262, x405))
                                 (match embeddedQMatrix3 with EmbeddedMarkovChainMatrix1 x3411
                                  then
                                    x3411.totalRates
                                  else
                                    let #var"144" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                                    in
                                    map
                                      (lam x406.
                                         p_pure x406)
                                      (exit 1))
                             with
                               (st263, x407)
                             in
                             match p_map st263 get x407 with (st264, x408)
                             in
                             match
                               p_map
                                 st264
                                 (lam x409.
                                    subi (addi x409 1) 1)
                                 currState3
                             with
                               (st265, x410)
                             in
                             match p_apply st265 x408 x410 with (st266, x411)
                             in
                             match p_apply st266 x404 x411 with (st267, x412)
                             in
                             match p_apply st267 x399 x412 with (st268, x413)
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
                               (st269, x414)
                             in
                             p_apply st269 x413 x414)
                        x366
  in
  let anon14 = lam x963.
      addi x963 1 in
  recursive
    let rec34 =
      lam i15.
        lam acc16.
          match geqi i15 0 with true
          then
            rec34 (subi i15 1) (cons (anon14 i15) acc16)
          else
            acc16
  in
  let anon15 =
    lam st605.
      lam msg1.
        lam x957.
          lam nodeLabel.
          match mtx3ToSeq st605 msg1 x957 with (st606, x958)
          in
          match
            p_traverseSeq
              st606
              (lam st607.
                 lam x959.
                   (st607, x959))
              x958
          with
            (st608, x960)
          in
          match
            p_map st608 (lam x961.
                 mkCategorical x961) x960
          with
            (st609, x962)
          in
          p_assume st609 (hrmStoreNode nodeLabel x957) x962
  in
  recursive
    let rec8 =
      lam st270.
        lam c27.
          lam s8.
            lam nodeLabel.
            match s8 with [ _,
                _ ] ++ _
            then
              match anon15 st270 c27 (get s8 0) nodeLabel with (st271, x415)
              in
              match splitAt s8 1 with {#label"1" = x416}
              in
              match rec8 st271 c27 x416 nodeLabel with (st272, x417)
              in
              (st272, cons x415 x417)
            else match s8 with [ e13 ]
            then
              match splitAt s8 1 with {#label"1" = x418}
              in
              let slice12 = x418 in
              match anon15 st270 c27 e13 nodeLabel with (st273, x419)
              in
              (st273, [ x419 ])
            else match s8 with ""
            in
            (st270, "")
  in
  let suggestNodeRep =
    lam st604.
      lam msg.
        lam nHosts4.
          lam nodeLabel5.
            let i110 = subi (addi (subi nHosts4 1) 1) 1 in
            rec8
              st604
              msg
              (match geqi i110 0 with true
               then
                 rec34 (subi i110 1) (cons (anon14 i110) "")
               else
                 "")
              nodeLabel5
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
                           lam x420.
                             match ltf x420 finalAge2 with true
                             then
                               p_map
                                 st275
                                 (lam x421.
                                    match eqi x421 finalState11 with true
                                    then
                                      Bridge1
                                        { success = true, events = "" }
                                    else
                                      Bridge1
                                        { success = false, events = "" })
                                 currentState
                             else match
                               p_traverseSeq
                                 st275
                                 (lam st276.
                                    lam x422.
                                      p_traverseSeq
                                        st276
                                        (lam st277.
                                           lam x423.
                                             (st277, x423))
                                        x422)
                                 (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x4010
                                  then
                                    x4010.transitionProbs
                                  else
                                    let #var"145" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 339:16-339:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                    in
                                    map
                                      (lam x424.
                                         map
                                           (lam x425.
                                              p_pure x425)
                                           x424)
                                      (exit 1))
                             with
                               (st278, x426)
                             in
                             match
                               p_map
                                 st278
                                 (lam x427.
                                    lam x428.
                                      mkCategorical (get x427 x428))
                                 x426
                             with
                               (st279, x429)
                             in
                             match
                               p_map
                                 st279
                                 (lam x430.
                                    subi (addi x430 1) 1)
                                 currentState
                             with
                               (st280, x431)
                             in
                             match p_apply st280 x429 x431 with (st281, x432)
                             in
                             match p_assume st281 (hrmStoreBranchState nodeLabel host) x432 with (st282, nextState11)
                             in
                             match
                               p_traverseSeq
                                 st282
                                 (lam st283.
                                    lam x433.
                                      (st283, x433))
                                 (match embeddedQMatrix11 with EmbeddedMarkovChainMatrix1 x3910
                                  then
                                    x3910.totalRates
                                  else
                                    let #var"146" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 343:20-343:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                    in
                                    map
                                      (lam x434.
                                         p_pure x434)
                                      (exit 1))
                             with
                               (st284, x435)
                             in
                             match
                               p_map
                                 st284
                                 (lam x436.
                                    lam x437.
                                      mkExponential
                                        (addf
                                           (addf (get x436 x437) (mulf (int2float host) 0.))
                                           (mulf (int2float nodeLabel) 0.)))
                                 x435
                             with
                               (st285, x438)
                             in
                             match
                               p_map
                                 st285
                                 (lam x439.
                                    subi (addi x439 1) 1)
                                 nextState11
                             with
                               (st286, x440)
                             in
                             match p_apply st286 x438 x440 with (st287, x441)
                             in
                             match p_assume st287 (hrmStoreBranchTime nodeLabel host) x441 with (st288, x442)
                             in
                             match
                               p_map
                                 st288
                                 (lam x443.
                                    subf x420 x443)
                                 x442
                             with
                               (st289, x444)
                             in
                             match
                               sampleHostHistoryRec
                                 st289
                                 nextState11
                                 finalState11
                                 x444
                                 finalAge2
                                 host
                                 nodeLabel
                                 embeddedQMatrix11
                             with
                               (st290, restOfHistory)
                             in
                             match
                               p_map
                                 st290
                                 (lam x445.
                                    lam x446.
                                      Bridge1
                                        { success =
                                            match x445 with Bridge1 x3710
                                            then
                                              x3710.success
                                            else
                                              let #var"147" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 361:18-361:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                              in
                                              exit 1,
                                          events = x446 })
                                 restOfHistory
                             with
                               (st291, x447)
                             in
                             match
                               p_map
                                 st291
                                 (lam x448.
                                    match x448 with Bridge1 x3810
                                    then
                                      x3810.events
                                    else
                                      let #var"148" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 359:10-359:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                      in
                                      exit 1)
                                 restOfHistory
                             with
                               (st292, x449)
                             in
                             match
                               cons11
                                 st292
                                 (Event1
                                    { host = host,
                                      toState = nextState11,
                                      eventTime = x420,
                                      fromState = currentState })
                                 x449
                             with
                               (st293, x450)
                             in
                             p_apply st293 x447 x450)
                        currentAge
    let sampleHostHistoryRec1 =
      lam st294.
        lam currentState1.
          lam finalState12.
            lam currentAge1.
              lam finalAge21.
                lam host1.
                  lam nodeLabel1.
                    lam embeddedQMatrix12.
                      p_bind
                        st294
                        hrmStoreSubmodel
                        (hrmInit {})
                        (lam st295.
                           lam x451.
                             match ltf x451 finalAge21 with true
                             then
                               match
                                 p_map
                                   st295
                                   (lam x452.
                                      lam x453.
                                        match eqi x452 x453 with true
                                        then
                                          Bridge1
                                            { success = true, events = "" }
                                        else
                                          Bridge1
                                            { success = false, events = "" })
                                   currentState1
                               with
                                 (st296, x454)
                               in
                               p_apply st296 x454 finalState12
                             else match
                               p_traverseSeq
                                 st295
                                 (lam st297.
                                    lam x455.
                                      p_traverseSeq
                                        st297
                                        (lam st298.
                                           lam x456.
                                             (st298, x456))
                                        x455)
                                 (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x4011
                                  then
                                    x4011.transitionProbs
                                  else
                                    let #var"149" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 339:16-339:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                                    in
                                    map
                                      (lam x457.
                                         map
                                           (lam x458.
                                              p_pure x458)
                                           x457)
                                      (exit 1))
                             with
                               (st299, x459)
                             in
                             match
                               p_map
                                 st299
                                 (lam x460.
                                    lam x461.
                                      mkCategorical (get x460 x461))
                                 x459
                             with
                               (st300, x462)
                             in
                             match
                               p_map
                                 st300
                                 (lam x463.
                                    subi (addi x463 1) 1)
                                 currentState1
                             with
                               (st301, x464)
                             in
                             match p_apply st301 x462 x464 with (st302, x465)
                             in
                             match p_assume st302 (hrmStoreBranchState nodeLabel1 host1) x465 with (st303, nextState12)
                             in
                             match
                               p_traverseSeq
                                 st303
                                 (lam st304.
                                    lam x466.
                                      (st304, x466))
                                 (match embeddedQMatrix12 with EmbeddedMarkovChainMatrix1 x3911
                                  then
                                    x3911.totalRates
                                  else
                                    let #var"150" =
                                      print
                                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 343:20-343:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                                    in
                                    map
                                      (lam x467.
                                         p_pure x467)
                                      (exit 1))
                             with
                               (st305, x468)
                             in
                             match
                               p_map
                                 st305
                                 (lam x469.
                                    lam x470.
                                      mkExponential
                                        (addf
                                           (addf (get x469 x470) (mulf (int2float host1) 0.))
                                           (mulf (int2float nodeLabel1) 0.)))
                                 x468
                             with
                               (st306, x471)
                             in
                             match
                               p_map
                                 st306
                                 (lam x472.
                                    subi (addi x472 1) 1)
                                 nextState12
                             with
                               (st307, x473)
                             in
                             match p_apply st307 x471 x473 with (st308, x474)
                             in
                             match p_assume st308 (hrmStoreBranchTime nodeLabel1 host1) x474 with (st309, x475)
                             in
                             match
                               p_map
                                 st309
                                 (lam x476.
                                    subf x451 x476)
                                 x475
                             with
                               (st310, x477)
                             in
                             match
                               sampleHostHistoryRec1
                                 st310
                                 nextState12
                                 finalState12
                                 x477
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
                                 (lam x478.
                                    lam x479.
                                      Bridge1
                                        { success =
                                            match x478 with Bridge1 x3711
                                            then
                                              x3711.success
                                            else
                                              let #var"151" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 361:18-361:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                                              in
                                              exit 1,
                                          events = x479 })
                                 restOfHistory1
                             with
                               (st312, x480)
                             in
                             match
                               p_map
                                 st312
                                 (lam x481.
                                    match x481 with Bridge1 x3811
                                    then
                                      x3811.events
                                    else
                                      let #var"152" =
                                        print
                                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 359:10-359:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                                      in
                                      exit 1)
                                 restOfHistory1
                             with
                               (st313, x482)
                             in
                             match
                               cons11
                                 st313
                                 (Event1
                                    { host = host1,
                                      toState = nextState12,
                                      eventTime = x451,
                                      fromState = currentState1 })
                                 x482
                             with
                               (st314, x483)
                             in
                             p_apply st314 x480 x483)
                        currentAge1
  in
  let anon16 = lam x956.
      addi x956 1 in
  recursive
    let rec35 =
      lam i16.
        lam acc17.
          match geqi i16 0 with true
          then
            rec35 (subi i16 1) (cons (anon16 i16) acc17)
          else
            acc17
  in
  let create12 =
    lam l71.
      let i19 = subi l71 1 in
      match geqi i19 0 with true
      then
        rec35 (subi i19 1) (cons (anon16 i19) "")
      else
        ""
  in
  let anon17 =
    lam st592.
      lam startRep1.
        lam finalRep12.
          lam startAge1.
            lam finalAge33.
              lam nodeLabel12.
                lam modelParams31.
                  lam x936.
                    let startState1 = get startRep1 (subi x936 1) in
                    let embeddedQMatrix51 =
                      match modelParams31 with ModelParams1 x1042
                      then
                        x1042.embeddedQMatrix
                      else
                        let #var"1119" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 211:4-211:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st592
                        (lam st593.
                           lam x937.
                             (st593, x937))
                        (match embeddedQMatrix51 with EmbeddedMarkovChainMatrix1 x1082
                         then
                           x1082.totalRates
                         else
                           let #var"1116" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 302:18-302:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x938.
                                p_pure x938)
                             (exit 1))
                    with
                      (st594, x939)
                    in
                    match
                      p_map
                        st594
                        (lam x940.
                           lam x942.
                             mkExponential
                               (addf
                                  (addf (get x940 x942) (mulf (int2float x936) 0.))
                                  (mulf (int2float nodeLabel12) 0.)))
                        x939
                    with
                      (st595, x943)
                    in
                    match
                      p_map
                        st595
                        (lam x944.
                           subi (addi x944 1) 1)
                        startState1
                    with
                      (st596, x945)
                    in
                    match p_apply st596 x943 x945 with (st597, x946)
                    in
                    match p_assume st597 (hrmStoreBranchTime nodeLabel12 x936) x946 with (st598, x947)
                    in
                    match
                      p_map
                        st598
                        (lam x948.
                           subf startAge1 x948)
                        x947
                    with
                      (st599, x949)
                    in
                    match
                      sampleHostHistoryRec
                        st599
                        startState1
                        (get finalRep12 (subi x936 1))
                        x949
                        finalAge33
                        x936
                        nodeLabel12
                        embeddedQMatrix51
                    with
                      (st600, bridge1)
                    in
                    match
                      p_map
                        st600
                        (lam x950.
                           match x950 with Bridge1 x1072
                           then
                             x1072.success
                           else
                             let #var"1117" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 314:19-314:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge1
                    with
                      (st601, x952)
                    in
                    match bool2real st601 x952 with (st602, x953)
                    in
                    let st603 =
                      p_weight
                        st602
                        (hrmStoreBridgeSuppWeight nodeLabel12 x936)
                        (lam x955.
                           externalLog
                             (addf
                                (addf x955 (mulf (int2float x936) 0.))
                                (mulf (int2float nodeLabel12) 0.)))
                        x953
                    in
                    let foo51 = {} in
                    p_map
                      st603
                      (lam x954.
                         match x954 with Bridge1 x1062
                         then
                           x1062.events
                         else
                           let #var"1118" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 315:9-315:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge1
  in
  let anon18 =
    lam st580.
      lam startRep.
        lam finalRep11.
          lam startAge.
            lam finalAge32.
              lam nodeLabel11.
                lam modelParams3.
                  lam x918.
                    let startState = get startRep (subi x918 1) in
                    let embeddedQMatrix5 =
                      match modelParams3 with ModelParams1 x1041
                      then
                        x1041.embeddedQMatrix
                      else
                        let #var"1115" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 211:4-211:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                        in
                        exit 1
                    in
                    match
                      p_traverseSeq
                        st580
                        (lam st581.
                           lam x919.
                             (st581, x919))
                        (match embeddedQMatrix5 with EmbeddedMarkovChainMatrix1 x1081
                         then
                           x1081.totalRates
                         else
                           let #var"1112" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 302:18-302:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                           in
                           map
                             (lam x920.
                                p_pure x920)
                             (exit 1))
                    with
                      (st582, x921)
                    in
                    match
                      p_map
                        st582
                        (lam x922.
                           lam x923.
                             mkExponential
                               (addf
                                  (addf (get x922 x923) (mulf (int2float x918) 0.))
                                  (mulf (int2float nodeLabel11) 0.)))
                        x921
                    with
                      (st583, x924)
                    in
                    match
                      p_map
                        st583
                        (lam x925.
                           subi (addi x925 1) 1)
                        startState
                    with
                      (st584, x926)
                    in
                    match p_apply st584 x924 x926 with (st585, x927)
                    in
                    match p_assume st585 (hrmStoreBranchTime nodeLabel11 x918) x927 with (st586, x928)
                    in
                    match
                      p_map
                        st586
                        (lam x929.
                           subf startAge x929)
                        x928
                    with
                      (st587, x930)
                    in
                    match
                      sampleHostHistoryRec1
                        st587
                        startState
                        (get finalRep11 (subi x918 1))
                        x930
                        finalAge32
                        x918
                        nodeLabel11
                        embeddedQMatrix5
                    with
                      (st588, bridge)
                    in
                    match
                      p_map
                        st588
                        (lam x931.
                           match x931 with Bridge1 x1071
                           then
                             x1071.success
                           else
                             let #var"1113" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 314:19-314:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                             in
                             exit 1)
                        bridge
                    with
                      (st589, x932)
                    in
                    match bool2real st589 x932 with (st590, x933)
                    in
                    let st591 =
                      p_weight
                        st590
                        (hrmStoreBridgeSuppWeight nodeLabel11 x918)
                        (lam x935.
                           externalLog
                             (addf
                                (addf x935 (mulf (int2float x918) 0.))
                                (mulf (int2float nodeLabel11) 0.)))
                        x933
                    in
                    let foo5 = {} in
                    p_map
                      st591
                      (lam x934.
                         match x934 with Bridge1 x1061
                         then
                           x1061.events
                         else
                           let #var"1114" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 315:9-315:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                           in
                           exit 1)
                      bridge
  in
  recursive
    let rec9 =
      lam st315.
        lam c28.
          lam c29.
            lam c30.
              lam c31.
                lam c32.
                  lam c33.
                    lam s9.
                      match s9 with [ _,
                          _ ] ++ _
                      then
                        match anon17 st315 c28 c29 c30 c31 c32 c33 (get s9 0) with (st316, x484)
                        in
                        match splitAt s9 1 with {#label"1" = x485}
                        in
                        match rec9 st316 c28 c29 c30 c31 c32 c33 x485 with (st317, x486)
                        in
                        (st317, cons x484 x486)
                      else match s9 with [ e14 ]
                      then
                        match splitAt s9 1 with {#label"1" = x487}
                        in
                        let slice13 = x487 in
                        match anon17 st315 c28 c29 c30 c31 c32 c33 e14 with (st318, x488)
                        in
                        (st318, [ x488 ])
                      else match s9 with ""
                      in
                      (st315, "")
    let rec10 =
      lam st319.
        lam c34.
          lam c35.
            lam c36.
              lam c37.
                lam c38.
                  lam c39.
                    lam s10.
                      match s10 with [ _,
                          _ ] ++ _
                      then
                        match
                          anon18 st319 c34 c35 c36 c37 c38 c39 (get s10 0)
                        with
                          (st320, x489)
                        in
                        match splitAt s10 1 with {#label"1" = x490}
                        in
                        match rec10 st320 c34 c35 c36 c37 c38 c39 x490 with (st321, x491)
                        in
                        (st321, cons x489 x491)
                      else match s10 with [ e15 ]
                      then
                        match splitAt s10 1 with {#label"1" = x492}
                        in
                        let slice14 = x492 in
                        match anon18 st319 c34 c35 c36 c37 c38 c39 e15 with (st322, x493)
                        in
                        (st322, [ x493 ])
                      else match s10 with ""
                      in
                      (st319, "")
  in
  let anon19 =
    lam h2.
      lam x917.
        lti
          (match
             isNaN1
               (match h2 with Event1 x1091
                then
                  x1091.eventTime
                else
                  let #var"1107" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 251:12-251:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
                  in
                  exit 1)
           with
             true
           then
             negi 1
           else match
             isNaN1
               (match x917 with Event1 x1131
                then
                  x1131.eventTime
                else
                  let #var"1108" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 254:12-254:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
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
                  let #var"1109" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 257:6-257:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
                  in
                  exit 1)
               (match x917 with Event1 x1151
                then
                  x1151.eventTime
                else
                  let #var"1111" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 257:25-257:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
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
      lam c40.
        lam l.
          lam r.
            lam seq1.
              match seq1 with [ _ ] ++ _
              then
                let s41 = get seq1 0 in
                match splitAt seq1 1 with {#label"1" = x494}
                in
                let seq2 = x494 in
                match anon19 c40 s41 with true
                then
                  work11 c40 (cons s41 l) r seq2
                else
                  work11 c40 l (cons s41 r) seq2
              else match seq1 with ""
              in
              (l, r)
    let work12 =
      lam c41.
        lam l1.
          lam r1.
            lam seq11.
              match seq11 with [ _ ] ++ _
              then
                let s42 = get seq11 0 in
                match splitAt seq11 1 with {#label"1" = x495}
                in
                let seq21 = x495 in
                match anon19 c41 s42 with true
                then
                  work12 c41 (cons s42 l1) r1 seq21
                else
                  work11 c41 l1 (cons s42 r1) seq21
              else match seq11 with ""
              in
              (l1, r1)
    let work13 =
      lam c42.
        lam l2.
          lam r2.
            lam seq12.
              match seq12 with [ _ ] ++ _
              then
                let s43 = get seq12 0 in
                match splitAt seq12 1 with {#label"1" = x496}
                in
                let seq22 = x496 in
                match anon19 c42 s43 with true
                then
                  work11 c42 (cons s43 l2) r2 seq22
                else
                  work13 c42 l2 (cons s43 r2) seq22
              else match seq12 with ""
              in
              (l2, r2)
    let work14 =
      lam c43.
        lam l3.
          lam r3.
            lam seq13.
              match seq13 with [ _ ] ++ _
              then
                let s44 = get seq13 0 in
                match splitAt seq13 1 with {#label"1" = x497}
                in
                let seq23 = x497 in
                match anon19 c43 s44 with true
                then
                  work12 c43 (cons s44 l3) r3 seq23
                else
                  work13 c43 l3 (cons s44 r3) seq23
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
      lam st323.
        lam seq31.
          p_map
            st323
            (lam x498.
               match null x498 with true
               then
                 x498
               else
                 let h1 = head x498 in
                 let lr1 = work14 h1 "" "" (reverse (tail x498)) in
                 match lr1 with (#var"X6",)
                 in
                 match lr1 with {#label"1" = #var"X7"}
                 in
                 concat (quickSort #var"X6") (cons h1 (quickSort #var"X7")))
            seq31
  in
  recursive
    let rec212 =
      lam st324.
        lam c44.
          lam c45.
            lam c46.
              lam c47.
                lam c48.
                  lam c49.
                    lam acc18.
                      lam s213.
                        match s213 with [ _ ] ++ _
                        then
                          let x499 = get s213 0 in
                          match
                            p_map
                              st324
                              (lam x500.
                                 lam x501.
                                   addf x500 x501)
                              acc18
                          with
                            (st325, x502)
                          in
                          match
                            hostIndepLikelihood
                              st325
                              1
                              (get c44 (subi x499 1))
                              (get c45 (subi x499 1))
                              c46
                              c47
                              (get c49 (subi x499 1))
                              (match c48 with ModelParams1 x1191
                               then
                                 x1191.embeddedQMatrix
                               else
                                 let #var"153" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st326, x503)
                          in
                          match p_apply st326 x502 x503 with (st327, x504)
                          in
                          match splitAt s213 1 with {#label"1" = x505}
                          in
                          rec212 st327 c44 c45 c46 c47 c48 c49 x504 x505
                        else match s213 with ""
                        in
                        (st324, acc18)
    let rec213 =
      lam st328.
        lam c50.
          lam c51.
            lam c52.
              lam c53.
                lam c54.
                  lam c55.
                    lam acc19.
                      lam s214.
                        match s214 with [ _ ] ++ _
                        then
                          let x506 = get s214 0 in
                          match
                            p_map
                              st328
                              (lam x507.
                                 lam x508.
                                   addf x507 x508)
                              acc19
                          with
                            (st329, x509)
                          in
                          match
                            hostIndepLikelihood2
                              st329
                              1
                              (get c50 (subi x506 1))
                              (get c51 (subi x506 1))
                              c52
                              c53
                              (get c55 (subi x506 1))
                              (match c54 with ModelParams1 x1192
                               then
                                 x1192.embeddedQMatrix
                               else
                                 let #var"154" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                 in
                                 exit 1)
                          with
                            (st330, x510)
                          in
                          match p_apply st330 x509 x510 with (st331, x511)
                          in
                          match splitAt s214 1 with {#label"1" = x512}
                          in
                          rec213 st331 c50 c51 c52 c53 c54 c55 x511 x512
                        else match s214 with ""
                        in
                        (st328, acc19)
  in
  let anon20 = lam x916.
      addi x916 1 in
  recursive
    let rec36 =
      lam i17.
        lam acc110.
          match geqi i17 0 with true
          then
            rec36 (subi i17 1) (cons (anon20 i17) acc110)
          else
            acc110
  in
  let create13 =
    lam l7.
      let i18 = subi l7 1 in
      match geqi i18 0 with true
      then
        rec36 (subi i18 1) (cons (anon20 i18) "")
      else
        ""
  in
  recursive
    let rec214 =
      lam st332.
        lam acc20.
          lam s215.
            match s215 with [ _ ] ++ _
            then
              match
                p_map
                  st332
                  (lam x513.
                     lam x514.
                       addf x513 x514)
                  acc20
              with
                (st333, x515)
              in
              match p_apply st333 x515 (get s215 0) with (st334, x516)
              in
              match splitAt s215 1 with {#label"1" = x517}
              in
              rec214 st334 x516 x517
            else match s215 with ""
            in
            (st332, acc20)
  in
  let fold2 =
    lam st578.
      lam init11.
        lam seq51.
          match seq51 with [ _ ] ++ _
          then
            match
              p_map
                st578
                (lam x913.
                   addf init11 x913)
                (get seq51 0)
            with
              (st579, x914)
            in
            match splitAt seq51 1 with {#label"1" = x915}
            in
            rec214 st579 x914 x915
          else match seq51 with ""
          in
          (st578, p_pure init11)
  in
  recursive
    let rec215 =
      lam st335.
        lam c56.
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
                        st335
                        (lam x518.
                           addi x518 1)
                        (get field3 0)
                    with
                      (st336, x519)
                    in
                    match mtxGet2 st336 x519 (addi (get s216 0) 1) c56 with (st337, x520)
                    in
                    match log11 st337 x520 with (st338, x521)
                    in
                    match splitAt field3 1 with {#label"1" = x522}
                    in
                    (st338, (snoc field2 x521, x522))
                  else
                    let x523 = error "foldl2: Cannot happen!" in
                    match x523 with (x524,)
                    in
                    match x523 with {#label"1" = x525}
                    in
                    (st335, (map (lam x526.
                         p_pure x526) x524, map (lam x527.
                         p_pure x527) x525))
                with
                  (st339, x528)
                in
                match splitAt s216 1 with {#label"1" = x529}
                in
                rec215 st339 c56 x528 x529
              else match s216 with ""
              in
              (st335, acc23)
    let rec216 =
      lam st340.
        lam c57.
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
                        st340
                        (lam x530.
                           addi x530 1)
                        (get field5 0)
                    with
                      (st341, x531)
                    in
                    match
                      p_map
                        st341
                        (lam x532.
                           addi x532 1)
                        (get s217 0)
                    with
                      (st342, x533)
                    in
                    match mtxGet4 st342 x531 x533 c57 with (st343, x534)
                    in
                    match log11 st343 x534 with (st344, x535)
                    in
                    match splitAt field5 1 with {#label"1" = x536}
                    in
                    (st344, (snoc field4 x535, x536))
                  else
                    let x537 = error "foldl2: Cannot happen!" in
                    match x537 with (x538,)
                    in
                    match x537 with {#label"1" = x539}
                    in
                    (st340, (map (lam x540.
                         p_pure x540) x538, map (lam x541.
                         p_pure x541) x539))
                with
                  (st345, x542)
                in
                match splitAt s217 1 with {#label"1" = x543}
                in
                rec216 st345 c57 x542 x543
              else match s217 with ""
              in
              (st340, acc24)
  in
  recursive
    let rec217 =
      lam st346.
        lam c58.
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
                        st346
                        (lam x544.
                           addi x544 1)
                        (get s218 0)
                    with
                      (st347, x545)
                    in
                    match mtxGet2 st347 x545 (addi (get field7 0) 1) c58 with (st348, x546)
                    in
                    match log11 st348 x546 with (st349, x547)
                    in
                    match splitAt field7 1 with {#label"1" = x548}
                    in
                    (st349, (snoc field6 x547, x548))
                  else
                    let x549 = error "foldl2: Cannot happen!" in
                    match x549 with (x550,)
                    in
                    match x549 with {#label"1" = x551}
                    in
                    (st346, (map (lam x552.
                         p_pure x552) x550, x551))
                with
                  (st350, x553)
                in
                match splitAt s218 1 with {#label"1" = x554}
                in
                rec217 st350 c58 x553 x554
              else match s218 with ""
              in
              (st346, acc25)
    let rec218 =
      lam st351.
        lam c59.
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
                        st351
                        (lam x555.
                           addi x555 1)
                        (get s219 0)
                    with
                      (st352, x556)
                    in
                    match
                      p_map
                        st352
                        (lam x557.
                           addi x557 1)
                        (get field9 0)
                    with
                      (st353, x558)
                    in
                    match mtxGet4 st353 x556 x558 c59 with (st354, x559)
                    in
                    match log11 st354 x559 with (st355, x560)
                    in
                    match splitAt field9 1 with {#label"1" = x561}
                    in
                    (st355, (snoc field8 x560, x561))
                  else
                    let x562 = error "foldl2: Cannot happen!" in
                    match x562 with (x563,)
                    in
                    match x562 with {#label"1" = x564}
                    in
                    (st351, (map (lam x565.
                         p_pure x565) x563, map (lam x566.
                         p_pure x566) x564))
                with
                  (st356, x567)
                in
                match splitAt s219 1 with {#label"1" = x568}
                in
                rec218 st356 c59 x567 x568
              else match s219 with ""
              in
              (st351, acc26)
  in
  recursive
    let sampleTreeHistory =
      lam st357.
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
                            let #var"168" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 124:14-124:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 130:6-130:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                            in
                            exit 1
                        in
                        match
                          rec9
                            st357
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
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 132:6-132:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                               in
                               exit 1)
                            modelParams11
                            (create12 (addi (subi nHosts 1) 1))
                        with
                          (st358, unorderedBranch)
                        in
                        match paste0 st358 unorderedBranch with (st359, x569)
                        in
                        match quickSort1 st359 x569 with (st360, orderedEvents)
                        in
                        match length13 st360 orderedEvents with (st361, nEvents4)
                        in
                        match
                          allTimesValidBranch st361 parentRep orderedEvents 1 nEvents4 nHosts
                        with
                          (st362, x570)
                        in
                        match
                          p_bind
                            st362
                            hrmStoreSubmodel
                            (hrmInit {})
                            (lam st363.
                               lam x571.
                                 match
                                   match x571 with true
                                   then
                                     let s220 = create13 (addi (subi (length11 unorderedBranch) 1) 1)
                                     in
                                     match
                                       match s220 with [ _ ] ++ _
                                       then
                                         let x572 = get s220 0 in
                                         match
                                           hostIndepLikelihood
                                             st363
                                             1
                                             (get parentRep (subi x572 1))
                                             (get rep1 (subi x572 1))
                                             parentAge
                                             finalAge3
                                             (get unorderedBranch (subi x572 1))
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
                                           (st364, x573)
                                         in
                                         match
                                           p_map
                                             st364
                                             (lam x574.
                                                addf 0. x574)
                                             x573
                                         with
                                           (st365, x575)
                                         in
                                         match splitAt s220 1 with {#label"1" = x576}
                                         in
                                         rec212
                                           st365
                                           parentRep
                                           rep1
                                           parentAge
                                           finalAge3
                                           modelParams11
                                           unorderedBranch
                                           x575
                                           x576
                                       else match s220 with ""
                                       in
                                       (st363, p_pure 0.)
                                     with
                                       (st366, x577)
                                     in
                                     match
                                       p_map
                                         st366
                                         (lam x578.
                                            lam x579.
                                              subf x578 x579)
                                         x577
                                     with
                                       (st367, x580)
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
                                                     st367
                                                     (lam x581.
                                                        addi x581 1)
                                                     (get field11 0)
                                                 with
                                                   (st368, x582)
                                                 in
                                                 match
                                                   mtxGet2 st368 x582 (addi (get rep1 0) 1) branchKernel
                                                 with
                                                   (st369, x583)
                                                 in
                                                 match log11 st369 x583 with (st370, x584)
                                                 in
                                                 match splitAt field11 1 with {#label"1" = x585}
                                                 in
                                                 (st370, (snoc field10 x584, x585))
                                               else
                                                 let x586 = error "foldl2: Cannot happen!" in
                                                 match x586 with (x587,)
                                                 in
                                                 match x586 with {#label"1" = x588}
                                                 in
                                                 (st367, (map
                                                   (lam x589.
                                                      p_pure x589)
                                                   x587, map
                                                   (lam x590.
                                                      p_pure x590)
                                                   x588))
                                             with
                                               (st371, x591)
                                             in
                                             match splitAt rep1 1 with {#label"1" = x592}
                                             in
                                             rec215 st371 branchKernel x591 x592
                                           else match rep1 with ""
                                           in
                                           (st367, acc27)
                                         with
                                           (st372, x593)
                                         in
                                         match x593 with (field12, field13)
                                         in
                                         (st372, field12)
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
                                                     st367
                                                     (lam x594.
                                                        addi x594 1)
                                                     (get parentRep 0)
                                                 with
                                                   (st373, x595)
                                                 in
                                                 match
                                                   mtxGet2 st373 x595 (addi (get field15 0) 1) branchKernel
                                                 with
                                                   (st374, x596)
                                                 in
                                                 match log11 st374 x596 with (st375, x597)
                                                 in
                                                 match splitAt field15 1 with {#label"1" = x598}
                                                 in
                                                 (st375, (snoc field14 x597, x598))
                                               else
                                                 let x599 = error "foldl2: Cannot happen!" in
                                                 match x599 with (x600,)
                                                 in
                                                 match x599 with {#label"1" = x601}
                                                 in
                                                 (st367, (map
                                                   (lam x602.
                                                      p_pure x602)
                                                   x600, x601))
                                             with
                                               (st376, x603)
                                             in
                                             match splitAt parentRep 1 with {#label"1" = x604}
                                             in
                                             rec217 st376 branchKernel x603 x604
                                           else match parentRep with ""
                                           in
                                           (st367, acc28)
                                         with
                                           (st377, x605)
                                         in
                                         match x605 with (field16, field17)
                                         in
                                         (st377, field16)
                                     with
                                       (st378, x606)
                                     in
                                     match fold2 st378 0. x606 with (st379, x607)
                                     in
                                     match p_apply st379 x580 x607 with (st380, x608)
                                     in
                                     match
                                       p_bind
                                         st380
                                         hrmStoreSubmodel
                                         (hrmInit {})
                                         (lam st381.
                                            lam x609.
                                              match gti 1 x609 with true
                                              then
                                                match
                                                  getTotalRate st381 parentRep modelParams11 nHosts
                                                with
                                                  (st382, x610)
                                                in
                                                p_map
                                                  st382
                                                  (lam x611.
                                                     mulf (negf (subf parentAge finalAge3)) x611)
                                                  x610
                                              else match
                                                p_map
                                                  st381
                                                  (lam x612.
                                                     get x612 (subi 1 1))
                                                  orderedEvents
                                              with
                                                (st383, nextEvent2)
                                              in
                                              match
                                                p_map
                                                  st383
                                                  (lam x613.
                                                     match x613 with Event1 x3110
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
                                                (st384, newAge2)
                                              in
                                              match
                                                getTotalRate st384 parentRep modelParams11 nHosts
                                              with
                                                (st385, totalLeavingRate12)
                                              in
                                              match p_traverseSeq st385 (lam st. lam e. (st, e)) parentRep with (st385, liftedRep) in
                                              match p_map st385 (lam rep. printLn (strJoin "," (map int2string rep))) liftedRep with (st385, _) in
                                              match p_map st385 (lam e. lam rep. match e with Event1 e in printLn (join ["8155:From state", int2string e.fromState, " to state ", int2string e.toState, "rep from state: ", int2string (e.host)])) nextEvent2 with (st385, printer) in
                                              match p_map st385 (lam e. lam rep. match e with Event1 e in printLn (join ["8158:From state", int2string e.fromState, " to state ", int2string e.toState, "rep from state: ", int2string (get rep (subi e.host 1))])) nextEvent3 with (st385, printer) in
                                              match p_apply st385 printer liftedRep with (st385, _) in
                                              match
                                                p_map
                                                  st385
                                                  (lam x614.
                                                     match x614 with Event1 x1323
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
                                                (st386, hostIndex12)
                                              in
                                              match
                                                p_map
                                                  st386
                                                  (lam x615.
                                                     lam x616.
                                                       lam st387.
                                                         match
                                                           gti
                                                             (match x615 with Event1 x1303
                                                              then
                                                                x1303.fromState
                                                              else
                                                                let #var"159" =
                                                                  print
                                                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                                in
                                                                exit 1)
                                                             x616
                                                         with
                                                           true
                                                         then
                                                           getLossRate2 st387 parentRep hostIndex12 modelParams11
                                                         else
                                                           getGainRate2 st387 parentRep hostIndex12 modelParams11)
                                                  nextEvent2
                                              with
                                                (st388, x617)
                                              in
                                              match
                                                p_map
                                                  st388
                                                  (lam x618.
                                                     match x618 with Event1 x1313
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
                                                (st389, x619)
                                              in
                                              match
                                                p_subApply st389 hrmStoreSubmodel (hrmInit {}) x617 x619
                                              with
                                                (st390, x620)
                                              in
                                              match p_join st390 x620 with (st391, x621)
                                              in
                                              match
                                                p_map
                                                  st391
                                                  (lam x622.
                                                     lam x623.
                                                       divf x622 x623)
                                                  x621
                                              with
                                                (st392, x624)
                                              in
                                              match p_apply st392 x624 totalLeavingRate12 with (st393, x625)
                                              in
                                              match log11 st393 x625 with (st394, x626)
                                              in
                                              match
                                                p_map
                                                  st394
                                                  (lam x627.
                                                     lam x628.
                                                       lam x629.
                                                         addf (subf x627 x628) x629)
                                                  x626
                                              with
                                                (st395, x630)
                                              in
                                              match
                                                p_map
                                                  st395
                                                  (lam x631.
                                                     lam x632.
                                                       mulf (subf parentAge x631) x632)
                                                  newAge2
                                              with
                                                (st396, x633)
                                              in
                                              match p_apply st396 x633 totalLeavingRate12 with (st397, x634)
                                              in
                                              match p_apply st397 x630 x634 with (st398, x635)
                                              in
                                              match
                                                updateRepertoire st398 parentRep nextEvent2 nHosts
                                              with
                                                (st399, x636)
                                              in
                                              match
                                                fullModelWeight
                                                  st399
                                                  (addi 1 1)
                                                  x636
                                                  rep1
                                                  newAge2
                                                  finalAge3
                                                  orderedEvents
                                                  x609
                                                  nHosts
                                                  modelParams11
                                              with
                                                (st400, x637)
                                              in
                                              p_apply st400 x635 x637)
                                         nEvents4
                                     with
                                       (st401, x638)
                                     in
                                     (st401, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = x608,
                                         logModelDensity = x638,
                                         success = true })
                                   else
                                     (st363, CorrectedBranchSample1
                                       { history = orderedEvents,
                                         logSamplingDensity = p_pure (log1 0.),
                                         logModelDensity = p_pure (log1 0.),
                                         success = false })
                                 with
                                   (st402, x639)
                                 in
                                 match x639 with CorrectedBranchSample1 x640
                                 in
                                 match x640 with {history = x641}
                                 in
                                 match
                                   p_map
                                     st402
                                     (lam x642.
                                        lam x643.
                                          lam x644.
                                            match x640 with {success = x645}
                                            in
                                            CorrectedBranchSample1
                                              { history = x642,
                                                logSamplingDensity = x643,
                                                logModelDensity = x644,
                                                success = x645 })
                                     x641
                                 with
                                   (st403, x646)
                                 in
                                 match x640 with {logSamplingDensity = x647}
                                 in
                                 match p_apply st403 x646 x647 with (st404, x648)
                                 in
                                 match x640 with {logModelDensity = x649}
                                 in
                                 p_apply st404 x648 x649)
                            x570
                        with
                          (st405, branchSample)
                        in
                        match
                          p_map
                            st405
                            (lam x650.
                               lam x651.
                                 mulf
                                   (subf
                                      (match x650 with CorrectedBranchSample1 x4610
                                       then
                                         x4610.logModelDensity
                                       else
                                         let #var"161" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 138:15-138:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x651)
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
                                               let #var"162" =
                                                 print
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 138:90-138:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1))
                                         0.)))
                            branchSample
                        with
                          (st406, x652)
                        in
                        match
                          p_map
                            st406
                            (lam x653.
                               match x653 with CorrectedBranchSample1 x4710
                               then
                                 x4710.logSamplingDensity
                               else
                                 let #var"163" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 138:46-138:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st407, x654)
                        in
                        match p_apply st407 x652 x654 with (st408, x655)
                        in
                        let nl = (match tree2 with MsgLeaf carried26
                                             then
                                               carried26.label
                                             else match tree2 with MsgNode carried27
                                             then
                                               carried27.label
                                             else
                                               let #var"162" =
                                                 print
                                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 138:90-138:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                               in
                                               exit 1) in
                        let st409 =
                          p_weight
                            st408
                            (hrmStoreLikrWeight nl)
                            (/-temp-/lam x658.
                               x658)
                            x655
                        in
                        let foo = {} in
                        match
                          p_map
                            st409
                            (lam x656.
                               match x656 with CorrectedBranchSample1 x4510
                               then
                                 x4510.history
                               else
                                 let #var"164" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 144:16-144:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                                 in
                                 exit 1)
                            branchSample
                        with
                          (st410, x657)
                        in
                        (st410, HistoryLeaf
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
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 141:12-141:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 142:14-142:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                                in
                                exit 1,
                            history = x657,
                            repertoire = rep1 })
                      else match
                        mtxElemMul
                          st357
                          (match tree2 with MsgLeaf carried34
                           then
                             match carried34 with {outMsg = #var"X8"}
                             in
                             p_pure #var"X8"
                           else match tree2 with MsgNode carried35
                           then
                             carried35.outMsg
                           else
                             let #var"169" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 147:34-147:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                             in
                             p_pure (exit 1))
                          preorderMsg
                      with
                        (st411, samplingProb)
                      in
                      match
                        suggestNodeRep
                          st411
                          samplingProb
                          nHosts
                          (match tree2 with MsgLeaf carried36
                           then
                             carried36.label
                           else match tree2 with MsgNode carried37
                           then
                             carried37.label
                           else
                             let #var"170" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 148:51-148:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                             in
                             exit 1)
                      with
                        (st412, rep2)
                      in
                      match any1 st412 rep2 with (st413, x659)
                      in
                      match bool2real st413 x659 with (st414, x660)
                      in
                      let nl = (match tree2 with MsgLeaf carried52
                                         then
                                           carried52.label
                                         else match tree2 with MsgNode carried53
                                         then
                                           carried53.label
                                         else
                                           let #var"192" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 150:43-150:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1) in
                      let st415 =
                        p_weight
                          st414
                          (hrmStoreNodeSuppWeight nl)
                          (lam x767.
                             externalLog
                               (addf
                                  x767
                                  (mulf
                                     (int2float
                                        (match tree2 with MsgLeaf carried52
                                         then
                                           carried52.label
                                         else match tree2 with MsgNode carried53
                                         then
                                           carried53.label
                                         else
                                           let #var"192" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 150:43-150:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                           in
                                           exit 1))
                                     0.)))
                          x660
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
                          let #var"191" =
                            print
                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 158:6-158:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                          in
                          exit 1
                      in
                      match
                        rec10
                          st415
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
                             let #var"171" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 160:6-160:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                             in
                             exit 1)
                          modelParams11
                          (create12 (addi (subi nHosts 1) 1))
                      with
                        (st416, unorderedBranch1)
                      in
                      match paste0 st416 unorderedBranch1 with (st417, x661)
                      in
                      match quickSort1 st417 x661 with (st418, orderedEvents1)
                      in
                      match length13 st418 orderedEvents1 with (st419, nEvents41)
                      in
                      match
                        allTimesValidBranch st419 parentRep orderedEvents1 1 nEvents41 nHosts
                      with
                        (st420, x662)
                      in
                      match
                        p_bind
                          st420
                          hrmStoreSubmodel
                          (hrmInit {})
                          (lam st421.
                             lam x663.
                               match
                                 match x663 with true
                                 then
                                   let s221 = create13 (addi (subi (length11 unorderedBranch1) 1) 1)
                                   in
                                   match
                                     match s221 with [ _ ] ++ _
                                     then
                                       let x664 = get s221 0 in
                                       match
                                         hostIndepLikelihood2
                                           st421
                                           1
                                           (get parentRep (subi x664 1))
                                           (get rep2 (subi x664 1))
                                           parentAge
                                           finalAge31
                                           (get unorderedBranch1 (subi x664 1))
                                           (match modelParams11 with ModelParams1 x1194
                                            then
                                              x1194.embeddedQMatrix
                                            else
                                              let #var"172" =
                                                print
                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                                              in
                                              exit 1)
                                       with
                                         (st422, x665)
                                       in
                                       match
                                         p_map
                                           st422
                                           (lam x666.
                                              addf 0. x666)
                                           x665
                                       with
                                         (st423, x667)
                                       in
                                       match splitAt s221 1 with {#label"1" = x668}
                                       in
                                       rec213
                                         st423
                                         parentRep
                                         rep2
                                         parentAge
                                         finalAge31
                                         modelParams11
                                         unorderedBranch1
                                         x667
                                         x668
                                     else match s221 with ""
                                     in
                                     (st421, p_pure 0.)
                                   with
                                     (st424, x669)
                                   in
                                   match
                                     p_map
                                       st424
                                       (lam x670.
                                          lam x671.
                                            subf x670 x671)
                                       x669
                                   with
                                     (st425, x672)
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
                                                   st425
                                                   (lam x673.
                                                      addi x673 1)
                                                   (get field19 0)
                                               with
                                                 (st426, x674)
                                               in
                                               match
                                                 p_map
                                                   st426
                                                   (lam x675.
                                                      addi x675 1)
                                                   (get rep2 0)
                                               with
                                                 (st427, x676)
                                               in
                                               match mtxGet4 st427 x674 x676 branchKernel with (st428, x677)
                                               in
                                               match log11 st428 x677 with (st429, x678)
                                               in
                                               match splitAt field19 1 with {#label"1" = x679}
                                               in
                                               (st429, (snoc field18 x678, x679))
                                             else
                                               let x680 = error "foldl2: Cannot happen!" in
                                               match x680 with (x681,)
                                               in
                                               match x680 with {#label"1" = x682}
                                               in
                                               (st425, (map
                                                 (lam x683.
                                                    p_pure x683)
                                                 x681, map
                                                 (lam x684.
                                                    p_pure x684)
                                                 x682))
                                           with
                                             (st430, x685)
                                           in
                                           match splitAt rep2 1 with {#label"1" = x686}
                                           in
                                           rec216 st430 branchKernel x685 x686
                                         else match rep2 with ""
                                         in
                                         (st425, acc29)
                                       with
                                         (st431, x687)
                                       in
                                       match x687 with (field20, field21)
                                       in
                                       (st431, field20)
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
                                                   st425
                                                   (lam x688.
                                                      addi x688 1)
                                                   (get parentRep 0)
                                               with
                                                 (st432, x689)
                                               in
                                               match
                                                 p_map
                                                   st432
                                                   (lam x690.
                                                      addi x690 1)
                                                   (get field23 0)
                                               with
                                                 (st433, x691)
                                               in
                                               match mtxGet4 st433 x689 x691 branchKernel with (st434, x692)
                                               in
                                               match log11 st434 x692 with (st435, x693)
                                               in
                                               match splitAt field23 1 with {#label"1" = x694}
                                               in
                                               (st435, (snoc field22 x693, x694))
                                             else
                                               let x695 = error "foldl2: Cannot happen!" in
                                               match x695 with (x696,)
                                               in
                                               match x695 with {#label"1" = x697}
                                               in
                                               (st425, (map
                                                 (lam x698.
                                                    p_pure x698)
                                                 x696, map
                                                 (lam x699.
                                                    p_pure x699)
                                                 x697))
                                           with
                                             (st436, x700)
                                           in
                                           match splitAt parentRep 1 with {#label"1" = x701}
                                           in
                                           rec218 st436 branchKernel x700 x701
                                         else match parentRep with ""
                                         in
                                         (st425, acc30)
                                       with
                                         (st437, x702)
                                       in
                                       match x702 with (field24, field25)
                                       in
                                       (st437, field24)
                                   with
                                     (st438, x703)
                                   in
                                   match fold2 st438 0. x703 with (st439, x704)
                                   in
                                   match p_apply st439 x672 x704 with (st440, x705)
                                   in
                                   match
                                     p_bind
                                       st440
                                       hrmStoreSubmodel
                                       (hrmInit {})
                                       (lam st441.
                                          lam x706.
                                            match gti 1 x706 with true
                                            then
                                              match
                                                getTotalRate st441 parentRep modelParams11 nHosts
                                              with
                                                (st442, x707)
                                              in
                                              p_map
                                                st442
                                                (lam x708.
                                                   mulf (negf (subf parentAge finalAge31)) x708)
                                                x707
                                            else match
                                              p_map
                                                st441
                                                (lam x709.
                                                   get x709 (subi 1 1))
                                                orderedEvents1
                                            with
                                              (st443, nextEvent3)
                                            in
                                            match
                                              p_map
                                                st443
                                                (lam x710.
                                                   match x710 with Event1 x3111
                                                   then
                                                     x3111.eventTime
                                                   else
                                                     let #var"173" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st444, newAge3)
                                            in
                                            match
                                              getTotalRate st444 parentRep modelParams11 nHosts
                                            with
                                              (st445, totalLeavingRate13)
                                            in
                                            -- match p_map st445 (lam e. match e with Event1 e in get parentRep e.host) nextEvent3 with (st445, repState) in
                                            match p_traverseSeq st445 (lam st. lam e. (st, e)) parentRep with (st445, liftedRep) in
                                            match p_map st445 (lam rep. printLn (strJoin "," (map int2string rep))) liftedRep with (st445, _) in
                                            match p_map st445 (lam e. lam rep. match e with Event1 e in printLn (join ["8849From state", int2string e.fromState, " to state ", int2string e.toState, "rep from state: ", int2string (get rep (subi e.host 1))])) nextEvent3 with (st445, printer) in
                                            match p_apply st445 printer liftedRep with (st445, _) in
                                            -- match p_apply st445 printer repState with (st445, _) in
                                            match
                                              p_map
                                                st445
                                                (lam x711.
                                                   match x711 with Event1 x1324
                                                   then
                                                     x1324.host
                                                   else
                                                     let #var"174" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st446, hostIndex13)
                                            in
                                            match
                                              p_map
                                                st446
                                                (lam x712.
                                                   lam x713.
                                                     lam st447.
                                                       match
                                                         gti
                                                           (match x712 with Event1 x1304
                                                            then
                                                              x1304.fromState
                                                            else
                                                              let #var"175" =
                                                                print
                                                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
                                                              in
                                                              exit 1)
                                                           x713
                                                       with
                                                         true
                                                       then
                                                         getLossRate2 st447 parentRep hostIndex13 modelParams11
                                                       else
                                                         getGainRate2 st447 parentRep hostIndex13 modelParams11)
                                                nextEvent3
                                            with
                                              (st448, x714)
                                            in
                                            match
                                              p_map
                                                st448
                                                (lam x715.
                                                   match x715 with Event1 x1314
                                                   then
                                                     x1314.toState
                                                   else
                                                     let #var"176" =
                                                       print
                                                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
                                                     in
                                                     exit 1)
                                                nextEvent3
                                            with
                                              (st449, x716)
                                            in
                                            match
                                              p_subApply st449 hrmStoreSubmodel (hrmInit {}) x714 x716
                                            with
                                              (st450, x717)
                                            in
                                            match p_join st450 x717 with (st451, x718)
                                            in
                                            match
                                              p_map
                                                st451
                                                (lam x719.
                                                   lam x720.
                                                     divf x719 x720)
                                                x718
                                            with
                                              (st452, x721)
                                            in
                                            match p_apply st452 x721 totalLeavingRate13 with (st453, x722)
                                            in
                                            match log11 st453 x722 with (st454, x723)
                                            in
                                            match
                                              p_map
                                                st454
                                                (lam x724.
                                                   lam x725.
                                                     lam x726.
                                                       addf (subf x724 x725) x726)
                                                x723
                                            with
                                              (st455, x727)
                                            in
                                            match
                                              p_map
                                                st455
                                                (lam x728.
                                                   lam x729.
                                                     mulf (subf parentAge x728) x729)
                                                newAge3
                                            with
                                              (st456, x730)
                                            in
                                            match p_apply st456 x730 totalLeavingRate13 with (st457, x731)
                                            in
                                            match p_apply st457 x727 x731 with (st458, x732)
                                            in
                                            match
                                              updateRepertoire st458 parentRep nextEvent3 nHosts
                                            with
                                              (st459, x733)
                                            in
                                            match
                                              fullModelWeight1
                                                st459
                                                (addi 1 1)
                                                x733
                                                rep2
                                                newAge3
                                                finalAge31
                                                orderedEvents1
                                                x706
                                                nHosts
                                                modelParams11
                                            with
                                              (st460, x734)
                                            in
                                            p_apply st460 x732 x734)
                                       nEvents41
                                   with
                                     (st461, x735)
                                   in
                                   (st461, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = x705,
                                       logModelDensity = x735,
                                       success = true })
                                 else
                                   (st421, CorrectedBranchSample1
                                     { history = orderedEvents1,
                                       logSamplingDensity = p_pure (log1 0.),
                                       logModelDensity = p_pure (log1 0.),
                                       success = false })
                               with
                                 (st462, x736)
                               in
                               match x736 with CorrectedBranchSample1 x737
                               in
                               match x737 with {history = x738}
                               in
                               match
                                 p_map
                                   st462
                                   (lam x739.
                                      lam x740.
                                        lam x741.
                                          match x737 with {success = x742}
                                          in
                                          CorrectedBranchSample1
                                            { history = x739,
                                              logSamplingDensity = x740,
                                              logModelDensity = x741,
                                              success = x742 })
                                   x738
                               with
                                 (st463, x743)
                               in
                               match x737 with {logSamplingDensity = x744}
                               in
                               match p_apply st463 x743 x744 with (st464, x745)
                               in
                               match x737 with {logModelDensity = x746}
                               in
                               p_apply st464 x745 x746)
                          x662
                      with
                        (st465, branchSample1)
                      in
                      match
                        p_map
                          st465
                          (lam x747.
                             lam x748.
                               lam x749.
                                 subf
                                   (subf
                                      (match x747 with CorrectedBranchSample1 x7010
                                       then
                                         x7010.logModelDensity
                                       else
                                         let #var"177" =
                                           print
                                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:14-166:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                         in
                                         exit 1)
                                      x748)
                                   x749)
                          branchSample1
                      with
                        (st466, x750)
                      in
                      match
                        p_map
                          st466
                          (lam x751.
                             match x751 with CorrectedBranchSample1 x7110
                             then
                               x7110.logSamplingDensity
                             else
                               let #var"178" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:45-166:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st467, x752)
                      in
                      match p_apply st467 x750 x752 with (st468, x753)
                      in
                      match
                        getRepertoireSamplingDensity st468 rep2 samplingProb nHosts
                      with
                        (st469, x754)
                      in
                      match
                        p_map
                          st469
                          (lam x755.
                             mulf
                               x755
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
                                           let #var"179" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:113-166:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1))
                                     0.)))
                          x754
                      with
                        (st470, x756)
                      in
                      match p_apply st470 x753 x756 with (st471, x757)
                      in
                      let nl = (match tree2 with MsgLeaf carried40
                                         then
                                           carried40.label
                                         else match tree2 with MsgNode carried41
                                         then
                                           carried41.label
                                         else
                                           let #var"179" =
                                             print
                                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:113-166:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                           in
                                           exit 1) in
                      let st472 =
                        p_weight
                          st471
                          (hrmStoreLikrWeight nl)
                          (/-temp-/lam x766.
                             x766)
                          x757
                      in
                      let foo2 = {} in
                      match
                        p_assume
                          st472
                          hrmStoreAssume
                          (p_pure (mkCategorical (kroneckerDelta 4 4)))
                      with
                        (st473, x758)
                      in
                      match observationMessage1 st473 rep2 1 nHosts with (st474, x759)
                      in
                      match mtxCreate1 st474 nHosts x758 x759 with (st475, newMsg)
                      in
                      match
                        mtxMul1
                          st475
                          newMsg
                          (match tree2 with MsgNode x6910
                           then
                             x6910.leftKernel
                           else
                             let #var"180" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 171:33-171:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st476, x760)
                      in
                      match
                        sampleTreeHistory
                          st476
                          (match tree2 with MsgNode x6410
                           then
                             x6410.left
                           else
                             let #var"181" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 176:6-176:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          nHosts
                          x760
                          rep2
                          (match tree2 with MsgLeaf carried42
                           then
                             carried42.age
                           else match tree2 with MsgNode carried43
                           then
                             carried43.age
                           else
                             let #var"182" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 176:39-176:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6710
                           then
                             x6710.leftKernel
                           else
                             let #var"183" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 176:62-176:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st477, x761)
                      in
                      match
                        mtxMul1
                          st477
                          newMsg
                          (match tree2 with MsgNode x6810
                           then
                             x6810.rightKernel
                           else
                             let #var"184" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 172:34-172:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                             in
                             p_pure (exit 1))
                      with
                        (st478, x762)
                      in
                      match
                        sampleTreeHistory
                          st478
                          (match tree2 with MsgNode x6010
                           then
                             x6010.right
                           else
                             let #var"185" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 179:6-179:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          nHosts
                          x762
                          rep2
                          (match tree2 with MsgLeaf carried44
                           then
                             carried44.age
                           else match tree2 with MsgNode carried45
                           then
                             carried45.age
                           else
                             let #var"186" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 179:41-179:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                             in
                             exit 1)
                          modelParams11
                          (match tree2 with MsgNode x6310
                           then
                             x6310.rightKernel
                           else
                             let #var"187" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 179:64-179:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                             in
                             p_pure (exit 1))
                      with
                        (st479, x763)
                      in
                      match
                        p_map
                          st479
                          (lam x764.
                             match x764 with CorrectedBranchSample1 x5910
                             then
                               x5910.history
                             else
                               let #var"188" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 186:16-186:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                               in
                               exit 1)
                          branchSample1
                      with
                        (st480, x765)
                      in
                      (st480, HistoryNode
                        { age =
                            match tree2 with MsgLeaf carried46
                            then
                              carried46.age
                            else match tree2 with MsgNode carried47
                            then
                              carried47.age
                            else
                              let #var"189" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 183:12-183:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                              let #var"190" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 184:14-184:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                              in
                              exit 1,
                          left = x761,
                          right = x763,
                          history = x765,
                          repertoire = rep2 })
  in
  let input1 =
  { symbiontTree = Node
    { age = 10.0
    , label = 9
    , left = Node
      { label = 8
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
      { label = 7
      , age = 5.0
      , left = Leaf
        { label = 3
        , age = 0.0
        }
      , right = Node
        { label = 6
        , age = 3.0
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
  , interactions =
      [ [2, 0, 0, 0, 2]
      , [0, 2, 0, 2, 0]
      , [2, 0, 2, 2, 2]
      , [2, 2, 0, 2, 0]
      , [2, 0, 0, 0, 2]
      ]
  , hostDistances =
      [ [1., 1., 1., 1., 1.]
      , [1., 1., 1., 1., 1.]
      , [1., 1., 1., 1., 1.]
      , [1., 1., 1., 1., 1.]
      , [1., 1., 1., 1., 1.]
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
    p_assume
      st hrmStoreLambda (p_pure (mkDirichlet [ 1., 1., 1., 1. ]))
  with
    (st481, lambda)
  in
  match
    p_assume st481 hrmStoreMu (p_pure (mkExponential 10.))
  with
    (st482, mu)
  in
  match
    p_assume st482 hrmStoreBeta (p_pure (mkExponential 1.))
  with
    (st483, beta)
  in
  match
    p_assume
      st483
      hrmStoreAssume
      (p_pure (mkCategorical (kroneckerDelta 4 4)))
  with
    (st484, mSize1)
  in
  recursive let buildTree = lam stree.
    match stree with Leaf { label = label, age = _ } then 
      HRMLeaf { label = label }
    else match stree with Node { label = label, age = _, left = left, right = right } in 
      HRMNode { label = label, left = buildTree left, right = buildTree right } in
  match p_export st484 (hrmStoreTree (buildTree symbiontTree) (match input1 with {interactions = ints} in ints)) (p_pure ()) with st484 in
  match
    p_map
      st484
      (lam x768.
         subf 0. (get x768 (subi 1 1)))
      lambda
  with
    (st485, x769)
  in
  match
    p_map st485 (lam x770.
         get x770 (subi 1 1)) lambda
  with
    (st486, x771)
  in
  match
    p_map st486 (lam x772.
         get x772 (subi 2 1)) lambda
  with
    (st487, x773)
  in
  match
    p_map
      st487
      (lam x774.
         lam x775.
           subf 0. (addf (get x774 (subi 2 1)) x775))
      lambda
  with
    (st488, x776)
  in
  match
    p_map st488 (lam x777.
         get x777 (subi 3 1)) lambda
  with
    (st489, x778)
  in
  match p_apply st489 x776 x778 with (st490, x779)
  in
  match
    p_map st490 (lam x780.
         get x780 (subi 3 1)) lambda
  with
    (st491, x781)
  in
  match
    p_map st491 (lam x782.
         get x782 (subi 4 1)) lambda
  with
    (st492, x783)
  in
  match
    p_map
      st492
      (lam x784.
         subf 0. (get x784 (subi 4 1)))
      lambda
  with
    (st493, x785)
  in
  match
    p_traverseSeq
      st493
      (lam st494.
         lam x786.
           (st494, x786))
      [ x769,
        x771,
        p_pure 0.,
        x773,
        x779,
        x781,
        p_pure 0.,
        x783,
        x785 ]
  with
    (st495, x787)
  in
  match p_map st495 concat x787 with (st496, x788)
  in
  match
    p_map
      st496
      (lam x789.
         lam x790.
           subi (muli x789 x790) 9)
      mSize1
  with
    (st497, x791)
  in
  match p_apply st497 x791 mSize1 with (st498, x792)
  in
  match
    p_map st498 (lam x793.
         subi x793 1) x792
  with
    (st499, x794)
  in
  match
    p_map
      st499
      (lam x795.
         match geqi x795 0 with true
         then
           rec3 0. (subi x795 1) (cons (anon 0. x795) "")
         else
           "")
      x794
  with
    (st500, x796)
  in
  match p_apply st500 x788 x796 with (st501, data)
  in
  match
    p_map
      st501
      (lam x797.
         externalExtArrMakeUninit extArrKindFloat64 (length x797))
      data
  with
    (st502, a70)
  in
  match
    p_bind
      st502
      hrmStoreSubmodel
      (hrmInit {})
      (lam st503.
         lam x798.
           match
             match x798 with [ _,
                 _ ] ++ _
             then
               match
                 p_map
                   st503
                   (lam x799.
                      externalExtArrSet x799 0 (get x798 0))
                   a70
               with
                 (st504, x800)
               in
               match splitAt x798 1 with {#label"1" = x801}
               in
               match rec12 st504 a70 (addi 0 1) x801 with (st505, x802)
               in
               (st505, cons x800 x802)
             else match x798 with [ e16 ]
             then
               match splitAt x798 1 with {#label"1" = x803}
               in
               let slice15 = x803 in
               match
                 p_map
                   st503
                   (lam x804.
                      externalExtArrSet x804 0 e16)
                   a70
               with
                 (st506, x805)
               in
               (st506, [ x805 ])
             else match x798 with ""
             in
             (st503, "")
           with
             (st507, x806)
           in
           p_traverseSeq
             st507
             (lam st508.
                lam x807.
                  (st508, x807))
             x806)
      data
  with
    (st509, #var"193")
  in
  let #var"1710" = {} in
  let a63 = a70 in
  match
    p_map
      st509
      (lam x808.
         lam x809.
           lam x810.
             lam st510.
               let x811 =
                 match eqi (muli x808 x809) x810 with true
                 then
                   { arr = a63, n = x809, m = x808 }
                 else
                   let x816 = error "matFromArrExn: dimensions mismatch" in
                   match x816 with {arr = x817}
                   in
                   match x816 with {n = x818}
                   in
                   match x816 with {m = x819}
                   in
                   { arr = p_pure x817, n = x818, m = x819 }
               in
               match x811 with {arr = x812}
               in
               p_map
                 st510
                 (lam x813.
                    match x811 with {n = x814}
                    in
                    match x811 with {m = x815}
                    in
                    { arr = x813, n = x814, m = x815 })
                 x812)
      mSize1
  with
    (st511, x820)
  in
  match p_apply st511 x820 mSize1 with (st512, x821)
  in
  match
    p_map st512 (lam x822.
         externalExtArrLength x822) a63
  with
    (st513, x823)
  in
  match
    p_subApply st513 hrmStoreSubmodel (hrmInit {}) x821 x823
  with
    (st514, x824)
  in
  match p_join st514 x824 with (st515, mtx4)
  in
  match p_map st515 (lam x825.
         x825.m) mtx4 with (st516, m2)
  in
  match p_map st516 (lam x826.
         x826.n) mtx4 with (st517, n3)
  in
  match
    p_map
      st517
      (lam x827.
         match x827 with {arr = #var"X11"}
         in
         externalExtArrKind #var"X11")
      mtx4
  with
    (st518, x828)
  in
  match matMakeUninit1 st518 x828 m2 n3 with (st519, b14)
  in
  match
    p_map
      st519
      (lam x829.
         lam x830.
           muli x829 x830)
      m2
  with
    (st520, x831)
  in
  match p_apply st520 x831 n3 with (st521, mn)
  in
  match
    p_map
      st521
      (lam x832.
         lam x833.
           lam x834.
             externalCblasCopy x832 x833 1 x834 1)
      mn
  with
    (st522, x835)
  in
  match p_map st522 (lam x836.
         x836.arr) mtx4 with (st523, x837)
  in
  match p_apply st523 x835 x837 with (st524, x838)
  in
  match b14 with {arr = #var"X12"}
  in
  match p_apply st524 x838 #var"X12" with (st525, #var"1110")
  in
  match
    p_map
      st525
      (lam x839.
         lam x840.
           lam x841.
             externalCblasScal x839 x840 x841 1)
      mn
  with
    (st526, x842)
  in
  match p_apply st526 x842 mu with (st527, x843)
  in
  match b14 with {arr = #var"X13"}
  in
  match p_apply st527 x843 #var"X13" with (st528, #var"1210")
  in
  match p_map st528 (lam x. lam. x) #var"X13" with (st528, part_dep_arr) in
  match p_apply st528 part_dep_arr #var"1210" with (st528, dep_arr) in
  let qMatrix2 = {b14 with arr = dep_arr } in
  match input1 with {interactions = #var"X14"}
  in
  match
    postorderTraverse st528 symbiontTree qMatrix2 #var"X14" nHosts1
  with
    (st529, postorderTree)
  in
  let a36 =
    match postorderTree with MsgLeaf carried66
    then
      match carried66 with {outMsg = #var"X24"}
      in
      p_pure #var"X24"
    else match postorderTree with MsgNode carried67
    then
      carried67.outMsg
    else
      let #var"1106" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 42:36-42:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n"
      in
      p_pure (exit 1)
  in
  let b4 = mtxCreate nHosts1 3 (ones (muli 3 nHosts1)) in
  match matHasSameShape2 st529 a36 b4 with (st530, x844)
  in
  match
    p_bind
      st530
      hrmStoreSubmodel
      (hrmInit {})
      (lam st531.
         lam x845.
           match
             match x845 with true
             then
               match
                 p_map
                   st531
                   (lam x846.
                      match x846 with {arr = #var"X15"}
                      in
                      externalExtArrKind #var"X15")
                   a36
               with
                 (st532, x847)
               in
               match
                 p_map st532 (lam x848.
                      x848.m) a36
               with
                 (st533, x849)
               in
               match
                 p_map st533 (lam x850.
                      x850.n) a36
               with
                 (st534, x851)
               in
               match matMakeUninit1 st534 x847 x849 x851 with (st535, c310)
               in
               match matHasSameShape2 st535 a36 b4 with (st536, x852)
               in
               match c310 with {m = #var"X16"}
               in
               match
                 p_map
                   st536
                   (lam x853.
                      match b4 with {m = #var"X17"}
                      in
                      eqi #var"X17" x853)
                   #var"X16"
               with
                 (st537, x854)
               in
               match c310 with {n = #var"X18"}
               in
               match
                 p_map
                   st537
                   (lam x855.
                      match b4 with {n = #var"X19"}
                      in
                      eqi #var"X19" x855)
                   #var"X18"
               with
                 (st538, x856)
               in
               match and st538 x854 x856 with (st539, x857)
               in
               match and st539 x852 x857 with (st540, x858)
               in
               match
                 p_subMap
                   st540
                   hrmStoreSubmodel
                   (hrmInit {})
                   (lam x859.
                      lam st541.
                        match x859 with true
                        then
                          match
                            p_map
                              st541
                              (lam x860.
                                 lam x861.
                                   lam x862.
                                     lam x863.
                                       match x860 with {m = #var"X20"}
                                       in
                                       match b4 with {arr = #var"X21"}
                                       in
                                       externalMatElemMul #var"X20" x861 x862 #var"X21" x863)
                              a36
                          with
                            (st542, x864)
                          in
                          match
                            p_map
                              st542 (lam x865.
                                 x865.n) a36
                          with
                            (st543, x866)
                          in
                          match p_apply st543 x864 x866 with (st544, x867)
                          in
                          match
                            p_map
                              st544
                              (lam x868.
                                 x868.arr)
                              a36
                          with
                            (st545, x869)
                          in
                          match p_apply st545 x867 x869 with (st546, x870)
                          in
                          match c310 with {arr = #var"X22"}
                          in
                          match p_apply st546 x870 #var"X22" with (st547, #var"1510")
                          in
                          (st547, Right
                            {})
                        else
                          (st541, Left
                            (DimensionMismatch
                               {})))
                   x858
               with
                 (st548, #var"1310")
               in
               (st548, Right
                 c310)
             else
               (st531, Left
                 (DimensionMismatch
                    {}))
           with
             (st549, n)
           in
           match n with Right x871
           then
             match x871 with {arr = x872}
             in
             match
               p_map
                 st549
                 (lam x873.
                    lam x874.
                      lam x875.
                        Right
                          { arr = x873, n = x874, m = x875 })
                 x872
             with
               (st550, x876)
             in
             match x871 with {n = x877}
             in
             match p_apply st550 x876 x877 with (st551, x878)
             in
             match x871 with {m = x879}
             in
             p_apply st551 x878 x879
           else match n with Left x880
           in
           (st549, p_pure (Left
                x880)))
      x844
  with
    (st552, x881)
  in
  match eitherEither1 st552 x881 with (st553, rootSamplingProb)
  in
  match
    suggestNodeRep
      st553
      rootSamplingProb
      nHosts1
      (match postorderTree with MsgLeaf carried54
       then
         carried54.label
       else match postorderTree with MsgNode carried55
       then
         carried55.label
       else
         let #var"194" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 43:57-43:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
         in
         exit 1)
  with
    (st554, rootRep)
  in
  match any1 st554 rootRep with (st555, x882)
  in
  match bool2real st555 x882 with (st556, x883)
  in
  let rl_ = (match postorderTree with MsgLeaf carried64
                     then
                       carried64.label
                     else match postorderTree with MsgNode carried65
                     then
                       carried65.label
                     else
                       let #var"1105" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 45:45-45:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1) in
  let st557 =
    p_weight
      st556
      (hrmStoreNodeSuppWeight rl_)
      (lam x912.
         externalLog
           (addf
              x912
              (mulf
                 (int2float
                    (match postorderTree with MsgLeaf carried64
                     then
                       carried64.label
                     else match postorderTree with MsgNode carried65
                     then
                       carried65.label
                     else
                       let #var"1105" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 45:45-45:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                       in
                       exit 1))
                 0.)))
      x883
  in
  let foo3 = {} in
  match
    getRepertoireSamplingDensity st557 rootRep rootSamplingProb nHosts1
  with
    (st558, x884)
  in
  let rl = (match postorderTree with MsgLeaf carried62
                     then
                       carried62.label
                     else match postorderTree with MsgNode carried63
                     then
                       carried63.label
                     else
                       let #var"1104" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 52:70-52:89>:\nField \'label\' not found\n[0m  logWeight (rootLogModelDensity - rootLogSamplingDensity) * exp(Real([31mpostorderTree.label[0m[0m) * 0.);\n"
                       in
                       exit 1) in
  let st559 =
    p_weight
      st558
      (hrmStoreLikrWeight rl)
      (lam x910.
         mulf
           (subf
              (negf
                 (log1
                    (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1)))))
              x910)
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
                       let #var"1104" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 52:70-52:89>:\nField \'label\' not found\n[0m  logWeight (rootLogModelDensity - rootLogSamplingDensity) * exp(Real([31mpostorderTree.label[0m[0m) * 0.);\n"
                       in
                       exit 1))
                 0.)))
      x884
  in
  let foo4 = {} in
  match observationMessage1 st559 rootRep 1 nHosts1 with (st560, x885)
  in
  match mtxCreate1 st560 nHosts1 mSize1 x885 with (st561, newMsg1)
  in
  match input1 with {dMean = #var"X23"}
  in
  match mtxGet st561 2 2 qMatrix2 with (st562, x886)
  in
  match p_map st562 (lam x887.
         negf x887) x886 with (st563, q2)
  in
  match mtxGet st563 1 1 qMatrix2 with (st564, x888)
  in
  match p_map st564 (lam x889.
         negf x889) x888 with (st565, x890)
  in
  match mtxGet st565 3 3 qMatrix2 with (st566, x891)
  in
  match p_map st566 (lam x892.
         negf x892) x891 with (st567, x893)
  in
  match mtxGet st567 2 1 qMatrix2 with (st568, x894)
  in
  match
    p_map
      st568
      (lam x895.
         lam x896.
           divf x895 x896)
      x894
  with
    (st569, x897)
  in
  match p_apply st569 x897 q2 with (st570, x898)
  in
  match mtxGet st570 2 3 qMatrix2 with (st571, x899)
  in
  match
    p_map
      st571
      (lam x900.
         lam x901.
           divf x900 x901)
      x899
  with
    (st572, x902)
  in
  match p_apply st572 x902 q2 with (st573, x903)
  in
  let modelParams2 =
    ModelParams1
      { beta = beta,
        meanDist = #var"X23",
        hostMetric =
          mtxCreate
            (length1 hostDistances)
            (length (get hostDistances (subi 1 1)))
            (match hostDistances with [ _ ] ++ _
             then
               match splitAt hostDistances 1 with {#label"1" = x909}
               in
               rec2 (concat "" (get hostDistances 0)) x909
             else match hostDistances with ""
             in
             ""),
        embeddedQMatrix =
          EmbeddedMarkovChainMatrix1
            { totalRates =
                [ x890,
                  q2,
                  x893 ],
              transitionProbs =
                [ [ p_pure 0.,
                    p_pure 1.,
                    p_pure 0. ],
                  [ x898,
                    p_pure 0.,
                    x903 ],
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
      let #var"1103" =
        print
          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 68:16-68:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
      in
      exit 1
  in
  match
    mtxMul1
      st573
      newMsg1
      (match postorderTree with MsgNode x951
       then
         x951.leftKernel
       else
         let #var"195" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 56:31-56:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st574, x904)
  in
  match
    sampleTreeHistory
      st574
      (match postorderTree with MsgNode x905
       then
         x905.left
       else
         let #var"196" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 70:4-70:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
         in
         exit 1)
      nHosts1
      x904
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x911
       then
         x911.leftKernel
       else
         let #var"197" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 70:72-70:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st575, x906)
  in
  match
    mtxMul1
      st575
      newMsg1
      (match postorderTree with MsgNode x941
       then
         x941.rightKernel
       else
         let #var"198" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 57:32-57:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
         in
         p_pure (exit 1))
  with
    (st576, x907)
  in
  match
    sampleTreeHistory
      st576
      (match postorderTree with MsgNode x8810
       then
         x8810.right
       else
         let #var"199" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 74:4-74:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
         in
         exit 1)
      nHosts1
      x907
      rootRep
      rootAge
      modelParams2
      (match postorderTree with MsgNode x8910
       then
         x8910.rightKernel
       else
         let #var"1100" =
           print
             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 74:74-74:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
         in
         p_pure (exit 1))
  with
    (st577, x908)
  in
  match p_map st577 (
    lam mu. lam beta. lam lambda. lam rootRep1. lam rootRep2.
      { mu = mu
      , beta = beta
      , lambda = lambda
      , rootRep = [rootRep1, rootRep2]
      }
  ) mu with (st577, partres) in
  match p_apply st577 partres beta with (st577, partres) in
  match p_apply st577 partres lambda with (st577, partres) in
  match p_apply st577 partres (get rootRep 0) with (st577, partres) in
  match p_apply st577 partres (get rootRep 1) with (st577, res) in
  p_export
    st577
    hrmStoreExport
    res
