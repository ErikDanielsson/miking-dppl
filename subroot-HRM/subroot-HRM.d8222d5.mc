let and: Bool -> Bool -> Bool =
  lam a92: Bool.
    lam b31: Bool.
      match a92 with true
      then
        b31
      else
        false
in
let isNaN: Float -> Bool =
  lam a91: Float.
    match eqf a91 a91 with true
    then
      false
    else
      true
in
external externalExp : Float -> Float in
let exp = lam x189: Float.
    externalExp x189 in
external externalLog : Float -> Float in
let log = lam x188: Float.
    externalLog x188 in
external externalPow : Float -> Float -> Float in
let pow = lam x187: Float.
    lam y: Float.
      externalPow x187 y
in
recursive
  let rec: all a. all a1. (a -> a1) -> [a] -> [a1] =
    lam f.
      lam s.
        match s with ""
        then
          ""
        else match s with [ a2 ]
        then
          [ f a2 ]
        else match s with [ a3 ] ++ ss
        in
        cons (f a3) (rec f ss)
in
let map1 = lam f37.
    lam s16.
      rec f37 s16 in
recursive
  let rec1: all a4. all a5. (Int -> a4 -> a5) -> Int -> [a4] -> [a5] =
    lam f1.
      lam i.
        lam s1.
          match s1 with ""
          then
            ""
          else match s1 with [ a6 ]
          then
            [ f1 i a6 ]
          else match s1 with [ a7 ] ++ ss1
          in
          cons (f1 i a7) (rec1 f1 (addi i 1) ss1)
in
let mapi1 = lam f36.
    lam s15.
      rec1 f36 0 s15 in
let iteri1 =
  lam f35.
    lam s14.
      let #var"24" = mapi1 f35 s14 in
      {}
in
recursive
  let rec2: all a8. all a9. (a8 -> a9 -> a8) -> a8 -> [a9] -> a8 =
    lam f2.
      lam acc.
        lam s2.
          match s2 with ""
          then
            acc
          else match s2 with [ a10 ] ++ ss2
          in
          rec2 f2 (f2 acc a10) ss2
in
let foldl1 =
  lam f34.
    lam acc20.
      lam s13.
        rec2 f34 acc20 s13
in
recursive
  let rec3: all a11. (Int -> a11) -> Int -> [a11] -> [a11] =
    lam f3.
      lam i1.
        lam acc1.
          match geqi i1 0 with true
          then
            rec3 f3 (subi i1 1) (cons (f3 i1) acc1)
          else
            acc1
in
let create1 = lam l6.
    lam f33.
      rec3 f33 (subi l6 1) ""
in
type Either a12 b in
con Left: all a13. all b1. a13 -> Either a13 b1 in
con Right: all a14. all b2. b2 -> Either a14 b2 in
let anon: all a90. a90 -> Int -> a90 = lam v4.
    lam #var"23".
      v4
in
let make: all a89. Int -> a89 -> [a89] = lam n9: Int.
    lam v3: a89.
      create1 n9 (anon v3)
in
let g: all c10. all b30. all a88. (a88 -> b30 -> c10 -> a88) -> (a88, [b30]) -> c10 -> (a88, [b30]) =
  lam f32.
    lam acc18: (a88, [b30]).
      lam x212.
        match acc18 with (acc19, [ x186 ] ++ xs1)
        then
          (f32 acc19 x186 x212, xs1)
        else
          error "foldl2: Cannot happen!"
in
let g1: all c9. all b29. all a87. (a87 -> b29 -> c9 -> a87) -> (a87, [c9]) -> b29 -> (a87, [c9]) =
  lam f31.
    lam acc16: (a87, [c9]).
      lam x185.
        match acc16 with (acc17, [ x211 ] ++ xs2)
        then
          (f31 acc17 x185 x211, xs2)
        else
          error "foldl2: Cannot happen!"
in
let foldl2: all a86. all b28. all c8. (a86 -> b28 -> c8 -> a86) -> a86 -> [b28] -> [c8] -> a86 =
  lam f30: a86 -> b28 -> c8 -> a86.
    lam acc13: a86.
      lam seq11: [b28].
        lam seq21: [c8].
          match geqi (length seq11) (length seq21) with true
          then
            match foldl1 (g f30) (acc13, seq11) seq21 with (acc14, _)
            in
            acc14
          else match foldl1 (g1 f30) (acc13, seq21) seq11 with (acc15, _)
          in
          acc15
in
recursive
  let work: all b3. all a15. (a15 -> Int -> b3 -> a15) -> a15 -> Int -> [b3] -> a15 =
    lam fn.
      lam acc2.
        lam i2.
          lam s3.
            match s3 with [ e ] ++ rest
            then
              work fn (fn acc2 i2 e) (addi i2 1) rest
            else
              acc2
in
let foldli: all a85. all b27. (a85 -> Int -> b27 -> a85) -> a85 -> [b27] -> a85 =
  lam fn1: a85 -> Int -> b27 -> a85.
    lam initAcc: a85.
      lam seq8: [b27].
        work fn1 initAcc 0 seq8
in
let anon1: all c7. all b26. all a84. (a84 -> b26 -> c7) -> [c7] -> a84 -> b26 -> [c7] =
  lam f29.
    lam acc12.
      lam x184.
        lam x210.
          snoc acc12 (f29 x184 x210)
in
let zipWith: all a83. all b25. all c6. (a83 -> b25 -> c6) -> [a83] -> [b25] -> [c6] = lam f28: a83 -> b25 -> c6.
    foldl2 (anon1 f28) ""
in
recursive
  let any: all a16. (a16 -> Bool) -> [a16] -> Bool =
    lam p: a16 -> Bool.
      lam seq: [a16].
        match null seq with true
        then
          false
        else match p (head seq) with true
        then
          true
        else
          any p (tail seq)
in
let join: all a82. [[a82]] -> [a82] = lam seqs: [[a82]].
    foldl1 concat "" seqs
in
recursive
  let work1: all a17. (a17 -> Bool) -> [a17] -> [a17] -> [a17] -> ([a17], [a17]) =
    lam p1.
      lam l.
        lam r.
          lam seq1.
            match seq1 with ""
            then
              (l, r)
            else match seq1 with [ s4 ] ++ seq2
            in
            match p1 s4 with true
            then
              work1 p1 (cons s4 l) r seq2
            else
              work1 p1 l (cons s4 r) seq2
in
let partition: all a81. (a81 -> Bool) -> [a81] -> ([a81], [a81]) =
  lam p2: a81 -> Bool.
    lam seq7: [a81].
      work1 p2 "" "" (reverse seq7)
in
let anon2: all a80. (a80 -> a80 -> Int) -> a80 -> a80 -> Bool =
  lam cmp4.
    lam h5.
      lam x183.
        lti (cmp4 x183 h5) 0
in
recursive
  let quickSort: all a18. (a18 -> a18 -> Int) -> [a18] -> [a18] =
    lam cmp: a18 -> a18 -> Int.
      lam seq3: [a18].
        match null seq3 with true
        then
          seq3
        else
          let h = head seq3 in
          let t = tail seq3 in
          let lr = partition (anon2 cmp h) t in
          concat (quickSort cmp lr.0) (cons h (quickSort cmp lr.1))
in
recursive
  let rec4 =
    lam f4.
      lam n.
        lam i3.
          match geqi i3 n with true
          then
            {}
          else
            (f4 i3)
            ; rec4 f4 n (addi i3 1)
in
let repeati: (Int -> ()) -> Int -> () = lam f27: Int -> ().
    lam n8: Int.
      rec4 f27 n8 0
in
let eitherEither: all a79. all b24. all c5. (a79 -> c5) -> (b24 -> c5) -> Either a79 b24 -> c5 =
  lam lf: a79 -> c5.
    lam rf: b24 -> c5.
      lam e3: Either a79 b24.
        match e3 with Left content
        then
          lf content
        else match e3 with Right content1
        in
        rf content1
in
type ExtArrKind a19 in
type ExtArr a20 in
external externalExtArrMakeUninit : all a21. ExtArrKind a21 -> Int -> ExtArr a21
in
external externalExtArrKind : all a22. ExtArr a22 -> ExtArrKind a22
in
external externalExtArrLength : all a23. ExtArr a23 -> Int in
external externalExtArrGet : all a24. ExtArr a24 -> Int -> a24
in
external externalExtArrSet! : all a25. ExtArr a25 -> Int -> a25 -> ()
in
external extArrKindFloat64 : ExtArrKind Float in
let extArrMakeUninit: all a78. ExtArrKind a78 -> Int -> ExtArr a78 =
  lam kind2: ExtArrKind a78.
    lam n7: Int.
      externalExtArrMakeUninit kind2 n7
in
let extArrLength: all a76. ExtArr a76 -> Int = lam a77: ExtArr a76.
    externalExtArrLength a77
in
let extArrGetExn: all a74. ExtArr a74 -> Int -> a74 =
  lam a75: ExtArr a74.
    lam i24: Int.
      externalExtArrGet a75 i24
in
let extArrSetExn: all a72. ExtArr a72 -> Int -> a72 -> () =
  lam a73: ExtArr a72.
    lam i23: Int.
      lam v2: a72.
        externalExtArrSet a73 i23 v2
in
let extArrOfSeq: all a70. ExtArrKind a70 -> [a70] -> ExtArr a70 =
  lam kind1: ExtArrKind a70.
    lam seq6: [a70].
      tmOpaque (let len = length seq6 in
       let a71 = externalExtArrMakeUninit kind1 len in
       recursive
         let work3 =
           lam i22.
             match eqi i22 len with true
             then
               {}
             else
               let #var"21" = externalExtArrSet a71 i22 (get seq6 i22) in
               work3 (addi i22 1)
       in
       let #var"22" = work3 0 in
       a71)
in
let extArrToSeq: all a68. ExtArr a68 -> [a68] =
  lam a69: ExtArr a68.
    create1 (externalExtArrLength a69) (externalExtArrGet a69)
in
type CBLASLayout in
external cblasRowMajor : CBLASLayout in
type CBLASTranspose in
external cblasNoTrans : CBLASTranspose in
external externalCblasCopy : all a26. Int -> ExtArr a26 -> Int -> ExtArr a26 -> Int -> ()
in
external externalCblasScal : all a27. Int -> a27 -> ExtArr a27 -> Int -> ()
in
external externalCblasGemm : all a28. CBLASLayout -> CBLASTranspose -> CBLASTranspose -> Int -> Int -> Int -> a28 -> ExtArr a28 -> Int -> ExtArr a28 -> Int -> a28 -> ExtArr a28 -> Int -> ()
in
type MatError in
con DimensionMismatch: () -> MatError in
con NotSquare: () -> MatError in
let matErrorToString: MatError -> [Char] =
  lam err3: MatError.
    let #var"X14" = err3 in
    match #var"X14" with DimensionMismatch _
    then
      "Dimension mismatch"
    else match #var"X14" with NotSquare _
    in
    "Not square"
in
type Mat a29 =
  {m: Int, n: Int, arr: ExtArr a29} in
let matMakeUninit: all a67. ExtArrKind a67 -> Int -> Int -> Mat a67 =
  lam kind: ExtArrKind a67.
    lam m4: Int.
      lam n6: Int.
        { n = n6,
          arr = externalExtArrMakeUninit kind (muli m4 n6),
          m = m4 }
in
let matGetExn: all a65. Mat a65 -> Int -> Int -> a65 =
  lam a66: Mat a65.
    lam i21: Int.
      lam j3: Int.
        externalExtArrGet a66.arr (addi (muli i21 a66.n) j3)
in
let matSetExn: all a63. Mat a63 -> Int -> Int -> a63 -> () =
  lam a64: Mat a63.
    lam i20: Int.
      lam j2: Int.
        lam v1: a63.
          externalExtArrSet a64.arr (addi (muli i20 a64.n) j2) v1
in
let matFromArrExn: all a61. Int -> Int -> ExtArr a61 -> Mat a61 =
  lam m3: Int.
    lam n5: Int.
      lam a62: ExtArr a61.
        match eqi (muli m3 n5) (extArrLength a62) with true
        then
          { n = n5, arr = a62, m = m3 }
        else
          error "matFromArrExn: dimensions mismatch"
in
let matCopy: all a59. Mat a59 -> Mat a59 =
  lam a60: Mat a59.
    let mn1 = muli a60.m a60.n in
    let b22 =
      tmOpaque (let b23 = extArrMakeUninit (externalExtArrKind a60.arr) mn1 in
       let #var"20" = externalCblasCopy mn1 a60.arr 1 b23 1 in
       b23)
    in
    { a60 with arr = b22 }
in
let matHasSameShape2 =
  lam a58.
    lam b21.
      and (eqi a58.m b21.m) (eqi a58.n b21.n)
in
let matHasSameShape3 =
  lam a57.
    lam b20.
      lam c4.
        and (matHasSameShape2 a57 b20) (matHasSameShape2 b20 c4)
in
let matIsSquare = lam a56.
    eqi a56.m a56.n in
external externalMatTranspose : Int -> Int -> ExtArr Float -> ExtArr Float -> ()
in
let matTranposeNoAlloc: Mat Float -> Mat Float -> Either MatError () =
  lam a55: Mat Float.
    lam b19: Mat Float.
      match and (eqi a55.m b19.n) (eqi a55.n b19.m) with true
      then
        let #var"19" = externalMatTranspose a55.m a55.n a55.arr b19.arr
        in
        Right
          {}
      else
        Left
          (DimensionMismatch
             {})
in
external externalMatElemMul : Int -> Int -> ExtArr Float -> ExtArr Float -> ExtArr Float -> ()
in
let matElemMulNoAlloc: Mat Float -> Mat Float -> Mat Float -> Either MatError () =
  lam a54: Mat Float.
    lam b18: Mat Float.
      lam c3: Mat Float.
        match matHasSameShape3 a54 b18 c3 with true
        then
          let #var"18" = externalMatElemMul a54.m a54.n a54.arr b18.arr c3.arr
          in
          Right
            {}
        else
          Left
            (DimensionMismatch
               {})
in
let matTranspose: Mat Float -> Mat Float =
  lam a53: Mat Float.
    tmOpaque (let b17 = matMakeUninit (externalExtArrKind a53.arr) a53.n a53.m
     in
     let #var"17" = matTranposeNoAlloc a53 b17 in
     b17)
in
let matElemMul: Mat Float -> Mat Float -> Either MatError (Mat Float) =
  lam a52: Mat Float.
    lam b16: Mat Float.
      match matHasSameShape2 a52 b16 with true
      then
        Right
          (tmOpaque (let c2 = matMakeUninit (externalExtArrKind a52.arr) a52.m a52.n
            in
            let #var"16" = matElemMulNoAlloc a52 b16 c2 in
            c2))
      else
        Left
          (DimensionMismatch
             {})
in
let anon3: MatError -> Mat Float = lam err2.
    error (matErrorToString err2)
in
let anon4: Mat Float -> Mat Float = lam x182.
    x182 in
let matElemMulExn: Mat Float -> Mat Float -> Mat Float =
  lam a51: Mat Float.
    lam b15: Mat Float.
      eitherEither anon3 anon4 (matElemMul a51 b15)
in
let matScale: Float -> Mat Float -> Mat Float =
  lam s12: Float.
    lam a50: Mat Float.
      let m2 = a50.m in
      let n4 = a50.n in
      let mn = muli m2 n4 in
      tmOpaque (let b14 = matMakeUninit (externalExtArrKind a50.arr) m2 n4 in
       let #var"14" = externalCblasCopy mn a50.arr 1 b14.arr 1 in
       let #var"15" = externalCblasScal mn s12 b14.arr 1 in
       b14)
in
let matMul: Mat Float -> Mat Float -> Either MatError (Mat Float) =
  lam a49: Mat Float.
    lam b13: Mat Float.
      let m1 = a49.m in
      let n3 = b13.n in
      let k = a49.n in
      match eqi k b13.m with true
      then
        Right
          (tmOpaque (let c1 = matMakeUninit (externalExtArrKind b13.arr) m1 n3 in
            let #var"13" =
              externalCblasGemm
                cblasRowMajor
                cblasNoTrans
                cblasNoTrans
                m1
                n3
                k
                1.
                a49.arr
                k
                b13.arr
                n3
                0.
                c1.arr
                n3
            in
            c1))
      else
        Left
          (DimensionMismatch
             {})
in
let anon5: MatError -> Mat Float = lam err1.
    error (matErrorToString err1)
in
let anon6: Mat Float -> Mat Float = lam x181.
    x181 in
let matMulExn: Mat Float -> Mat Float -> Mat Float =
  lam a48: Mat Float.
    lam b12: Mat Float.
      eitherEither anon5 anon6 (matMul a48 b12)
in
external externalMatExp : Int -> Int -> ExtArr Float -> ExtArr Float
in
let matExp: Mat Float -> Either MatError (Mat Float) =
  lam a47: Mat Float.
    match matIsSquare a47 with true
    then
      Right
        { a47 with arr = externalMatExp a47.m a47.n a47.arr }
    else
      Left
        (NotSquare
           {})
in
let anon7: MatError -> Mat Float = lam err.
    error (matErrorToString err)
in
let anon8: Mat Float -> Mat Float = lam x180.
    x180 in
let matExpExn: Mat Float -> Mat Float =
  lam a46: Mat Float.
    eitherEither anon7 anon8 (matExp a46)
in
recursive
  let work2: all a30. Int -> (Int -> a30 -> a30) -> Int -> a30 -> a30 =
    lam bound.
      lam f5.
        lam i4.
          lam acc3.
            match lti i4 bound with true
            then
              work2 bound f5 (addi i4 1) (f5 i4 acc3)
            else
              acc3
in
let _iterateni = lam bound1.
    lam f26.
      work2 bound1 f26 0
in
let seqSnoc = snoc in
let seqCons = cons in
let seqCreate = create1 in
let seqLength = length in
let seqMap = map1 in
let seqMapi = mapi1 in
let seqZipWith = zipWith in
let seqSubsequence = subsequence in
let seqFoldl = foldl1 in
let seqFoldli = foldli in
let seqAny = any in
let mathExp = exp in
let mathLog = log in
let mathIsNaN = isNaN in
let anon9: (Float -> Float) -> Mat Float -> Mat Float -> Int -> () =
  lam f25.
    lam mtx14.
      lam mtx25.
        lam i19.
          extArrSetExn mtx25.arr i19 (f25 (extArrGetExn mtx14.arr i19))
in
let matMap: all x179. (Float -> Float) -> Mat Float -> Mat Float =
  lam f24: Float -> Float.
    lam mtx13: Mat Float.
      let mtx24 = matCopy mtx13 in
      let #var"12" = repeati (anon9 f24 mtx13 mtx24) (muli mtx13.m mtx13.n)
      in
      mtx24
in
let anon10: Mat Float -> [Float] -> Mat Float -> Int -> Int -> () =
  lam mtx12.
    lam sums2.
      lam mtx23.
        lam i18.
          lam j1.
            matSetExn
              mtx23 i18 j1 (divf (matGetExn mtx12 i18 j1) (get sums2 i18))
in
let anon11: Mat Float -> [Float] -> Mat Float -> Int -> () =
  lam mtx11.
    lam sums1.
      lam mtx22.
        lam i17.
          repeati (anon10 mtx11 sums1 mtx22 i17) mtx11.n
in
let matNormalizeRows: Mat Float -> Mat Float =
  lam mtx10: Mat Float.
    let sums =
      extArrToSeq
        (matMulExn
           mtx10
           (matFromArrExn mtx10.m 1 (extArrOfSeq extArrKindFloat64 (make mtx10.m 1.)))).arr
    in
    let mtx21 = matCopy mtx10 in
    let #var"11" = repeati (anon11 mtx10 sums mtx21) mtx10.m in
    mtx21
in
let anon12: Float -> Float =
  lam f23.
    match gtf f23 0. with true
    then
      f23
    else
      0.
in
let matExpRateSafe: Mat Float -> Mat Float =
  lam mtx9: Mat Float.
    matNormalizeRows (matMap anon12 (matExpExn mtx9))
in
let anon13: Matrix Float -> Int -> Float -> Float =
  lam t4.
    lam i16.
      lam acc11.
        addf acc11 (extArrGetExn t4.arr i16)
in
let matMean =
  lam t3.
    let sum2 = _iterateni (muli t3.m t3.n) (anon13 t3) 0. in
    divf sum2 (int2float (muli t3.m t3.n))
in
let anon14: all a45. Mat a45 -> Int -> Mat a45 -> Int -> Int -> () =
  lam matrix1.
    lam r4.
      lam new1.
        lam i15.
          lam c.
            matSetExn new1 0 i15 (matGetExn matrix1 r4 (subi c 1))
in
let matRowCols =
  lam matrix.
    lam row2.
      lam cols2.
        let r3 = subi row2 1 in
        let new =
          matMakeUninit (externalExtArrKind matrix.arr) 1 (length cols2)
        in
        let #var"10" = iteri1 (anon14 matrix r3 new) cols2 in
        new
in
type Matrix #var"X" =
  Mat #var"X" in
let x: all #var"B13". all #var"A13". (Int -> #var"A13" -> #var"B13") -> Int -> #var"A13" -> #var"B13" =
  lam f22.
    lam i14.
      lam x177: #var"A13".
        let x178: #var"B13" = f22 (addi i14 1) x177 in
        x178
in
let x1: all #var"B12". all #var"A12". (#var"A12" -> #var"B12" -> #var"A12") -> #var"A12" -> #var"B12" -> #var"A12" =
  lam f21.
    lam a44.
      lam b11: #var"B12".
        let x176: #var"A12" = f21 a44 b11 in
        x176
in
let x2: all #var"B11". all #var"A11". (#var"A11" -> Int -> #var"B11" -> #var"A11") -> #var"A11" -> Int -> #var"B11" -> #var"A11" =
  lam f20.
    lam a43.
      lam idx10.
        lam b10: #var"B11".
          let x175: #var"A11" = f20 a43 (addi idx10 1) b10 in
          x175
in
let x3: all #var"B10". all #var"A10". (#var"A10" -> Int -> #var"B10" -> #var"A10") -> #var"A10" -> Int -> #var"B10" -> #var"A10" =
  lam f19.
    lam a42.
      lam idx9: Int.
        x2 f19 a42 idx9
in
let x4: all #var"C2". all #var"B9". all #var"A9". (#var"A9" -> #var"B9" -> #var"C2") -> #var"A9" -> #var"B9" -> #var"C2" =
  lam f18.
    lam a41.
      lam b9: #var"B9".
        let x174: #var"C2" = f18 a41 b9 in
        x174
in
let x5: all #var"X13". (#var"X13" -> #var"X13" -> Int) -> #var"X13" -> #var"X13" -> Int =
  lam cmp3.
    lam a40.
      lam b8: #var"X13".
        let x173: Int = cmp3 a40 b8 in
        x173
in
let ifCont = lam acc10.
    lam #var"9": Int.
      acc10 in
let ifCont1 = lam #var"8": Int.
    0. in
let exp1: Float -> Float = lam x172: Float.
    mathExp x172 in
let log1: Float -> Float = lam x171: Float.
    mathLog x171 in
let isNaN1: Float -> Bool = lam r2: Float.
    mathIsNaN r2 in
let cons1: all #var"X12". #var"X12" -> [#var"X12"] -> [#var"X12"] =
  lam e2: #var"X12".
    lam s11: [#var"X12"].
      seqCons e2 s11
in
let rep: all #var"X11". Int -> #var"X11" -> [#var"X11"] =
  lam count1: Int.
    lam elem1: #var"X11".
      make count1 elem1
in
let anon15: all #var"X10". (Int -> #var"X10") -> Int -> #var"X10" =
  lam f17.
    lam idx8: Int.
      let x170: #var"X10" = f17 (addi idx8 1) in
      x170
in
let repApply: all #var"X9". Int -> (Int -> #var"X9") -> [#var"X9"] =
  lam count: Int.
    lam f16: Int -> #var"X9".
      seqCreate count (anon15 f16)
in
let paste0: all #var"X8". [[#var"X8"]] -> [#var"X8"] = lam l5: [[#var"X8"]].
    join l5
in
let slice: all #var"X7". [#var"X7"] -> Int -> Int -> [#var"X7"] =
  lam l4: [#var"X7"].
    lam first: Int.
      lam last: Int.
        seqSubsequence l4 (subi first 1) (subi last first)
in
let length1: all #var"X6". [#var"X6"] -> Int = lam l3: [#var"X6"].
    seqLength l3
in
let sapply: all #var"A8". all #var"B8". [#var"A8"] -> (#var"A8" -> #var"B8") -> [#var"B8"] =
  lam s10: [#var"A8"].
    lam f15: #var"A8" -> #var"B8".
      seqMap f15 s10
in
let anon16: all #var"B7". all #var"A7". (Int -> #var"A7" -> #var"B7") -> Int -> #var"A7" -> #var"B7" = lam f14.
    lam i13: Int.
      x f14 i13
in
let sapplyi: all #var"A6". all #var"B6". [#var"A6"] -> (Int -> #var"A6" -> #var"B6") -> [#var"B6"] =
  lam s9: [#var"A6"].
    lam f13: Int -> #var"A6" -> #var"B6".
      seqMapi (anon16 f13) s9
in
let anon17: all #var"B5". all #var"A5". (#var"A5" -> #var"B5" -> #var"A5") -> #var"A5" -> #var"B5" -> #var"A5" = lam f12.
    lam a39: #var"A5".
      x1 f12 a39
in
let fold: all #var"A4". all #var"B4". (#var"A4" -> #var"B4" -> #var"A4") -> #var"A4" -> [#var"B4"] -> #var"A4" =
  lam f11: #var"A4" -> #var"B4" -> #var"A4".
    lam init1: #var"A4".
      lam seq5: [#var"B4"].
        seqFoldl (anon17 f11) init1 seq5
in
let anon18: all #var"B3". all #var"A3". (#var"A3" -> Int -> #var"B3" -> #var"A3") -> #var"A3" -> Int -> #var"B3" -> #var"A3" = lam f10.
    lam a38: #var"A3".
      x3 f10 a38
in
let foldi: all #var"A2". all #var"B2". (#var"A2" -> Int -> #var"B2" -> #var"A2") -> #var"A2" -> [#var"B2"] -> #var"A2" =
  lam f9: #var"A2" -> Int -> #var"B2" -> #var"A2".
    lam init: #var"A2".
      lam seq4: [#var"B2"].
        seqFoldli (anon18 f9) init seq4
in
let anon19: all #var"C1". all #var"B1". all #var"A1". (#var"A1" -> #var"B1" -> #var"C1") -> #var"A1" -> #var"B1" -> #var"C1" = lam f8.
    lam a37: #var"A1".
      x4 f8 a37
in
let zipWith1: all #var"A". all #var"B". all #var"C". (#var"A" -> #var"B" -> #var"C") -> [#var"A"] -> [#var"B"] -> [#var"C"] =
  lam f7: #var"A" -> #var"B" -> #var"C".
    lam a36: [#var"A"].
      lam b7: [#var"B"].
        seqZipWith (anon19 f7) a36 b7
in
let anon20: Float -> Float -> Float =
  lam a35: Float.
    lam b6: Float.
      let x169: Float = addf a35 b6 in
      x169
in
let seqSumReal: [Float] -> Float = lam s8: [Float].
    fold anon20 0. s8
in
let anon21: Float -> Float -> Float =
  lam sum1.
    lam x167: Float.
      let x168: Float = divf x167 sum1 in
      x168
in
let seqNormalize: [Float] -> [Float] =
  lam s7: [Float].
    let sum = seqSumReal s7 in
    sapply s7 (anon21 sum)
in
let any1: all #var"X5". (#var"X5" -> Bool) -> [#var"X5"] -> Bool =
  lam f6: #var"X5" -> Bool.
    lam l2: [#var"X5"].
      seqAny f6 l2
in
let anon22: all #var"X4". (#var"X4" -> #var"X4" -> Int) -> #var"X4" -> #var"X4" -> Int = lam cmp2.
    lam a34: #var"X4".
      x5 cmp2 a34
in
let qSort: all #var"X3". (#var"X3" -> #var"X3" -> Int) -> [#var"X3"] -> [#var"X3"] =
  lam cmp1: #var"X3" -> #var"X3" -> Int.
    lam l1: [#var"X3"].
      quickSort (anon22 cmp1) l1
in
let anon23: [Int] -> Int -> Bool -> [Int] =
  lam acc9: [Int].
    lam idx7: Int.
      lam elem: Bool.
        let x166: [Int] =
          match elem with true
          then
            seqSnoc acc9 idx7
          else
            ifCont acc9 0
        in
        x166
in
let whichTrue: [Bool] -> [Int] = lam s6: [Bool].
    foldi anon23 "" s6
in
let bool2real: Bool -> Float =
  lam v: Bool.
    match v with true
    then
      1.
    else
      ifCont1 0
in
let anon24: Int -> Int -> Float =
  lam index1.
    lam i12: Int.
      let x165: Float = bool2real (eqi index1 i12) in
      x165
in
let kroneckerDelta: Int -> Int -> [Float] =
  lam index: Int.
    lam length2: Int.
      repApply length2 (anon24 index)
in
let mtxCreate: Int -> Int -> [Float] -> Matrix Float =
  lam rows: Int.
    lam cols1: Int.
      lam data: [Float].
        matFromArrExn rows cols1 (extArrOfSeq extArrKindFloat64 data)
in
let mtxGet: all #var"X2". Int -> Int -> Matrix #var"X2" -> #var"X2" =
  lam row1: Int.
    lam col: Int.
      lam mtx8: Matrix #var"X2".
        matGetExn mtx8 (subi row1 1) (subi col 1)
in
let mtxRowCols: all #var"X1". Matrix #var"X1" -> Int -> [Int] -> Matrix #var"X1" =
  lam mtx7: Matrix #var"X1".
    lam row: Int.
      lam cols: [Int].
        matRowCols mtx7 row cols
in
let mtxSclrMul: Float -> Matrix Float -> Matrix Float =
  lam scalar: Float.
    lam mtx6: Matrix Float.
      matScale scalar mtx6
in
let mtxTrans: Matrix Float -> Matrix Float = lam mtx5: Matrix Float.
    matTranspose mtx5
in
let mtxExp: Matrix Float -> Matrix Float = lam mtx4: Matrix Float.
    matExpExn mtx4
in
let mtxExpRateSafe: Matrix Float -> Matrix Float = lam mtx3: Matrix Float.
    matExpRateSafe mtx3
in
let mtxMul: Matrix Float -> Matrix Float -> Matrix Float =
  lam a33: Matrix Float.
    lam b5: Matrix Float.
      matMulExn a33 b5
in
let mtxElemMul: Matrix Float -> Matrix Float -> Matrix Float =
  lam a32: Matrix Float.
    lam b4: Matrix Float.
      matElemMulExn a32 b4
in
let mtxMean: Matrix Float -> Float = lam mtx2: Matrix Float.
    matMean mtx2
in
type TreeLabeled in
type MsgTree in
type HistoryTree in
type Event in
type CorrectedBranchSample in
type ModelParams in
type EmbeddedMarkovChainMatrix in
con Leaf: {age: Float, label: Int} -> TreeLabeled in
con Node: {age: Float, left: TreeLabeled, label: Int, right: TreeLabeled} -> TreeLabeled
in
con MsgLeaf: {age: Float, label: Int, outMsg: Matrix Float, interactions: [Int]} -> MsgTree
in
con MsgNode: {age: Float, left: MsgTree, label: Int, right: MsgTree, outMsg: Matrix Float, leftInMsg: Matrix Float, leftKernel: Matrix Float, rightInMsg: Matrix Float, rightKernel: Matrix Float} -> MsgTree
in
con HistoryLeaf: {age: Float, label: Int, history: [Event], repertoire: [Int]} -> HistoryTree
in
con HistoryNode: {age: Float, left: HistoryTree, label: Int, right: HistoryTree, history: [Event], repertoire: [Int]} -> HistoryTree
in
con Event1: {host: Int, toState: Int, eventTime: Float, fromState: Int} -> Event
in
con CorrectedBranchSample1: {history: [Event], success: Bool, logModelDensity: Float, logSamplingDensity: Float} -> CorrectedBranchSample
in
con ModelParams1: {beta: Float, hostMetric: Matrix Float, embeddedQMatrix: EmbeddedMarkovChainMatrix} -> ModelParams
in
con EmbeddedMarkovChainMatrix1: {mat: Matrix Float, totalRates: [Float], transitionProbs: [[Float]]} -> EmbeddedMarkovChainMatrix
in
let anon25: Float -> Float -> Float =
  lam meanDist2.
    lam e1: Float.
      let x164: Float = divf e1 meanDist2 in
      x164
in
let anon26: Float -> [Float] -> [Float] =
  lam meanDist1.
    lam s5: [Float].
      let x163: [Float] = sapply s5 (anon25 meanDist1) in
      x163
in
let normalizeHostMetric: [[Float]] -> [[Float]] =
  lam hostMetric: [[Float]].
    let summedPairWiseDists = seqSumReal (paste0 hostMetric) in
    let n2 = length1 hostMetric in
    let meanDist = divf summedPairWiseDists (int2float (muli n2 (subi n2 1)))
    in
    sapply hostMetric (anon26 meanDist)
in
let rateMatrixToEmbeddedMarkovChain: Matrix Float -> EmbeddedMarkovChainMatrix =
  lam qMatrix4: Matrix Float.
    let q1 = negf (mtxGet 1 1 qMatrix4) in
    let q2 = negf (mtxGet 2 2 qMatrix4) in
    let q3 = negf (mtxGet 3 3 qMatrix4) in
    EmbeddedMarkovChainMatrix1
      { totalRates = [ q1,
            q2,
            q3 ],
        transitionProbs =
          [ [ 0., 1., 0. ],
            [ divf (mtxGet 2 1 qMatrix4) q2,
              0.,
              divf (mtxGet 2 3 qMatrix4) q2 ],
            [ 0., 1., 0. ] ],
        mat = qMatrix4 }
in
let nestSeqToMtx: [[Float]] -> Matrix Float =
  lam ns: [[Float]].
    let n1 = length1 ns in
    let m = length1 (get ns (subi 1 1)) in
    mtxCreate n1 m (paste0 ns)
in
let makeStateMessage: Int -> [Float] =
  lam interaction: Int.
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
let observationMessage: [Int] -> Matrix Float =
  lam obsRepertoire: [Int].
    mtxCreate
      (length1 obsRepertoire)
      3
      (paste0 (sapply obsRepertoire makeStateMessage))
in
recursive
  let ifCont2 =
    lam tree.
      lam qMatrix.
        lam interactions.
          lam nhosts.
            lam #var"1": Int.
              let left =
                postorderTraverse
                  (let target9 = tree in
                   match target9 with Node x23
                   then
                     x23.left
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 18:31-18:40>:\nField \'left\' not found\n[0m  let left = postorderTraverse([31mtree.left[0m[0m, qMatrix, interactions, nhosts);\n"
                     in
                     exit 1)
                  qMatrix
                  interactions
                  nhosts
              in
              let right =
                postorderTraverse
                  (let target8 = tree in
                   match target8 with Node x22
                   then
                     x22.right
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 19:32-19:42>:\nField \'right\' not found\n[0m  let right = postorderTraverse([31mtree.right[0m[0m, qMatrix, interactions, nhosts);\n"
                     in
                     exit 1)
                  qMatrix
                  interactions
                  nhosts
              in
              let leftKernel =
                mtxExpRateSafe
                  (mtxSclrMul
                     (subf
                        (let target6 = tree in
                         match target6 with Node x18
                         then
                           x18.age
                         else match target6 with Leaf x19
                         then
                           x19.age
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 22:45-22:53>:\nField \'age\' not found\n[0m  let leftKernel = mtxExpRateSafe(mtxSclrMul([31mtree.age[0m[0m-left.age, qMatrix));\n"
                           in
                           exit 1)
                        (let target7 = left in
                         match target7 with MsgNode x20
                         then
                           x20.age
                         else match target7 with MsgLeaf x21
                         then
                           x21.age
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 22:54-22:62>:\nField \'age\' not found\n[0m  let leftKernel = mtxExpRateSafe(mtxSclrMul(tree.age-[31mleft.age[0m[0m, qMatrix));\n"
                           in
                           exit 1))
                     qMatrix)
              in
              let rightKernel =
                mtxExpRateSafe
                  (mtxSclrMul
                     (subf
                        (let target4 = tree in
                         match target4 with Node x14
                         then
                           x14.age
                         else match target4 with Leaf x15
                         then
                           x15.age
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:46-23:54>:\nField \'age\' not found\n[0m  let rightKernel = mtxExpRateSafe(mtxSclrMul([31mtree.age[0m[0m-right.age, qMatrix));\n"
                           in
                           exit 1)
                        (let target5 = right in
                         match target5 with MsgNode x16
                         then
                           x16.age
                         else match target5 with MsgLeaf x17
                         then
                           x17.age
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:55-23:64>:\nField \'age\' not found\n[0m  let rightKernel = mtxExpRateSafe(mtxSclrMul(tree.age-[31mright.age[0m[0m, qMatrix));\n"
                           in
                           exit 1))
                     qMatrix)
              in
              let leftBackwardKernel = mtxTrans leftKernel in
              let rightBackwardKernel = mtxTrans rightKernel in
              let leftInMsg =
                mtxMul
                  (let target3 = left in
                   match target3 with MsgNode x12
                   then
                     x12.outMsg
                   else match target3 with MsgLeaf x13
                   then
                     x13.outMsg
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 29:25-29:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n"
                     in
                     exit 1)
                  leftBackwardKernel
              in
              let rightInMsg =
                mtxMul
                  (let target2 = right in
                   match target2 with MsgNode x10
                   then
                     x10.outMsg
                   else match target2 with MsgLeaf x11
                   then
                     x11.outMsg
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:26-30:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n"
                     in
                     exit 1)
                  rightBackwardKernel
              in
              let outMsg = mtxElemMul leftInMsg rightInMsg in
              MsgNode
                { age =
                    let target = tree in
                    match target with Node x6
                    then
                      x6.age
                    else match target with Leaf x7
                    then
                      x7.age
                    else
                      let #var"2" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 35:10-35:18>:\nField \'age\' not found\n[0m    age = [31mtree.age[0m[0m, label = tree.label,\n"
                      in
                      exit 1,
                  left = left,
                  right = right,
                  label =
                    let target1 = tree in
                    match target1 with Node x8
                    then
                      x8.label
                    else match target1 with Leaf x9
                    then
                      x9.label
                    else
                      let #var"2" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 35:28-35:38>:\nField \'label\' not found\n[0m    age = tree.age, label = [31mtree.label[0m[0m,\n"
                      in
                      exit 1,
                  outMsg = outMsg,
                  leftInMsg = leftInMsg,
                  rightInMsg = rightInMsg,
                  leftKernel = leftKernel,
                  rightKernel = rightKernel }
  let postorderTraverse: TreeLabeled -> Matrix Float -> [[Int]] -> Int -> MsgTree =
    lam tree1: TreeLabeled.
      lam qMatrix1: Matrix Float.
        lam interactions1: [[Int]].
          lam nhosts1: Int.
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
                        (let target12 = tree1 in
                         match target12 with Node x28
                         then
                           x28.label
                         else match target12 with Leaf x29
                         then
                           x29.label
                         else
                           let #var"2" =
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
                     (let target11 = tree1 in
                      match target11 with Node x26
                      then
                        x26.label
                      else match target11 with Leaf x27
                      then
                        x27.label
                      else
                        let #var"2" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 9:32-9:42>:\nField \'label\' not found\n[0m    let leafInts = interactions[[31mtree.label[0m[0m];\n"
                        in
                        exit 1)
                     1)
              in
              MsgLeaf
                { age = 0.,
                  label =
                    let target10 = tree1 in
                    match target10 with Node x24
                    then
                      x24.label
                    else match target10 with Leaf x25
                    then
                      x25.label
                    else
                      let #var"2" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 12:14-12:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                      in
                      exit 1,
                  outMsg = observationMessage leafInts,
                  interactions = leafInts }
            else
              ifCont2 tree1 qMatrix1 interactions1 nhosts1 0
in
let categoricalLogPmf: Int -> [Float] -> Float =
  lam x162: Int.
    lam param6: [Float].
      match
        match leqi 0 x162 with true
        then
          lti x162 (length1 param6)
        else
          false
      with
        true
      then
        log1 (get param6 (subi (addi x162 1) 1))
      else
        log1 0.
in
let anon27: Int -> Int -> Int = lam start13.
    lam idx6.
      addi idx6 start13
in
let anon28: Matrix Float -> Int -> Int -> Float =
  lam mtx1.
    lam i11.
      lam j: Int.
        let x161: Float = mtxGet i11 j mtx1 in
        x161
in
let hostMsgToProb: Matrix Float -> Int -> [Float] =
  lam mtx: Matrix Float.
    lam i10: Int.
      seqNormalize
        (sapply
           (let start12 = 1 in
            let end7 = 3 in
            create1 (addi (subi end7 start12) 1) (anon27 start12))
           (anon28 mtx i10))
in
let anon29: Matrix Float -> Int -> Int -> Float =
  lam samplingProb2.
    lam h4: Int.
      lam obs: Int.
        let x160: Float = categoricalLogPmf obs (hostMsgToProb samplingProb2 h4)
        in
        x160
in
let getRepertoireSamplingDensity: [Int] -> Matrix Float -> Float =
  lam x159: [Int].
    lam samplingProb1: Matrix Float.
      seqSumReal (sapplyi x159 (anon29 samplingProb1))
in
let anon30: Int -> Int -> Int =
  lam acc8: Int.
    lam h3: Int.
      let x158: Int =
        match eqi h3 2 with true
        then
          addi acc8 1
        else
          acc8
      in
      x158
in
let count2s: [Int] -> Int = lam repertoire2: [Int].
    fold anon30 0 repertoire2
in
let updateRepertoire: [Int] -> Event -> Int -> [Int] =
  lam currRep8: [Int].
    lam event3: Event.
      lam nhosts7: Int.
        let hostIndex4 =
          let target94 = event3 in
          match target94 with Event1 x157
          then
            x157.host
          else
            let #var"2" =
              print
                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 169:18-169:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
            in
            exit 1
        in
        paste0
          [ slice currRep8 1 hostIndex4,
            [ let target93 = event3 in
              match target93 with Event1 x156
              then
                x156.toState
              else
                let #var"2" =
                  print
                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 173:7-173:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                in
                exit 1 ],
            slice currRep8 (addi hostIndex4 1) (addi nhosts7 1) ]
in
recursive
  let ifCont3 =
    lam currRep.
      lam eventSeq.
        lam eventIndex.
          lam nEvents.
            lam nhosts2.
              lam event.
                lam #var"3": Int.
                  let newRep = updateRepertoire currRep event nhosts2 in
                  allTimesValidBranch newRep eventSeq (addi eventIndex 1) nEvents nhosts2
  let allTimesValidBranch: [Int] -> [Event] -> Int -> Int -> Int -> Bool =
    lam currRep1: [Int].
      lam eventSeq1: [Event].
        lam eventIndex1: Int.
          lam nEvents1: Int.
            lam nhosts3: Int.
              match gti eventIndex1 nEvents1 with true
              then
                true
              else
                let event1 = get eventSeq1 (subi eventIndex1 1) in
                match
                  eqi
                    (let target13 = event1 in
                     match target13 with Event1 x30
                     then
                       x30.fromState
                     else
                       let #var"2" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 144:7-144:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                       in
                       exit 1)
                    2
                with
                  true
                then
                  match eqi (count2s currRep1) 1 with true
                  then
                    false
                  else
                    ifCont4 currRep1 eventSeq1 eventIndex1 nEvents1 nhosts3 event1 0
                else
                  ifCont3 currRep1 eventSeq1 eventIndex1 nEvents1 nhosts3 event1 0
  let ifCont4 =
    lam currRep2.
      lam eventSeq2.
        lam eventIndex2.
          lam nEvents2.
            lam nhosts4.
              lam event2.
                lam #var"4": Int.
                  ifCont3 currRep2 eventSeq2 eventIndex2 nEvents2 nhosts4 event2 0
in
let anon31: Int -> Bool =
  lam i9: Int.
    let x155: Bool =
      match eqi i9 2 with true
      then
        true
      else
        eqi i9 1
    in
    x155
in
let anon32: Int -> Bool = lam i8: Int.
    let x154: Bool = eqi i8 2 in
    x154
in
let getGainRate: [Int] -> Int -> ModelParams -> Float =
  lam repertoire1: [Int].
    lam hostIndex3: Int.
      lam modelParams12: ModelParams.
        let fromState5 = get repertoire1 (subi hostIndex3 1) in
        let toState3 = addi fromState5 1 in
        let baseRate1 =
          mtxGet
            (addi fromState5 1)
            (addi toState3 1)
            (let target91 =
               let target92 = modelParams12 in
               match target92 with ModelParams1 x153
               then
                 x153.embeddedQMatrix
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                 in
                 exit 1
             in
             match target91 with EmbeddedMarkovChainMatrix1 x152
             then
               x152.mat
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 110:52-110:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
               in
               exit 1)
        in
        match eqi fromState5 0 with true
        then
          let currentHosts = whichTrue (sapply repertoire1 anon31) in
          let dist =
            mtxMean
              (mtxRowCols
                 (let target88 = modelParams12 in
                  match target88 with ModelParams1 x149
                  then
                    x149.hostMetric
                  else
                    let #var"2" =
                      print
                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 119:6-119:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                    in
                    exit 1)
                 hostIndex3
                 currentHosts)
          in
          mulf
            baseRate1
            (pow
               dist
               (negf
                  (let target87 = modelParams12 in
                   match target87 with ModelParams1 x148
                   then
                     x148.beta
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 121:30-121:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                     in
                     exit 1)))
        else
          let currentHosts1 = whichTrue (sapply repertoire1 anon32) in
          let dist1 =
            mtxMean
              (mtxRowCols
                 (let target90 = modelParams12 in
                  match target90 with ModelParams1 x151
                  then
                    x151.hostMetric
                  else
                    let #var"2" =
                      print
                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 128:6-128:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                    in
                    exit 1)
                 hostIndex3
                 currentHosts1)
          in
          mulf
            baseRate1
            (pow
               dist1
               (negf
                  (let target89 = modelParams12 in
                   match target89 with ModelParams1 x150
                   then
                     x150.beta
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 130:30-130:46>:\nField \'beta\' not found\n[0m    return baseRate * (dist^(-[31mmodelParams.beta[0m[0m));\n"
                     in
                     exit 1)))
in
let anon33: [Int] -> ModelParams -> Float -> Int -> Float =
  lam currRep7.
    lam modelParams11.
      lam acc7: Float.
        lam i7: Int.
          let x147: Float =
            let fromState4 = get currRep7 (subi i7 1) in
            match eqi fromState4 2 with true
            then
              acc7
            else
              addf acc7 (getGainRate currRep7 i7 modelParams11)
          in
          x147
in
let anon34: Int -> Int -> Int = lam start11.
    lam idx5.
      addi idx5 start11
in
let getLossRate: [Int] -> Int -> ModelParams -> Float =
  lam repertoire: [Int].
    lam hostIndex2: Int.
      lam modelParams10: ModelParams.
        let fromState3 = get repertoire (subi hostIndex2 1) in
        match
          match eqi fromState3 2 with true
          then
            eqi (count2s repertoire) 1
          else
            false
        with
          true
        then
          0.
        else
          let toState2 = subi fromState3 1 in
          let baseRate =
            mtxGet
              (addi fromState3 1)
              (addi toState2 1)
              (let target85 =
                 let target86 = modelParams10 in
                 match target86 with ModelParams1 x146
                 then
                   x146.embeddedQMatrix
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                   in
                   exit 1
               in
               match target85 with EmbeddedMarkovChainMatrix1 x145
               then
                 x145.mat
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 98:54-98:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                 in
                 exit 1)
          in
          baseRate
in
let anon35: [Int] -> ModelParams -> Float -> Int -> Float =
  lam currRep6.
    lam modelParams9.
      lam acc6: Float.
        lam i6: Int.
          let x144: Float =
            let fromState2 = get currRep6 (subi i6 1) in
            match eqi fromState2 0 with true
            then
              acc6
            else
              addf acc6 (getLossRate currRep6 i6 modelParams9)
          in
          x144
in
let anon36: Int -> Int -> Int = lam start10.
    lam idx4.
      addi idx4 start10
in
let getTotalRate: [Int] -> ModelParams -> Int -> Float =
  lam currRep5: [Int].
    lam modelParams8: ModelParams.
      lam nhosts6: Int.
        let gainRates =
          fold
            (anon33 currRep5 modelParams8)
            0.
            (let start9 = 1 in
             let end6 = nhosts6 in
             create1 (addi (subi end6 start9) 1) (anon34 start9))
        in
        let lossRates =
          fold
            (anon35 currRep5 modelParams8)
            0.
            (let start8 = 1 in
             let end5 = nhosts6 in
             create1 (addi (subi end5 start8) 1) (anon36 start8))
        in
        addf gainRates lossRates
in
let getRate: [Int] -> Event -> ModelParams -> Float =
  lam currRep4: [Int].
    lam nextEvent2: Event.
      lam modelParams7: ModelParams.
        let hostIndex1 =
          let target84 = nextEvent2 in
          match target84 with Event1 x143
          then
            x143.host
          else
            let #var"2" =
              print
                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 81:18-81:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
            in
            exit 1
        in
        match
          gti
            (let target82 = nextEvent2 in
             match target82 with Event1 x141
             then
               x141.fromState
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:5-82:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
               in
               exit 1)
            (let target83 = nextEvent2 in
             match target83 with Event1 x142
             then
               x142.toState
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 82:27-82:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
               in
               exit 1)
        with
          true
        then
          getLossRate currRep4 hostIndex1 modelParams7
        else
          getGainRate currRep4 hostIndex1 modelParams7
in
recursive
  let fullModelWeight: Int -> [Int] -> [Int] -> Float -> Float -> [Event] -> Int -> Int -> ModelParams -> Float =
    lam nextIndex: Int.
      lam currRep3: [Int].
        lam finalRep: [Int].
          lam currAge: Float.
            lam finalAge: Float.
              lam eventSeq3: [Event].
                lam nEvents3: Int.
                  lam nhosts5: Int.
                    lam modelParams: ModelParams.
                      match gti nextIndex nEvents3 with true
                      then
                        let timePassed = subf currAge finalAge in
                        let totalLeavingRate = getTotalRate currRep3 modelParams nhosts5
                        in
                        mulf (negf timePassed) totalLeavingRate
                      else
                        let nextEvent = get eventSeq3 (subi nextIndex 1) in
                        let newAge =
                          let target14 = nextEvent in
                          match target14 with Event1 x31
                          then
                            x31.eventTime
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 25:17-25:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
                            in
                            exit 1
                        in
                        let totalLeavingRate1 = getTotalRate currRep3 modelParams nhosts5
                        in
                        let thisRate = getRate currRep3 nextEvent modelParams in
                        let timePassed1 = subf currAge newAge in
                        let thisWeight =
                          subf
                            (log1 (divf thisRate totalLeavingRate1))
                            (mulf timePassed1 totalLeavingRate1)
                        in
                        let newRep1 = updateRepertoire currRep3 nextEvent nhosts5 in
                        addf
                          thisWeight
                          (fullModelWeight
                             (addi nextIndex 1)
                             newRep1
                             finalRep
                             newAge
                             finalAge
                             eventSeq3
                             nEvents3
                             nhosts5
                             modelParams)
in
recursive
  let hostIndepLikelihood: Int -> Int -> Int -> Float -> Float -> [Event] -> EmbeddedMarkovChainMatrix -> Float =
    lam nextIndex1: Int.
      lam currState: Int.
        lam finalState: Int.
          lam currAge1: Float.
            lam finalAge1: Float.
              lam eventSeq4: [Event].
                lam embeddedQMatrix: EmbeddedMarkovChainMatrix.
                  match gti nextIndex1 (length1 eventSeq4) with true
                  then
                    let timePassed2 = subf currAge1 finalAge1 in
                    let outRate =
                      get
                        (let target15 = embeddedQMatrix in
                         match target15 with EmbeddedMarkovChainMatrix1 x32
                         then
                           x32.totalRates
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 79:18-79:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                           in
                           exit 1)
                        (subi (addi currState 1) 1)
                    in
                    mulf (negf timePassed2) outRate
                  else
                    let nextEvent1 = get eventSeq4 (subi nextIndex1 1) in
                    let nextState =
                      let target19 = nextEvent1 in
                      match target19 with Event1 x36
                      then
                        x36.toState
                      else
                        let #var"2" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 83:20-83:37>:\nField \'toState\' not found\n[0m    let nextState = [31mnextEvent.toState[0m[0m;\n"
                        in
                        exit 1
                    in
                    let nextAge =
                      let target18 = nextEvent1 in
                      match target18 with Event1 x35
                      then
                        x35.eventTime
                      else
                        let #var"2" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 84:18-84:37>:\nField \'eventTime\' not found\n[0m    let nextAge = [31mnextEvent.eventTime[0m[0m;\n"
                        in
                        exit 1
                    in
                    let timePassed3 = subf currAge1 nextAge in
                    let outRate1 =
                      get
                        (let target17 = embeddedQMatrix in
                         match target17 with EmbeddedMarkovChainMatrix1 x34
                         then
                           x34.totalRates
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 86:18-86:44>:\nField \'totalRates\' not found\n[0m    let outRate = [31membeddedQMatrix.totalRates[0m[0m[currState + 1];\n"
                           in
                           exit 1)
                        (subi (addi currState 1) 1)
                    in
                    let transProb =
                      get
                        (get
                           (let target16 = embeddedQMatrix in
                            match target16 with EmbeddedMarkovChainMatrix1 x33
                            then
                              x33.transitionProbs
                            else
                              let #var"2" =
                                print
                                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 87:20-87:51>:\nField \'transitionProbs\' not found\n[0m    let transProb = [31membeddedQMatrix.transitionProbs[0m[0m[currState + 1][nextState + 1];\n"
                              in
                              exit 1)
                           (subi (addi currState 1) 1))
                        (subi (addi nextState 1) 1)
                    in
                    addf
                      (subf (log1 transProb) (mulf timePassed3 outRate1))
                      (hostIndepLikelihood
                         (addi nextIndex1 1)
                         nextState
                         finalState
                         nextAge
                         finalAge1
                         eventSeq4
                         embeddedQMatrix)
in
let anon37: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Float -> Int -> Float =
  lam fromRep2.
    lam toRep2.
      lam fromAge2.
        lam toAge2.
          lam eventSeqs2.
            lam modelParams6.
              lam acc5: Float.
                lam h2: Int.
                  let x139: Float =
                    let eventSeq5 = get eventSeqs2 (subi h2 1) in
                    let fromState1 = get fromRep2 (subi h2 1) in
                    let toState1 = get toRep2 (subi h2 1) in
                    addf
                      acc5
                      (hostIndepLikelihood
                         1
                         fromState1
                         toState1
                         fromAge2
                         toAge2
                         eventSeq5
                         (let target81 = modelParams6 in
                          match target81 with ModelParams1 x140
                          then
                            x140.embeddedQMatrix
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                            in
                            exit 1))
                  in
                  x139
in
let anon38: Int -> Int -> Int = lam start7.
    lam idx3.
      addi idx3 start7
in
let independenceLikelihood: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Float =
  lam fromRep1: [Int].
    lam toRep1: [Int].
      lam fromAge1: Float.
        lam toAge1: Float.
          lam eventSeqs1: [[Event]].
            lam modelParams5: ModelParams.
              let unconditional1 =
                fold
                  (anon37 fromRep1 toRep1 fromAge1 toAge1 eventSeqs1 modelParams5)
                  0.
                  (let start6 = 1 in
                   let end4 = length1 eventSeqs1 in
                   create1 (addi (subi end4 start6) 1) (anon38 start6))
              in
              unconditional1
in
let anon39: Float -> Float -> Float =
  lam acc4: Float.
    lam val: Float.
      let x138: Float = addf acc4 val in
      x138
in
let anon40: Matrix Float -> Int -> Int -> Float =
  lam kernel1.
    lam fromState: Int.
      lam toState: Int.
        let x137: Float = log1 (mtxGet (addi fromState 1) (addi toState 1) kernel1)
        in
        x137
in
let independenceLikelihoodEndCond: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Matrix Float -> Float =
  lam fromRep: [Int].
    lam toRep: [Int].
      lam fromAge: Float.
        lam toAge: Float.
          lam eventSeqs: [[Event]].
            lam modelParams4: ModelParams.
              lam kernel: Matrix Float.
                let unconditional =
                  independenceLikelihood fromRep toRep fromAge toAge eventSeqs modelParams4
                in
                let logTotalTransProb = fold anon39 0. (zipWith1 (anon40 kernel) fromRep toRep)
                in
                let conditional = subf unconditional logTotalTransProb in
                conditional
in
let newParamFun =
  lam alpha2.
    lam epsilon1.
      lam a31: Float.
        let x136: Float =
          match gtf a31 epsilon1 with true
          then
            match ltf a31 (subf 1. epsilon1) with true
            then
              mulf a31 alpha2
            else
              mulf (subf a31 epsilon1) alpha2
          else
            mulf (addf a31 epsilon1) alpha2
        in
        x136
in
let simplexMove: [Float] -> Float -> Float -> Dist([Float]) =
  lam x135: [Float].
    lam alpha1: Float.
      lam epsilon: Float.
        let newParams = sapply x135 (newParamFun alpha1 epsilon) in
        Dirichlet newParams
in
let scaleMove: Float -> Float -> Dist(Float) =
  lam x134: Float.
    lam lambda6: Float.
      Reciprocal
        (mulf x134 (exp1 (divf (negf lambda6) 2.)))
        (mulf x134 (exp1 (divf lambda6 2.)))
in
let anon41: Int -> Int -> Int = lam start5.
    lam idx2.
      addi idx2 start5
in
let anon42: Int -> [Float] -> Float -> Float -> Int -> Float =
  lam x132.
    lam param5.
      lam currProb1.
        lam nextProb1.
          lam i5: Int.
            let x133: Float =
              match eqi i5 x132 with true
              then
                nextProb1
              else
                divf
                  (mulf (get param5 (subi (addi i5 1) 1)) (subf 1. nextProb1))
                  (subf 1. currProb1)
            in
            x133
in
let categoricalShiftKernel: Int -> [Float] -> Float -> Float -> Dist(Int) =
  lam x131: Int.
    lam param4: [Float].
      lam lambda5: Float.
        lam errMargin1: Float.
          let currProb = get param4 (subi (addi x131 1) 1) in
          match ltf currProb (subf 1. errMargin1) with true
          then
            let nextProb = mulf currProb (subf 1. lambda5) in
            let newParam =
              sapply
                (let start4 = 1 in
                 let end3 = length1 param4 in
                 create1 (addi (subi end3 start4) 1) (anon41 start4))
                (anon42 x131 param4 currProb nextProb)
            in
            Categorical newParam
          else
            Categorical param4
in
let rbLambdaMove: [Float] -> Dist([Float]) =
  lam x130: [Float].
    let _EPSILON = 0.001 in
    let alpha = 25. in
    simplexMove x130 alpha _EPSILON
in
let rbBetaMove: Float -> Dist(Float) =
  lam x129: Float.
    let lambda4 = 1. in
    scaleMove x129 lambda4
in
let rbMuMove: Float -> Dist(Float) =
  lam x128: Float.
    let lambda3 = 0.2 in
    scaleMove x128 lambda3
in
let categoricalMove: Int -> [Float] -> Dist(Int) =
  lam x127: Int.
    lam param3: [Float].
      let lambda2 = 0.9 in
      let errMargin = 1e-06 in
      categoricalShiftKernel x127 param3 lambda2 errMargin
in
type ReturnType in
type SubrootInfo in
type Bridge in
con ReturnType1: {mu: Float, beta: Float, tree: HistoryTree, lambda: [Float]} -> ReturnType
in
con SubrootInfo1: {msg: Matrix Float, rep: [Int], kernel: Matrix Float} -> SubrootInfo
in
con Bridge1: {events: [Event], success: Bool} -> Bridge in
let ifCont5 =
  lam left4.
    lam right4.
      lam #var"7": Int.
        match
          geqf
            (let target79 = right4 in
             match target79 with Event1 x125
             then
               x125.eventTime
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 301:6-301:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
               in
               exit 1)
            (let target80 = left4 in
             match target80 with Event1 x126
             then
               x126.eventTime
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 301:25-301:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
               in
               exit 1)
        with
          true
        then
          1
        else
          negi 1
in
let ifCont6 =
  lam left3.
    lam right3.
      lam #var"6": Int.
        match
          isNaN1
            (let target78 = left3 in
             match target78 with Event1 x124
             then
               x124.eventTime
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 298:12-298:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
               in
               exit 1)
        with
          true
        then
          1
        else
          ifCont5 left3 right3 0
in
let anon43: Int -> Int -> Int = lam start3.
    lam idx1.
      addi idx1 start3
in
let anon44: [Float] -> Int -> Dist(Int) = lam param2.
    lam x123.
      categoricalMove x123 param2
in
let anon45: Matrix Float -> Int -> Int -> Int =
  lam msg1.
    lam nodeLabel6.
      lam h1: Int.
        let x121: Int =
          let param1 = hostMsgToProb msg1 (addi h1 (muli nodeLabel6 0))
          in
          let x122 = assume
              (Categorical param1) in
          x122
        in
        x121
in
let suggestNodeRep: Matrix Float -> Int -> Int -> [Int] =
  lam msg: Matrix Float.
    lam nHosts5: Int.
      lam nodeLabel5: Int.
        sapply
          (let start2 = 1 in
           let end2 = nHosts5 in
           create1 (addi (subi end2 start2) 1) (anon43 start2))
          (anon45 msg nodeLabel5)
in
let is2: Int -> Bool = lam x120: Int.
    eqi x120 2 in
let subrootNode: Matrix Float -> Float -> Int -> Matrix Float -> Int -> SubrootInfo =
  lam rootMsg: Matrix Float.
    lam subrootLength1: Float.
      lam subrootLabel1: Int.
        lam qMatrix3: Matrix Float.
          lam nHosts4: Int.
            let subrootKernel = mtxExp (mtxSclrMul subrootLength1 qMatrix3)
            in
            let subrootBackwardsKernel = mtxTrans subrootKernel in
            let subRootSamplingProb = mtxMul rootMsg subrootBackwardsKernel
            in
            let subrootNodePrior = mtxCreate nHosts4 3 (rep (muli 3 nHosts4) 1.)
            in
            let subrootSamplingProb = mtxElemMul subRootSamplingProb subrootNodePrior
            in
            let subrootRep = suggestNodeRep subrootSamplingProb nHosts4 (negi 1)
            in
            let foo6 =
              weight
                (externalLog
                   (addf
                      (bool2real (any1 is2 subrootRep))
                      (mulf (int2float subrootLabel1) 0.)))
            in
            let subrootSamplingDensity = getRepertoireSamplingDensity subrootRep subrootSamplingProb
            in
            let subrootModelDensity =
              negf
                (log1
                   (subf (pow 3. (int2float nHosts4)) (pow 2. (int2float nHosts4))))
            in
            let foo7 =
              weight
                (addf
                   (subf subrootModelDensity subrootSamplingDensity)
                   (mulf (int2float subrootLabel1) 0.))
            in
            let subrootMsg = observationMessage subrootRep in
            SubrootInfo1
              { rep = subrootRep,
                msg = mtxMul subrootMsg subrootKernel,
                kernel = subrootKernel }
in
let compAge: Event -> Event -> Int =
  lam left2: Event.
    lam right2: Event.
      match
        isNaN1
          (let target77 = right2 in
           match target77 with Event1 x119
           then
             x119.eventTime
           else
             let #var"2" =
               print
                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 295:12-295:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
             in
             exit 1)
      with
        true
      then
        negi 1
      else
        ifCont6 left2 right2 0
in
let anon46: Int -> Int -> Int = lam start1.
    lam idx.
      addi idx start1
in
recursive
  let sampleHostHistoryRec: Int -> Int -> Float -> Float -> Int -> Int -> EmbeddedMarkovChainMatrix -> Bridge =
    lam currentState: Int.
      lam finalState1: Int.
        lam currentAge: Float.
          lam finalAge2: Float.
            lam host: Int.
              lam nodeLabel: Int.
                lam embeddedQMatrix1: EmbeddedMarkovChainMatrix.
                  match ltf currentAge finalAge2 with true
                  then
                    Bridge1
                      { success = eqi currentState finalState1, events = "" }
                  else
                    let param =
                      get
                        (let target23 = embeddedQMatrix1 in
                         match target23 with EmbeddedMarkovChainMatrix1 x40
                         then
                           x40.transitionProbs
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 377:16-377:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
                           in
                           exit 1)
                        (subi (addi currentState 1) 1)
                    in
                    let nextState1 = assume
                        (Categorical param)
                    in
                    let totalRate =
                      get
                        (let target22 = embeddedQMatrix1 in
                         match target22 with EmbeddedMarkovChainMatrix1 x39
                         then
                           x39.totalRates
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 381:20-381:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
                           in
                           exit 1)
                        (subi (addi nextState1 1) 1)
                    in
                    let t1 =
                      assume
                        (Exponential
                           (addf
                              (addf totalRate (mulf (int2float host) 0.))
                              (mulf (int2float nodeLabel) 0.)))
                    in
                    let restOfHistory =
                      sampleHostHistoryRec
                        nextState1
                        finalState1
                        (subf currentAge t1)
                        finalAge2
                        host
                        nodeLabel
                        embeddedQMatrix1
                    in
                    Bridge1
                      { success =
                          let target20 = restOfHistory in
                          match target20 with Bridge1 x37
                          then
                            x37.success
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 399:18-399:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
                            in
                            exit 1,
                        events =
                          cons1
                            (Event1
                               { eventTime = currentAge,
                                 fromState = currentState,
                                 toState = nextState1,
                                 host = host })
                            (let target21 = restOfHistory in
                             match target21 with Bridge1 x38
                             then
                               x38.events
                             else
                               let #var"2" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 397:10-397:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
                               in
                               exit 1) }
in
let sampleHostHistory: Int -> Int -> Float -> Float -> Int -> Int -> EmbeddedMarkovChainMatrix -> [Event] =
  lam startState: Int.
    lam finalState2: Int.
      lam startAge3: Float.
        lam finalAge6: Float.
          lam host1: Int.
            lam nodeLabel4: Int.
              lam embeddedQMatrix5: EmbeddedMarkovChainMatrix.
                let totalRate1 =
                  get
                    (let target76 = embeddedQMatrix5 in
                     match target76 with EmbeddedMarkovChainMatrix1 x118
                     then
                       x118.totalRates
                     else
                       let #var"2" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 346:18-346:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
                       in
                       exit 1)
                    (subi (addi startState 1) 1)
                in
                let t2 =
                  assume
                    (Exponential
                       (addf
                          (addf totalRate1 (mulf (int2float host1) 0.))
                          (mulf (int2float nodeLabel4) 0.)))
                in
                let eventTime = subf startAge3 t2 in
                let bridge =
                  sampleHostHistoryRec
                    startState
                    finalState2
                    eventTime
                    finalAge6
                    host1
                    nodeLabel4
                    embeddedQMatrix5
                in
                let foo5 =
                  weight
                    (externalLog
                       (addf
                          (addf
                             (bool2real
                                (let target75 = bridge in
                                 match target75 with Bridge1 x117
                                 then
                                   x117.success
                                 else
                                   let #var"2" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 358:19-358:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                                   in
                                   exit 1))
                             (mulf (int2float host1) 0.))
                          (mulf (int2float nodeLabel4) 0.)))
                in
                let target74 = bridge in
                match target74 with Bridge1 x116
                then
                  x116.events
                else
                  let #var"2" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 359:9-359:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                  in
                  exit 1
in
let anon47: [Int] -> [Int] -> Float -> Float -> Int -> EmbeddedMarkovChainMatrix -> Int -> [Event] =
  lam startRep2.
    lam finalRep3.
      lam startAge2.
        lam finalAge5.
          lam nodeLabel3.
            lam embeddedQMatrix4.
              lam hostIndex: Int.
                let x115: [Event] =
                  sampleHostHistory
                    (get startRep2 (subi hostIndex 1))
                    (get finalRep3 (subi hostIndex 1))
                    startAge2
                    finalAge5
                    hostIndex
                    nodeLabel3
                    embeddedQMatrix4
                in
                x115
in
let sampleUnorderedBranch: [Int] -> [Int] -> Float -> Float -> Int -> Int -> EmbeddedMarkovChainMatrix -> [[Event]] =
  lam startRep1: [Int].
    lam finalRep2: [Int].
      lam startAge1: Float.
        lam finalAge4: Float.
          lam nHosts3: Int.
            lam nodeLabel2: Int.
              lam embeddedQMatrix3: EmbeddedMarkovChainMatrix.
                sapply
                  (let start = 1 in
                   let end1 = nHosts3 in
                   create1 (addi (subi end1 start) 1) (anon46 start))
                  (anon47
                     startRep1
                     finalRep2
                     startAge1
                     finalAge4
                     nodeLabel2
                     embeddedQMatrix3)
in
let sampleBranch: [Int] -> [Int] -> Float -> Float -> Int -> Int -> ModelParams -> Matrix Float -> CorrectedBranchSample =
  lam startRep: [Int].
    lam finalRep1: [Int].
      lam startAge: Float.
        lam finalAge3: Float.
          lam nHosts2: Int.
            lam nodeLabel1: Int.
              lam modelParams3: ModelParams.
                lam branchKernel1: Matrix Float.
                  let unorderedBranch =
                    sampleUnorderedBranch
                      startRep
                      finalRep1
                      startAge
                      finalAge3
                      nHosts2
                      nodeLabel1
                      (let target73 = modelParams3 in
                       match target73 with ModelParams1 x114
                       then
                         x114.embeddedQMatrix
                       else
                         let #var"2" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 255:4-255:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
                         in
                         exit 1)
                  in
                  let allHostEvents = paste0 unorderedBranch in
                  let orderedEvents = qSort compAge allHostEvents in
                  let nEvents4 = length1 orderedEvents in
                  match
                    allTimesValidBranch startRep orderedEvents 1 nEvents4 nHosts2
                  with
                    true
                  then
                    let logSamplingDensity =
                      independenceLikelihoodEndCond
                        startRep
                        finalRep1
                        startAge
                        finalAge3
                        unorderedBranch
                        modelParams3
                        branchKernel1
                    in
                    let logModelDensity =
                      fullModelWeight
                        1
                        startRep
                        finalRep1
                        startAge
                        finalAge3
                        orderedEvents
                        nEvents4
                        nHosts2
                        modelParams3
                    in
                    CorrectedBranchSample1
                      { history = orderedEvents,
                        logSamplingDensity = logSamplingDensity,
                        logModelDensity = logModelDensity,
                        success = true }
                  else
                    CorrectedBranchSample1
                      { history = orderedEvents,
                        logSamplingDensity = log1 0.,
                        logModelDensity = log1 0.,
                        success = false }
in
recursive
  let sampleTreeHistory: MsgTree -> Int -> Matrix Float -> [Int] -> Float -> ModelParams -> Matrix Float -> HistoryTree =
    lam tree2: MsgTree.
      lam nHosts: Int.
        lam preorderMsg: Matrix Float.
          lam parentRep: [Int].
            lam parentAge: Float.
              lam modelParams1: ModelParams.
                lam branchKernel: Matrix Float.
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
                      let target32 = tree2 in
                      match target32 with MsgLeaf x54
                      then
                        x54.interactions
                      else
                        let #var"2" =
                          print
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 169:14-169:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
                        in
                        exit 1
                    in
                    let branchSample =
                      sampleBranch
                        parentRep
                        rep1
                        parentAge
                        (let target30 = tree2 in
                         match target30 with MsgNode x50
                         then
                           x50.age
                         else match target30 with MsgLeaf x51
                         then
                           x51.age
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 175:6-175:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                           in
                           exit 1)
                        nHosts
                        (let target31 = tree2 in
                         match target31 with MsgNode x52
                         then
                           x52.label
                         else match target31 with MsgLeaf x53
                         then
                           x53.label
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 177:6-177:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                           in
                           exit 1)
                        modelParams1
                        branchKernel
                    in
                    let foo =
                      weight
                        (mulf
                           (subf
                              (let target27 = branchSample in
                               match target27 with CorrectedBranchSample1 x46
                               then
                                 x46.logModelDensity
                               else
                                 let #var"2" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 183:15-183:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                              (let target28 = branchSample in
                               match target28 with CorrectedBranchSample1 x47
                               then
                                 x47.logSamplingDensity
                               else
                                 let #var"2" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 183:46-183:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1))
                           (exp1
                              (mulf
                                 (int2float
                                    (let target29 = tree2 in
                                     match target29 with MsgNode x48
                                     then
                                       x48.label
                                     else match target29 with MsgLeaf x49
                                     then
                                       x49.label
                                     else
                                       let #var"2" =
                                         print
                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 183:90-183:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                       in
                                       exit 1))
                                 0.)))
                    in
                    HistoryLeaf
                      { age =
                          let target24 = tree2 in
                          match target24 with MsgNode x41
                          then
                            x41.age
                          else match target24 with MsgLeaf x42
                          then
                            x42.age
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 186:12-186:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
                            in
                            exit 1,
                        label =
                          let target25 = tree2 in
                          match target25 with MsgNode x43
                          then
                            x43.label
                          else match target25 with MsgLeaf x44
                          then
                            x44.label
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 187:14-187:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                            in
                            exit 1,
                        repertoire = rep1,
                        history =
                          let target26 = branchSample in
                          match target26 with CorrectedBranchSample1 x45
                          then
                            x45.history
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 189:16-189:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
                            in
                            exit 1 }
                  else
                    let samplingProb =
                      mtxElemMul
                        (let target51 = tree2 in
                         match target51 with MsgNode x82
                         then
                           x82.outMsg
                         else match target51 with MsgLeaf x83
                         then
                           x83.outMsg
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 192:34-192:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
                           in
                           exit 1)
                        preorderMsg
                    in
                    let rep2 =
                      suggestNodeRep
                        samplingProb
                        nHosts
                        (let target50 = tree2 in
                         match target50 with MsgNode x80
                         then
                           x80.label
                         else match target50 with MsgLeaf x81
                         then
                           x81.label
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 193:51-193:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
                           in
                           exit 1)
                    in
                    let foo1 =
                      weight
                        (externalLog
                           (addf
                              (bool2real (any1 is2 rep2))
                              (mulf
                                 (int2float
                                    (let target49 = tree2 in
                                     match target49 with MsgNode x78
                                     then
                                       x78.label
                                     else match target49 with MsgLeaf x79
                                     then
                                       x79.label
                                     else
                                       let #var"2" =
                                         print
                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 195:43-195:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                       in
                                       exit 1))
                                 0.)))
                    in
                    let nodeLogSamplingDensity = getRepertoireSamplingDensity rep2 samplingProb
                    in
                    let branchSample1 =
                      sampleBranch
                        parentRep
                        rep2
                        parentAge
                        (let target47 = tree2 in
                         match target47 with MsgNode x74
                         then
                           x74.age
                         else match target47 with MsgLeaf x75
                         then
                           x75.age
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 203:6-203:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
                           in
                           exit 1)
                        nHosts
                        (let target48 = tree2 in
                         match target48 with MsgNode x76
                         then
                           x76.label
                         else match target48 with MsgLeaf x77
                         then
                           x77.label
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 205:6-205:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
                           in
                           exit 1)
                        modelParams1
                        branchKernel
                    in
                    let foo2 =
                      weight
                        (subf
                           (subf
                              (let target44 = branchSample1 in
                               match target44 with CorrectedBranchSample1 x70
                               then
                                 x70.logModelDensity
                               else
                                 let #var"2" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 211:14-211:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                              (let target45 = branchSample1 in
                               match target45 with CorrectedBranchSample1 x71
                               then
                                 x71.logSamplingDensity
                               else
                                 let #var"2" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 211:45-211:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1))
                           (mulf
                              nodeLogSamplingDensity
                              (exp1
                                 (mulf
                                    (int2float
                                       (let target46 = tree2 in
                                        match target46 with MsgNode x72
                                        then
                                          x72.label
                                        else match target46 with MsgLeaf x73
                                        then
                                          x73.label
                                        else
                                          let #var"2" =
                                            print
                                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 211:113-211:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                          in
                                          exit 1))
                                    0.))))
                    in
                    let newMsg = observationMessage rep2 in
                    let leftMsg =
                      mtxMul
                        newMsg
                        (let target43 = tree2 in
                         match target43 with MsgNode x69
                         then
                           x69.leftKernel
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 215:33-215:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
                           in
                           exit 1)
                    in
                    let rightMsg =
                      mtxMul
                        newMsg
                        (let target42 = tree2 in
                         match target42 with MsgNode x68
                         then
                           x68.rightKernel
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 216:34-216:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
                           in
                           exit 1)
                    in
                    let left1 =
                      sampleTreeHistory
                        (let target39 = tree2 in
                         match target39 with MsgNode x64
                         then
                           x64.left
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 220:6-220:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
                           in
                           exit 1)
                        nHosts
                        leftMsg
                        rep2
                        (let target40 = tree2 in
                         match target40 with MsgNode x65
                         then
                           x65.age
                         else match target40 with MsgLeaf x66
                         then
                           x66.age
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 220:39-220:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
                           in
                           exit 1)
                        modelParams1
                        (let target41 = tree2 in
                         match target41 with MsgNode x67
                         then
                           x67.leftKernel
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 220:62-220:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
                           in
                           exit 1)
                    in
                    let right1 =
                      sampleTreeHistory
                        (let target36 = tree2 in
                         match target36 with MsgNode x60
                         then
                           x60.right
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 223:6-223:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
                           in
                           exit 1)
                        nHosts
                        rightMsg
                        rep2
                        (let target37 = tree2 in
                         match target37 with MsgNode x61
                         then
                           x61.age
                         else match target37 with MsgLeaf x62
                         then
                           x62.age
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 223:41-223:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
                           in
                           exit 1)
                        modelParams1
                        (let target38 = tree2 in
                         match target38 with MsgNode x63
                         then
                           x63.rightKernel
                         else
                           let #var"2" =
                             print
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 223:64-223:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
                           in
                           exit 1)
                    in
                    HistoryNode
                      { age =
                          let target33 = tree2 in
                          match target33 with MsgNode x55
                          then
                            x55.age
                          else match target33 with MsgLeaf x56
                          then
                            x56.age
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 227:12-227:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
                            in
                            exit 1,
                        left = left1,
                        right = right1,
                        label =
                          let target34 = tree2 in
                          match target34 with MsgNode x57
                          then
                            x57.label
                          else match target34 with MsgLeaf x58
                          then
                            x58.label
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 228:14-228:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                            in
                            exit 1,
                        repertoire = rep2,
                        history =
                          let target35 = branchSample1 in
                          match target35 with CorrectedBranchSample1 x59
                          then
                            x59.history
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 230:16-230:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                            in
                            exit 1 }
in
let anon48: [Float] -> Dist([Float]) = lam lambda1.
    rbLambdaMove lambda1
in
let anon49: Float -> Dist(Float) = lam mu1.
    rbMuMove mu1 in
let anon50: Float -> Dist(Float) = lam beta1.
    rbBetaMove beta1
in
let hostRepertoireModel: TreeLabeled -> [[Int]] -> [[Float]] -> Float -> Int -> ReturnType =
  lam symbiontTree: TreeLabeled.
    lam interactions2: [[Int]].
      lam hostDistances: [[Float]].
        lam subrootLength: Float.
          lam subrootLabel: Int.
            let nHosts1 = length1 hostDistances in
            let lambda = assume
                (Dirichlet [ 1., 1., 1., 1. ])
            in
            let mu = assume
                (Exponential 10.) in
            let beta = assume
                (Exponential 1.) in
            let r1 =
              mtxCreate
                3
                3
                [ subf 0. (get lambda (subi 1 1)),
                  get lambda (subi 1 1),
                  0.,
                  get lambda (subi 2 1),
                  subf 0. (addf (get lambda (subi 2 1)) (get lambda (subi 3 1))),
                  get lambda (subi 3 1),
                  0.,
                  get lambda (subi 4 1),
                  subf 0. (get lambda (subi 4 1)) ]
            in
            let qMatrix2 = mtxSclrMul mu r1 in
            let embeddedQMatrix2 = rateMatrixToEmbeddedMarkovChain qMatrix2
            in
            let modelParams2 =
              ModelParams1
                { beta = beta,
                  hostMetric = nestSeqToMtx (normalizeHostMetric hostDistances),
                  embeddedQMatrix = embeddedQMatrix2 }
            in
            let postorderTree =
              postorderTraverse symbiontTree qMatrix2 interactions2 nHosts1
            in
            let subrootInfo =
              subrootNode
                (let target72 = postorderTree in
                 match target72 with MsgNode x112
                 then
                   x112.outMsg
                 else match target72 with MsgLeaf x113
                 then
                   x113.outMsg
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 84:32-84:52>:\nField \'outMsg\' not found\n[0m  let subrootInfo = subrootNode([31mpostorderTree.outMsg[0m[0m, subrootLength, subrootLabel, qMatrix, nHosts);\n"
                   in
                   exit 1)
                subrootLength
                subrootLabel
                qMatrix2
                nHosts1
            in
            let rootSamplingProb =
              mtxElemMul
                (let target70 = subrootInfo in
                 match target70 with SubrootInfo1 x109
                 then
                   x109.msg
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 86:36-86:51>:\nField \'msg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31msubrootInfo.msg[0m[0m, postorderTree.outMsg);\n"
                   in
                   exit 1)
                (let target71 = postorderTree in
                 match target71 with MsgNode x110
                 then
                   x110.outMsg
                 else match target71 with MsgLeaf x111
                 then
                   x111.outMsg
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 86:53-86:73>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul(subrootInfo.msg, [31mpostorderTree.outMsg[0m[0m);\n"
                   in
                   exit 1)
            in
            let rootRep =
              suggestNodeRep
                rootSamplingProb
                nHosts1
                (let target69 = postorderTree in
                 match target69 with MsgNode x107
                 then
                   x107.label
                 else match target69 with MsgLeaf x108
                 then
                   x108.label
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 87:57-87:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
                   in
                   exit 1)
            in
            let foo3 =
              weight
                (externalLog
                   (addf
                      (bool2real (any1 is2 rootRep))
                      (mulf
                         (int2float
                            (let target68 = postorderTree in
                             match target68 with MsgNode x105
                             then
                               x105.label
                             else match target68 with MsgLeaf x106
                             then
                               x106.label
                             else
                               let #var"2" =
                                 print
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 88:45-88:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                               in
                               exit 1))
                         0.)))
            in
            let rootAge =
              let target67 = postorderTree in
              match target67 with MsgNode x103
              then
                x103.age
              else match target67 with MsgLeaf x104
              then
                x104.age
              else
                let #var"2" =
                  print
                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 91:16-91:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
                in
                exit 1
            in
            let subrootBranchSample =
              sampleBranch
                (let target65 = subrootInfo in
                 match target65 with SubrootInfo1 x101
                 then
                   x101.rep
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 93:4-93:19>:\nField \'rep\' not found\n[0m    [31msubrootInfo.rep[0m[0m,\n"
                   in
                   exit 1)
                rootRep
                (addf rootAge subrootLength)
                rootAge
                nHosts1
                (negi 1)
                modelParams2
                (let target66 = subrootInfo in
                 match target66 with SubrootInfo1 x102
                 then
                   x102.kernel
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 100:4-100:22>:\nField \'kernel\' not found\n[0m    [31msubrootInfo.kernel[0m\n"
                   in
                   exit 1)
            in
            let rootLogSamplingDensity = getRepertoireSamplingDensity rootRep rootSamplingProb
            in
            let foo4 =
              weight
                (subf
                   (subf
                      (let target62 = subrootBranchSample in
                       match target62 with CorrectedBranchSample1 x97
                       then
                         x97.logModelDensity
                       else
                         let #var"2" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 108:4-108:39>:\nField \'logModelDensity\' not found\n[0m    [31msubrootBranchSample.logModelDensity[0m\n"
                         in
                         exit 1)
                      (let target63 = subrootBranchSample in
                       match target63 with CorrectedBranchSample1 x98
                       then
                         x98.logSamplingDensity
                       else
                         let #var"2" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 109:6-109:44>:\nField \'logSamplingDensity\' not found\n[0m    - [31msubrootBranchSample.logSamplingDensity[0m\n"
                         in
                         exit 1))
                   (mulf
                      rootLogSamplingDensity
                      (exp1
                         (mulf
                            (int2float
                               (let target64 = postorderTree in
                                match target64 with MsgNode x99
                                then
                                  x99.label
                                else match target64 with MsgLeaf x100
                                then
                                  x100.label
                                else
                                  let #var"2" =
                                    print
                                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 110:40-110:59>:\nField \'label\' not found\n[0m    - rootLogSamplingDensity * exp(Real([31mpostorderTree.label[0m[0m) * 0.)\n"
                                  in
                                  exit 1))
                            0.))))
            in
            let newMsg1 = observationMessage rootRep in
            let leftMsg1 =
              mtxMul
                newMsg1
                (let target61 = postorderTree in
                 match target61 with MsgNode x96
                 then
                   x96.leftKernel
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 115:31-115:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
                   in
                   exit 1)
            in
            let rightMsg1 =
              mtxMul
                newMsg1
                (let target60 = postorderTree in
                 match target60 with MsgNode x95
                 then
                   x95.rightKernel
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 116:32-116:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
                   in
                   exit 1)
            in
            let rootAge1 =
              let target59 = postorderTree in
              match target59 with MsgNode x93
              then
                x93.age
              else match target59 with MsgLeaf x94
              then
                x94.age
              else
                let #var"2" =
                  print
                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 119:16-119:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
                in
                exit 1
            in
            let leftRepertoireTree =
              sampleTreeHistory
                (let target57 = postorderTree in
                 match target57 with MsgNode x91
                 then
                   x91.left
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 121:4-121:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
                   in
                   exit 1)
                nHosts1
                leftMsg1
                rootRep
                rootAge1
                modelParams2
                (let target58 = postorderTree in
                 match target58 with MsgNode x92
                 then
                   x92.leftKernel
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 121:72-121:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
                   in
                   exit 1)
            in
            let rightRepertoireTree =
              sampleTreeHistory
                (let target55 = postorderTree in
                 match target55 with MsgNode x89
                 then
                   x89.right
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 125:4-125:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
                   in
                   exit 1)
                nHosts1
                rightMsg1
                rootRep
                rootAge1
                modelParams2
                (let target56 = postorderTree in
                 match target56 with MsgNode x90
                 then
                   x90.rightKernel
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 125:74-125:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
                   in
                   exit 1)
            in
            let historyTree =
              HistoryNode
                { age =
                    let target52 = symbiontTree in
                    match target52 with Node x84
                    then
                      x84.age
                    else match target52 with Leaf x85
                    then
                      x85.age
                    else
                      let #var"2" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 130:10-130:26>:\nField \'age\' not found\n[0m    age = [31msymbiontTree.age[0m[0m, label = symbiontTree.label,\n"
                      in
                      exit 1,
                  left = leftRepertoireTree,
                  right = rightRepertoireTree,
                  label =
                    let target53 = symbiontTree in
                    match target53 with Node x86
                    then
                      x86.label
                    else match target53 with Leaf x87
                    then
                      x87.label
                    else
                      let #var"2" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 130:36-130:54>:\nField \'label\' not found\n[0m    age = symbiontTree.age, label = [31msymbiontTree.label[0m[0m,\n"
                      in
                      exit 1,
                  repertoire = rootRep,
                  history =
                    let target54 = subrootBranchSample in
                    match target54 with CorrectedBranchSample1 x88
                    then
                      x88.history
                    else
                      let #var"2" =
                        print
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/subroot-HRM.tppl 132:36-132:63>:\nField \'history\' not found\n[0m    repertoire = rootRep, history = [31msubrootBranchSample.history[0m\n"
                      in
                      exit 1 }
            in
            ReturnType1
              { mu = mu, lambda = lambda, beta = beta, tree = historyTree }
in
let anon51: {interactions: [[Int]], subrootLabel: Int, symbiontTree: TreeLabeled, hostDistances: [[Float]], subrootLength: Float} -> () -> ReturnType =
  lam input1.
    lam #var"5".
      hostRepertoireModel
        input1.symbiontTree
        input1.interactions
        input1.hostDistances
        input1.subrootLength
        input1.subrootLabel
in
anon51 input {}
