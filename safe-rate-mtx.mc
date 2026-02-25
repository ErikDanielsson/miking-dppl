let and: Bool -> Bool -> Bool =
  lam a95: Bool.
    lam b32: Bool.
      match a95 with true
      then
        b32
      else
        false
in
let isNaN: Float -> Bool =
  lam a94: Float.
    match eqf a94 a94 with true
    then
      false
    else
      true
in
external externalExp : Float -> Float in
let exp = lam x174: Float.
    externalExp x174 in
external externalLog : Float -> Float in
let log = lam x173: Float.
    externalLog x173 in
external externalPow : Float -> Float -> Float in
let pow = lam x172: Float.
    lam y: Float.
      externalPow x172 y
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
let map1 = lam f33.
    lam s14.
      rec f33 s14 in
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
let mapi1 = lam f32.
    lam s13.
      rec1 f32 0 s13 in
let iteri1 =
  lam f31.
    lam s12.
      let #var"24" = mapi1 f31 s12 in
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
  lam f30.
    lam acc22.
      lam s11.
        rec2 f30 acc22 s11
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
    lam f29.
      rec3 f29 (subi l6 1) ""
in
type Option a12 in
con Some: all a13. a13 -> Option a13 in
con None: all a14. () -> Option a14 in
type Either a15 b in
con Left: all a16. all b1. a16 -> Either a16 b1 in
con Right: all a17. all b2. b2 -> Either a17 b2 in
let anon: all a93. a93 -> Int -> a93 = lam v4.
    lam #var"23".
      v4
in
let make: all a92. Int -> a92 -> [a92] = lam n9: Int.
    lam v3: a92.
      create1 n9 (anon v3)
in
recursive
  let unfoldr: all a18. all c. (a18 -> Option (c, a18)) -> a18 -> [c] =
    lam f4: a18 -> Option (c, a18).
      lam b0: a18.
        let fb = f4 b0 in
        match fb with None _
        then
          ""
        else match fb with Some (x, b11)
        in
        cons x (unfoldr f4 b11)
in
let anon1: Int -> Int -> Int -> Option (Int, Int) =
  lam e4.
    lam by1.
      lam b31.
        match leqi e4 b31 with true
        then
          None
            {}
        else
          Some
            (b31, addi b31 by1)
in
let range: Int -> Int -> Int -> [Int] =
  lam s10: Int.
    lam e3: Int.
      lam by: Int.
        unfoldr (anon1 e3 by) s10
in
let g: all c11. all b30. all a91. (a91 -> b30 -> c11 -> a91) -> (a91, [b30]) -> c11 -> (a91, [b30]) =
  lam f28.
    lam acc20: (a91, [b30]).
      lam x212.
        match acc20 with (acc21, [ x171 ] ++ xs1)
        then
          (f28 acc21 x171 x212, xs1)
        else
          error "foldl2: Cannot happen!"
in
let g1: all c10. all b29. all a90. (a90 -> b29 -> c10 -> a90) -> (a90, [c10]) -> b29 -> (a90, [c10]) =
  lam f27.
    lam acc18: (a90, [c10]).
      lam x170.
        match acc18 with (acc19, [ x211 ] ++ xs2)
        then
          (f27 acc19 x170 x211, xs2)
        else
          error "foldl2: Cannot happen!"
in
let foldl2: all a89. all b28. all c9. (a89 -> b28 -> c9 -> a89) -> a89 -> [b28] -> [c9] -> a89 =
  lam f26: a89 -> b28 -> c9 -> a89.
    lam acc15: a89.
      lam seq11: [b28].
        lam seq21: [c9].
          match geqi (length seq11) (length seq21) with true
          then
            match foldl1 (g f26) (acc15, seq11) seq21 with (acc16, _)
            in
            acc16
          else match foldl1 (g1 f26) (acc15, seq21) seq11 with (acc17, _)
          in
          acc17
in
recursive
  let work: all b3. all a19. (a19 -> Int -> b3 -> a19) -> a19 -> Int -> [b3] -> a19 =
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
let foldli: all a88. all b27. (a88 -> Int -> b27 -> a88) -> a88 -> [b27] -> a88 =
  lam fn1: a88 -> Int -> b27 -> a88.
    lam initAcc: a88.
      lam seq8: [b27].
        work fn1 initAcc 0 seq8
in
let anon2: all c8. all b26. all a87. (a87 -> b26 -> c8) -> [c8] -> a87 -> b26 -> [c8] =
  lam f25.
    lam acc14.
      lam x169.
        lam x210.
          snoc acc14 (f25 x169 x210)
in
let zipWith: all a86. all b25. all c7. (a86 -> b25 -> c7) -> [a86] -> [b25] -> [c7] = lam f24: a86 -> b25 -> c7.
    foldl2 (anon2 f24) ""
in
recursive
  let any: all a20. (a20 -> Bool) -> [a20] -> Bool =
    lam p: a20 -> Bool.
      lam seq: [a20].
        match null seq with true
        then
          false
        else match p (head seq) with true
        then
          true
        else
          any p (tail seq)
in
let join: all a85. [[a85]] -> [a85] = lam seqs: [[a85]].
    foldl1 concat "" seqs
in
recursive
  let work1: all a21. (a21 -> Bool) -> [a21] -> [a21] -> [a21] -> ([a21], [a21]) =
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
let partition: all a84. (a84 -> Bool) -> [a84] -> ([a84], [a84]) =
  lam p4: a84 -> Bool.
    lam seq7: [a84].
      work1 p4 "" "" (reverse seq7)
in
let anon3: all a83. (a83 -> a83 -> Int) -> a83 -> a83 -> Bool =
  lam cmp4.
    lam h5.
      lam x168.
        lti (cmp4 x168 h5) 0
in
recursive
  let quickSort: all a22. (a22 -> a22 -> Int) -> [a22] -> [a22] =
    lam cmp: a22 -> a22 -> Int.
      lam seq3: [a22].
        match null seq3 with true
        then
          seq3
        else
          let h = head seq3 in
          let t = tail seq3 in
          let lr = partition (anon3 cmp h) t in
          concat (quickSort cmp lr.0) (cons h (quickSort cmp lr.1))
in
recursive
  let rec4 =
    lam f5.
      lam n.
        lam i3.
          match geqi i3 n with true
          then
            {}
          else
            (f5 i3)
            ; rec4 f5 n (addi i3 1)
in
let repeati: (Int -> ()) -> Int -> () = lam f23: Int -> ().
    lam n8: Int.
      rec4 f23 n8 0
in
let eitherEither: all a82. all b24. all c6. (a82 -> c6) -> (b24 -> c6) -> Either a82 b24 -> c6 =
  lam lf: a82 -> c6.
    lam rf: b24 -> c6.
      lam e2: Either a82 b24.
        match e2 with Left content
        then
          lf content
        else match e2 with Right content1
        in
        rf content1
in
type ExtArrKind a23 in
type ExtArr a24 in
external externalExtArrMakeUninit : all a25. ExtArrKind a25 -> Int -> ExtArr a25
in
external externalExtArrKind : all a26. ExtArr a26 -> ExtArrKind a26
in
external externalExtArrLength : all a27. ExtArr a27 -> Int in
external externalExtArrGet : all a28. ExtArr a28 -> Int -> a28
in
external externalExtArrSet! : all a29. ExtArr a29 -> Int -> a29 -> ()
in
external extArrKindFloat64 : ExtArrKind Float in
let extArrMakeUninit: all a81. ExtArrKind a81 -> Int -> ExtArr a81 =
  lam kind2: ExtArrKind a81.
    lam n7: Int.
      externalExtArrMakeUninit kind2 n7
in
let extArrLength: all a79. ExtArr a79 -> Int = lam a80: ExtArr a79.
    externalExtArrLength a80
in
let extArrGetExn: all a77. ExtArr a77 -> Int -> a77 =
  lam a78: ExtArr a77.
    lam i23: Int.
      externalExtArrGet a78 i23
in
let extArrSetExn: all a75. ExtArr a75 -> Int -> a75 -> () =
  lam a76: ExtArr a75.
    lam i22: Int.
      lam v2: a75.
        externalExtArrSet a76 i22 v2
in
let extArrOfSeq: all a73. ExtArrKind a73 -> [a73] -> ExtArr a73 =
  lam kind1: ExtArrKind a73.
    lam seq6: [a73].
      tmOpaque (let len = length seq6 in
       let a74 = externalExtArrMakeUninit kind1 len in
       recursive
         let work3 =
           lam i21.
             match eqi i21 len with true
             then
               {}
             else
               let #var"21" = externalExtArrSet a74 i21 (get seq6 i21) in
               work3 (addi i21 1)
       in
       let #var"22" = work3 0 in
       a74)
in
let extArrToSeq: all a71. ExtArr a71 -> [a71] =
  lam a72: ExtArr a71.
    create1 (externalExtArrLength a72) (externalExtArrGet a72)
in
type CBLASLayout in
external cblasRowMajor : CBLASLayout in
type CBLASTranspose in
external cblasNoTrans : CBLASTranspose in
external externalCblasCopy : all a30. Int -> ExtArr a30 -> Int -> ExtArr a30 -> Int -> ()
in
external externalCblasScal : all a31. Int -> a31 -> ExtArr a31 -> Int -> ()
in
external externalCblasGemm : all a32. CBLASLayout -> CBLASTranspose -> CBLASTranspose -> Int -> Int -> Int -> a32 -> ExtArr a32 -> Int -> ExtArr a32 -> Int -> a32 -> ExtArr a32 -> Int -> ()
in
type MatError in
con DimensionMismatch: () -> MatError in
con NotSquare: () -> MatError in
let matErrorToString: MatError -> [Char] =
  lam err3: MatError.
    let #var"X12" = err3 in
    match #var"X12" with DimensionMismatch _
    then
      "Dimension mismatch"
    else match #var"X12" with NotSquare _
    in
    "Not square"
in
type Mat a33 =
  {m: Int, n: Int, arr: ExtArr a33} in
let matMakeUninit: all a70. ExtArrKind a70 -> Int -> Int -> Mat a70 =
  lam kind: ExtArrKind a70.
    lam m4: Int.
      lam n6: Int.
        { n = n6,
          arr = externalExtArrMakeUninit kind (muli m4 n6),
          m = m4 }
in
let matGetExn: all a68. Mat a68 -> Int -> Int -> a68 =
  lam a69: Mat a68.
    lam i20: Int.
      lam j2: Int.
        externalExtArrGet a69.arr (addi (muli i20 a69.n) j2)
in
let matSetExn: all a66. Mat a66 -> Int -> Int -> a66 -> () =
  lam a67: Mat a66.
    lam i19: Int.
      lam j1: Int.
        lam v1: a66.
          externalExtArrSet a67.arr (addi (muli i19 a67.n) j1) v1
in
let matFromArrExn: all a64. Int -> Int -> ExtArr a64 -> Mat a64 =
  lam m3: Int.
    lam n5: Int.
      lam a65: ExtArr a64.
        match eqi (muli m3 n5) (extArrLength a65) with true
        then
          { n = n5, arr = a65, m = m3 }
        else
          error "matFromArrExn: dimensions mismatch"
in
let matCopy: all a62. Mat a62 -> Mat a62 =
  lam a63: Mat a62.
    let mn1 = muli a63.m a63.n in
    let b22 =
      tmOpaque (let b23 = extArrMakeUninit (externalExtArrKind a63.arr) mn1 in
       let #var"20" = externalCblasCopy mn1 a63.arr 1 b23 1 in
       b23)
    in
    { a63 with arr = b22 }
in
let matHasSameShape2 =
  lam a61.
    lam b21.
      and (eqi a61.m b21.m) (eqi a61.n b21.n)
in
let matHasSameShape3 =
  lam a60.
    lam b20.
      lam c5.
        and (matHasSameShape2 a60 b20) (matHasSameShape2 b20 c5)
in
let matIsSquare = lam a59.
    eqi a59.m a59.n in
external externalMatTranspose : Int -> Int -> ExtArr Float -> ExtArr Float -> ()
in
let matTranposeNoAlloc: Mat Float -> Mat Float -> Either MatError () =
  lam a58: Mat Float.
    lam b19: Mat Float.
      match and (eqi a58.m b19.n) (eqi a58.n b19.m) with true
      then
        let #var"19" = externalMatTranspose a58.m a58.n a58.arr b19.arr
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
  lam a57: Mat Float.
    lam b18: Mat Float.
      lam c4: Mat Float.
        match matHasSameShape3 a57 b18 c4 with true
        then
          let #var"18" = externalMatElemMul a57.m a57.n a57.arr b18.arr c4.arr
          in
          Right
            {}
        else
          Left
            (DimensionMismatch
               {})
in
let matTranspose: Mat Float -> Mat Float =
  lam a56: Mat Float.
    tmOpaque (let b17 = matMakeUninit (externalExtArrKind a56.arr) a56.n a56.m
     in
     let #var"17" = matTranposeNoAlloc a56 b17 in
     b17)
in
let matElemMul: Mat Float -> Mat Float -> Either MatError (Mat Float) =
  lam a55: Mat Float.
    lam b16: Mat Float.
      match matHasSameShape2 a55 b16 with true
      then
        Right
          (tmOpaque (let c3 = matMakeUninit (externalExtArrKind a55.arr) a55.m a55.n
            in
            let #var"16" = matElemMulNoAlloc a55 b16 c3 in
            c3))
      else
        Left
          (DimensionMismatch
             {})
in
let anon4: MatError -> Mat Float = lam err2.
    error (matErrorToString err2)
in
let anon5: Mat Float -> Mat Float = lam x167.
    x167 in
let matElemMulExn: Mat Float -> Mat Float -> Mat Float =
  lam a54: Mat Float.
    lam b15: Mat Float.
      eitherEither anon4 anon5 (matElemMul a54 b15)
in
let matScale: Float -> Mat Float -> Mat Float =
  lam s9: Float.
    lam a53: Mat Float.
      let m2 = a53.m in
      let n4 = a53.n in
      let mn = muli m2 n4 in
      tmOpaque (let b14 = matMakeUninit (externalExtArrKind a53.arr) m2 n4 in
       let #var"14" = externalCblasCopy mn a53.arr 1 b14.arr 1 in
       let #var"15" = externalCblasScal mn s9 b14.arr 1 in
       b14)
in
let matMul: Mat Float -> Mat Float -> Either MatError (Mat Float) =
  lam a52: Mat Float.
    lam b13: Mat Float.
      let m1 = a52.m in
      let n3 = b13.n in
      let k2 = a52.n in
      match eqi k2 b13.m with true
      then
        Right
          (tmOpaque (let c2 = matMakeUninit (externalExtArrKind b13.arr) m1 n3 in
            let #var"13" =
              externalCblasGemm
                cblasRowMajor
                cblasNoTrans
                cblasNoTrans
                m1
                n3
                k2
                1.
                a52.arr
                k2
                b13.arr
                n3
                0.
                c2.arr
                n3
            in
            c2))
      else
        Left
          (DimensionMismatch
             {})
in
let anon6: MatError -> Mat Float = lam err1.
    error (matErrorToString err1)
in
let anon7: Mat Float -> Mat Float = lam x166.
    x166 in
let matMulExn: Mat Float -> Mat Float -> Mat Float =
  lam a51: Mat Float.
    lam b12: Mat Float.
      eitherEither anon6 anon7 (matMul a51 b12)
in
external externalMatExp : Int -> Int -> ExtArr Float -> ExtArr Float
in
let matExp: Mat Float -> Either MatError (Mat Float) =
  lam a50: Mat Float.
    match matIsSquare a50 with true
    then
      Right
        { a50 with arr = externalMatExp a50.m a50.n a50.arr }
    else
      Left
        (NotSquare
           {})
in
let anon8: MatError -> Mat Float = lam err.
    error (matErrorToString err)
in
let anon9: Mat Float -> Mat Float = lam x165.
    x165 in
let matExpExn: Mat Float -> Mat Float =
  lam a49: Mat Float.
    eitherEither anon8 anon9 (matExp a49)
in
recursive
  let work2: all a34. Int -> (Int -> a34 -> a34) -> Int -> a34 -> a34 =
    lam bound.
      lam f6.
        lam i4.
          lam acc3.
            match lti i4 bound with true
            then
              work2 bound f6 (addi i4 1) (f6 i4 acc3)
            else
              acc3
in
let _iterateni = lam bound1.
    lam f22.
      work2 bound1 f22 0
in
let seqSnoc = snoc in
let seqCons = cons in
let seqLength = length in
let seqMap = map1 in
let seqZipWith = zipWith in
let seqSubsequence = subsequence in
let seqFoldl = foldl1 in
let seqFoldli = foldli in
let seqAny = any in
let mathExp = exp in
let mathLog = log in
let anon10: (Float -> Float) -> Mat Float -> Mat Float -> Int -> () =
  lam f21.
    lam mtx12.
      lam mtx25.
        lam i18.
          extArrSetExn mtx25.arr i18 (f21 (extArrGetExn mtx12.arr i18))
in
let matMap: all x164. (Float -> Float) -> Mat Float -> Mat Float =
  lam f20: Float -> Float.
    lam mtx11: Mat Float.
      let mtx24 = matCopy mtx11 in
      let #var"12" = repeati (anon10 f20 mtx11 mtx24) (muli mtx11.m mtx11.n)
      in
      mtx24
in
let anon11: Mat Float -> [Float] -> Mat Float -> Int -> Int -> () =
  lam mtx10.
    lam sums2.
      lam mtx23.
        lam i17.
          lam j.
            matSetExn mtx23 i17 j (divf (matGetExn mtx10 i17 j) (get sums2 i17))
in
let anon12: Mat Float -> [Float] -> Mat Float -> Int -> () =
  lam mtx9.
    lam sums1.
      lam mtx22.
        lam i16.
          repeati (anon11 mtx9 sums1 mtx22 i16) mtx9.n
in
let matNormalizeRows: Mat Float -> Mat Float =
  lam mtx8: Mat Float.
    let sums =
      extArrToSeq
        (matMulExn
           mtx8
           (matFromArrExn mtx8.m 1 (extArrOfSeq extArrKindFloat64 (make mtx8.m 1.)))).arr
    in
    let mtx21 = matCopy mtx8 in
    let #var"11" = repeati (anon12 mtx8 sums mtx21) mtx8.m in
    mtx21
in
let anon13: Float -> Float =
  lam f19.
    match gtf f19 0. with true
    then
      f19
    else
      0.
in
let matExpRateSafe: Mat Float -> Mat Float =
  lam mtx7: Mat Float.
    matNormalizeRows (matMap anon13 (matExpExn mtx7))
in
let anon14: Matrix Float -> Int -> Float -> Float =
  lam t4.
    lam i15.
      lam acc13.
        addf acc13 (extArrGetExn t4.arr i15)
in
let matMean =
  lam t3.
    let sum = _iterateni (muli t3.m t3.n) (anon14 t3) 0. in
    divf sum (int2float (muli t3.m t3.n))
in
let anon15: all a48. Mat a48 -> Int -> Mat a48 -> Int -> Int -> () =
  lam matrix1.
    lam r4.
      lam new1.
        lam i14.
          lam c1.
            matSetExn new1 0 i14 (matGetExn matrix1 r4 (subi c1 1))
in
let matRowCols =
  lam matrix.
    lam row2.
      lam cols2.
        let r3 = subi row2 1 in
        let new =
          matMakeUninit (externalExtArrKind matrix.arr) 1 (length cols2)
        in
        let #var"10" = iteri1 (anon15 matrix r3 new) cols2 in
        new
in
type Matrix #var"X" =
  Mat #var"X" in
let x1: all #var"B10". all #var"A10". (#var"A10" -> #var"B10" -> #var"A10") -> #var"A10" -> #var"B10" -> #var"A10" =
  lam f18.
    lam a47.
      lam b10: #var"B10".
        let x163: #var"A10" = f18 a47 b10 in
        x163
in
let x2: all #var"B9". all #var"A9". (#var"A9" -> Int -> #var"B9" -> #var"A9") -> #var"A9" -> Int -> #var"B9" -> #var"A9" =
  lam f17.
    lam a46.
      lam idx9.
        lam b9: #var"B9".
          let x162: #var"A9" = f17 a46 (addi idx9 1) b9 in
          x162
in
let x3: all #var"B8". all #var"A8". (#var"A8" -> Int -> #var"B8" -> #var"A8") -> #var"A8" -> Int -> #var"B8" -> #var"A8" =
  lam f16.
    lam a45.
      lam idx8: Int.
        x2 f16 a45 idx8
in
let x4: all #var"C2". all #var"B7". all #var"A7". (#var"A7" -> #var"B7" -> #var"C2") -> #var"A7" -> #var"B7" -> #var"C2" =
  lam f15.
    lam a44.
      lam b8: #var"B7".
        let x161: #var"C2" = f15 a44 b8 in
        x161
in
let x5: all #var"X11". (#var"X11" -> #var"X11" -> Int) -> #var"X11" -> #var"X11" -> Int =
  lam cmp3.
    lam a43.
      lam b7: #var"X11".
        let x160: Int = cmp3 a43 b7 in
        x160
in
let ifCont = lam acc12.
    lam #var"9": Int.
      acc12 in
let ifCont1 = lam #var"8": Int.
    0. in
let exp1: Float -> Float = lam x159: Float.
    mathExp x159 in
let log1: Float -> Float = lam x158: Float.
    mathLog x158 in
let cons1: all #var"X10". #var"X10" -> [#var"X10"] -> [#var"X10"] =
  lam e1: #var"X10".
    lam s8: [#var"X10"].
      seqCons e1 s8
in
let rep: all #var"X9". Int -> #var"X9" -> [#var"X9"] =
  lam count: Int.
    lam elem1: #var"X9".
      make count elem1
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
let sapply: all #var"A6". all #var"B6". [#var"A6"] -> (#var"A6" -> #var"B6") -> [#var"B6"] =
  lam s7: [#var"A6"].
    lam f14: #var"A6" -> #var"B6".
      seqMap f14 s7
in
let anon16: all #var"B5". all #var"A5". (#var"A5" -> #var"B5" -> #var"A5") -> #var"A5" -> #var"B5" -> #var"A5" = lam f13.
    lam a42: #var"A5".
      x1 f13 a42
in
let fold: all #var"A4". all #var"B4". (#var"A4" -> #var"B4" -> #var"A4") -> #var"A4" -> [#var"B4"] -> #var"A4" =
  lam f12: #var"A4" -> #var"B4" -> #var"A4".
    lam init1: #var"A4".
      lam seq5: [#var"B4"].
        seqFoldl (anon16 f12) init1 seq5
in
let anon17: all #var"B3". all #var"A3". (#var"A3" -> Int -> #var"B3" -> #var"A3") -> #var"A3" -> Int -> #var"B3" -> #var"A3" = lam f11.
    lam a41: #var"A3".
      x3 f11 a41
in
let foldi: all #var"A2". all #var"B2". (#var"A2" -> Int -> #var"B2" -> #var"A2") -> #var"A2" -> [#var"B2"] -> #var"A2" =
  lam f10: #var"A2" -> Int -> #var"B2" -> #var"A2".
    lam init: #var"A2".
      lam seq4: [#var"B2"].
        seqFoldli (anon17 f10) init seq4
in
let anon18: all #var"C1". all #var"B1". all #var"A1". (#var"A1" -> #var"B1" -> #var"C1") -> #var"A1" -> #var"B1" -> #var"C1" = lam f9.
    lam a40: #var"A1".
      x4 f9 a40
in
let zipWith1: all #var"A". all #var"B". all #var"C". (#var"A" -> #var"B" -> #var"C") -> [#var"A"] -> [#var"B"] -> [#var"C"] =
  lam f8: #var"A" -> #var"B" -> #var"C".
    lam a39: [#var"A"].
      lam b6: [#var"B"].
        seqZipWith (anon18 f8) a39 b6
in
let any1: all #var"X5". (#var"X5" -> Bool) -> [#var"X5"] -> Bool =
  lam f7: #var"X5" -> Bool.
    lam l2: [#var"X5"].
      seqAny f7 l2
in
let anon19: all #var"X4". (#var"X4" -> #var"X4" -> Int) -> #var"X4" -> #var"X4" -> Int = lam cmp2.
    lam a38: #var"X4".
      x5 cmp2 a38
in
let qSort: all #var"X3". (#var"X3" -> #var"X3" -> Int) -> [#var"X3"] -> [#var"X3"] =
  lam cmp1: #var"X3" -> #var"X3" -> Int.
    lam l1: [#var"X3"].
      quickSort (anon19 cmp1) l1
in
let anon20: [Int] -> Int -> Bool -> [Int] =
  lam acc11: [Int].
    lam idx7: Int.
      lam elem: Bool.
        let x157: [Int] =
          match elem with true
          then
            seqSnoc acc11 idx7
          else
            ifCont acc11 0
        in
        x157
in
let whichTrue: [Bool] -> [Int] = lam s6: [Bool].
    foldi anon20 "" s6
in
let bool2real: Bool -> Float =
  lam v: Bool.
    match v with true
    then
      1.
    else
      ifCont1 0
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
      lam mtx6: Matrix #var"X2".
        matGetExn mtx6 (subi row1 1) (subi col 1)
in
let mtxRowCols: all #var"X1". Matrix #var"X1" -> Int -> [Int] -> Matrix #var"X1" =
  lam mtx5: Matrix #var"X1".
    lam row: Int.
      lam cols: [Int].
        matRowCols mtx5 row cols
in
let mtxSclrMul: Float -> Matrix Float -> Matrix Float =
  lam scalar: Float.
    lam mtx4: Matrix Float.
      matScale scalar mtx4
in
let mtxTrans: Matrix Float -> Matrix Float = lam mtx3: Matrix Float.
    matTranspose mtx3
in
let mtxExpRateSafe: Matrix Float -> Matrix Float = lam mtx2: Matrix Float.
    matExpRateSafe mtx2
in
let mtxMul: Matrix Float -> Matrix Float -> Matrix Float =
  lam a37: Matrix Float.
    lam b5: Matrix Float.
      matMulExn a37 b5
in
let mtxElemMul: Matrix Float -> Matrix Float -> Matrix Float =
  lam a36: Matrix Float.
    lam b4: Matrix Float.
      matElemMulExn a36 b4
in
let mtxMean: Matrix Float -> Float = lam mtx1: Matrix Float.
    matMean mtx1
in
let mathIsNaN = isNaN in
let delta =
  lam k1.
    lam x156.
      match eqi k1 x156 with true
      then
        1.
      else
        0.
in
let seqKroneckerDelta: Int -> Int -> [Float] =
  lam i13: Int.
    lam n2: Int.
      let k = subi i13 1 in
      map1 (delta k) (range 0 n2 1)
in
let kroneckerDelta: Int -> Int -> [Float] =
  lam index: Int.
    lam length2: Int.
      seqKroneckerDelta index length2
in
let isNaN1: Float -> Bool = lam r2: Float.
    mathIsNaN r2 in
let nestSeqToMtx: [[Float]] -> Matrix Float =
  lam ns: [[Float]].
    let n1 = length1 ns in
    let m = length1 (get ns (subi 1 1)) in
    mtxCreate n1 m (paste0 ns)
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
con ModelParams1: {beta: Float, meanDist: Float, hostMetric: Matrix Float, embeddedQMatrix: EmbeddedMarkovChainMatrix} -> ModelParams
in
con EmbeddedMarkovChainMatrix1: {mat: Matrix Float, totalRates: [Float], transitionProbs: [[Float]]} -> EmbeddedMarkovChainMatrix
in
let rateMatrixToEmbeddedMarkovChain: Matrix Float -> EmbeddedMarkovChainMatrix =
  lam qMatrix3: Matrix Float.
    let q1 = negf (mtxGet 1 1 qMatrix3) in
    let q2 = negf (mtxGet 2 2 qMatrix3) in
    let q3 = negf (mtxGet 3 3 qMatrix3) in
    EmbeddedMarkovChainMatrix1
      { totalRates = [ q1,
            q2,
            q3 ],
        transitionProbs =
          [ [ 0., 1., 0. ],
            [ divf (mtxGet 2 1 qMatrix3) q2,
              0.,
              divf (mtxGet 2 3 qMatrix3) q2 ],
            [ 0., 1., 0. ] ],
        mat = qMatrix3 }
in
let is2: Int -> Bool = lam x155: Int.
    eqi x155 2 in
recursive
  let ones: Int -> [Float] =
    lam nOnes: Int.
      match gti nOnes 0 with true
      then
        cons1 1. (ones (subi nOnes 1))
      else
        ""
in
let anon21: Int -> Int -> Int =
  lam acc10: Int.
    lam h4: Int.
      let x154: Int =
        match eqi h4 2 with true
        then
          addi acc10 1
        else
          acc10
      in
      x154
in
let n2s: [Int] -> Int = lam repertoire2: [Int].
    fold anon21 0 repertoire2
in
let updateRepertoire: [Int] -> Event -> Int -> [Int] =
  lam currRep8: [Int].
    lam event3: Event.
      lam nhosts8: Int.
        let hostIndex4 =
          let target88 = event3 in
          match target88 with Event1 x153
          then
            x153.host
          else
            let #var"2" =
              print
                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 52:18-52:28>:\nField \'host\' not found\n[0m  let hostIndex = [31mevent.host[0m[0m;\n"
            in
            exit 1
        in
        paste0
          [ slice currRep8 1 hostIndex4,
            [ let target87 = event3 in
              match target87 with Event1 x152
              then
                x152.toState
              else
                let #var"2" =
                  print
                    "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/helpers.tppl 56:7-56:20>:\nField \'toState\' not found\n[0m      [[31mevent.toState[0m[0m],\n"
                in
                exit 1 ],
            slice currRep8 (addi hostIndex4 1) (addi nhosts8 1) ]
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
recursive
  let observationMessage: [Int] -> Int -> Int -> [Float] =
    lam obsRepertoire: [Int].
      lam i5: Int.
        lam max: Int.
          match leqi i5 max with true
          then
            let stateMsg = makeStateMessage (get obsRepertoire (subi i5 1))
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
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 19:31-19:40>:\nField \'left\' not found\n[0m  let left = postorderTraverse([31mtree.left[0m[0m, qMatrix, interactions, nhosts);\n"
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
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 20:32-20:42>:\nField \'right\' not found\n[0m  let right = postorderTraverse([31mtree.right[0m[0m, qMatrix, interactions, nhosts);\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:45-23:53>:\nField \'age\' not found\n[0m  let leftKernel = mtxExpRateSafe(mtxSclrMul([31mtree.age[0m[0m-left.age, qMatrix));\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 23:54-23:62>:\nField \'age\' not found\n[0m  let leftKernel = mtxExpRateSafe(mtxSclrMul(tree.age-[31mleft.age[0m[0m, qMatrix));\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:46-24:54>:\nField \'age\' not found\n[0m  let rightKernel = mtxExpRateSafe(mtxSclrMul([31mtree.age[0m[0m-right.age, qMatrix));\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 24:55-24:64>:\nField \'age\' not found\n[0m  let rightKernel = mtxExpRateSafe(mtxSclrMul(tree.age-[31mright.age[0m[0m, qMatrix));\n"
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
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 30:25-30:36>:\nField \'outMsg\' not found\n[0m  let leftInMsg = mtxMul([31mleft.outMsg[0m[0m, leftBackwardKernel);\n"
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
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 31:26-31:38>:\nField \'outMsg\' not found\n[0m  let rightInMsg = mtxMul([31mright.outMsg[0m[0m, rightBackwardKernel);\n"
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
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:10-36:18>:\nField \'age\' not found\n[0m    age = [31mtree.age[0m[0m, label = tree.label,\n"
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
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 36:28-36:38>:\nField \'label\' not found\n[0m    age = tree.age, label = [31mtree.label[0m[0m,\n"
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
                mtxCreate
                  nhosts1
                  3
                  (observationMessage
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
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 10:32-10:42>:\nField \'label\' not found\n[0m    let leafInts = interactions[[31mtree.label[0m[0m];\n"
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
                          "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/belief-propagation.tppl 13:14-13:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
                      in
                      exit 1,
                  outMsg =
                    mtxCreate nhosts1 3 (observationMessage leafInts 1 nhosts1),
                  interactions = leafInts }
            else
              ifCont2 tree1 qMatrix1 interactions1 nhosts1 0
in
let categoricalLogPdf: Int -> [Float] -> Float =
  lam x151: Int.
    lam params: [Float].
      match
        match geqi x151 0 with true
        then
          lti x151 (length1 params)
        else
          false
      with
        true
      then
        log1 (get params (subi (addi x151 1) 1))
      else
        log1 0.
in
let mtx3ToSeq: Matrix Float -> Int -> [Float] =
  lam mtx: Matrix Float.
    lam i12: Int.
      let p11 = mtxGet i12 1 mtx in
      let p2 = mtxGet i12 2 mtx in
      let p3 = mtxGet i12 3 mtx in
      let s5 = addf (addf p11 p2) p3 in
      [ divf p11 s5,
        divf p2 s5,
        divf p3 s5 ]
in
let anon22: [Int] -> Matrix Float -> Float -> Int -> Float =
  lam x149.
    lam samplingProb2.
      lam acc9: Float.
        lam i11: Int.
          let x150: Float =
            let param6 = mtx3ToSeq samplingProb2 i11 in
            addf acc9 (categoricalLogPdf (get x149 (subi i11 1)) param6)
          in
          x150
in
let anon23: Int -> Int -> Int = lam start13.
    lam idx6.
      addi idx6 start13
in
let getRepertoireSamplingDensity: [Int] -> Matrix Float -> Int -> Float =
  lam x148: [Int].
    lam samplingProb1: Matrix Float.
      lam nhosts7: Int.
        fold
          (anon22 x148 samplingProb1)
          0.
          (let start12 = 1 in
           let end7 = nhosts7 in
           create1 (addi (subi end7 start12) 1) (anon23 start12))
in
let anon24: Int -> Int -> Int =
  lam acc8: Int.
    lam h3: Int.
      let x147: Int =
        match eqi h3 2 with true
        then
          addi acc8 1
        else
          acc8
      in
      x147
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
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 146:7-146:22>:\nField \'fromState\' not found\n[0m    if [31mevent.fromState[0m[0m == 2 {\n"
                       in
                       exit 1)
                    2
                with
                  true
                then
                  let n2s1 = fold anon24 0 currRep1 in
                  match eqi n2s1 1 with true
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
let anon25: Int -> Bool =
  lam i10: Int.
    let x146: Bool =
      match eqi i10 2 with true
      then
        true
      else
        eqi i10 1
    in
    x146
in
let anon26: Int -> Bool = lam i9: Int.
    let x145: Bool = eqi i9 2 in
    x145
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
            (let target85 =
               let target86 = modelParams12 in
               match target86 with ModelParams1 x144
               then
                 x144.embeddedQMatrix
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:79>:\nField \'embeddedQMatrix\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                 in
                 exit 1
             in
             match target85 with EmbeddedMarkovChainMatrix1 x143
             then
               x143.mat
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 112:52-112:83>:\nField \'mat\' not found\n[0m  let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
               in
               exit 1)
        in
        match eqi fromState5 0 with true
        then
          let currentHosts = whichTrue (sapply repertoire1 anon25) in
          let dist =
            mtxMean
              (mtxRowCols
                 (let target81 = modelParams12 in
                  match target81 with ModelParams1 x139
                  then
                    x139.hostMetric
                  else
                    let #var"2" =
                      print
                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 118:6-118:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                    in
                    exit 1)
                 hostIndex3
                 currentHosts)
          in
          mulf
            baseRate1
            (pow
               (divf
                  dist
                  (let target79 = modelParams12 in
                   match target79 with ModelParams1 x137
                   then
                     x137.meanDist
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:14-122:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                     in
                     exit 1))
               (negf
                  (let target80 = modelParams12 in
                   match target80 with ModelParams1 x138
                   then
                     x138.beta
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 122:38-122:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                     in
                     exit 1)))
        else
          let currentHosts1 = whichTrue (sapply repertoire1 anon26) in
          let dist1 =
            mtxMean
              (mtxRowCols
                 (let target84 = modelParams12 in
                  match target84 with ModelParams1 x142
                  then
                    x142.hostMetric
                  else
                    let #var"2" =
                      print
                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 127:6-127:28>:\nField \'hostMetric\' not found\n[0m      [31mmodelParams.hostMetric[0m[0m, hostIndex, currentHosts\n"
                    in
                    exit 1)
                 hostIndex3
                 currentHosts1)
          in
          mulf
            baseRate1
            (pow
               (divf
                  dist1
                  (let target82 = modelParams12 in
                   match target82 with ModelParams1 x140
                   then
                     x140.meanDist
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:14-131:34>:\nField \'meanDist\' not found\n[0m      (dist / [31mmodelParams.meanDist[0m[0m)^(-modelParams.beta)\n"
                     in
                     exit 1))
               (negf
                  (let target83 = modelParams12 in
                   match target83 with ModelParams1 x141
                   then
                     x141.beta
                   else
                     let #var"2" =
                       print
                         "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 131:38-131:54>:\nField \'beta\' not found\n[0m      (dist / modelParams.meanDist)^(-[31mmodelParams.beta[0m[0m)\n"
                     in
                     exit 1)))
in
let anon27: [Int] -> ModelParams -> Float -> Int -> Float =
  lam currRep7.
    lam modelParams11.
      lam acc7: Float.
        lam i8: Int.
          let x136: Float =
            let fromState4 = get currRep7 (subi i8 1) in
            match eqi fromState4 2 with true
            then
              acc7
            else
              addf acc7 (getGainRate currRep7 i8 modelParams11)
          in
          x136
in
let anon28: Int -> Int -> Int = lam start11.
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
            eqi (n2s repertoire) 1
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
              (let target77 =
                 let target78 = modelParams10 in
                 match target78 with ModelParams1 x135
                 then
                   x135.embeddedQMatrix
                 else
                   let #var"2" =
                     print
                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:81>:\nField \'embeddedQMatrix\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix[0m[0m.mat);\n"
                   in
                   exit 1
               in
               match target77 with EmbeddedMarkovChainMatrix1 x134
               then
                 x134.mat
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 100:54-100:85>:\nField \'mat\' not found\n[0m    let baseRate = mtxGet(fromState + 1, toState + 1, [31mmodelParams.embeddedQMatrix.mat[0m[0m);\n"
                 in
                 exit 1)
          in
          baseRate
in
let anon29: [Int] -> ModelParams -> Float -> Int -> Float =
  lam currRep6.
    lam modelParams9.
      lam acc6: Float.
        lam i7: Int.
          let x133: Float =
            let fromState2 = get currRep6 (subi i7 1) in
            match eqi fromState2 0 with true
            then
              acc6
            else
              addf acc6 (getLossRate currRep6 i7 modelParams9)
          in
          x133
in
let anon30: Int -> Int -> Int = lam start10.
    lam idx4.
      addi idx4 start10
in
let getTotalRate: [Int] -> ModelParams -> Int -> Float =
  lam currRep5: [Int].
    lam modelParams8: ModelParams.
      lam nhosts6: Int.
        let gainRates =
          fold
            (anon27 currRep5 modelParams8)
            0.
            (let start9 = 1 in
             let end6 = nhosts6 in
             create1 (addi (subi end6 start9) 1) (anon28 start9))
        in
        let lossRates =
          fold
            (anon29 currRep5 modelParams8)
            0.
            (let start8 = 1 in
             let end5 = nhosts6 in
             create1 (addi (subi end5 start8) 1) (anon30 start8))
        in
        addf gainRates lossRates
in
let getRate: [Int] -> Event -> ModelParams -> Float =
  lam currRep4: [Int].
    lam nextEvent2: Event.
      lam modelParams7: ModelParams.
        let hostIndex1 =
          let target76 = nextEvent2 in
          match target76 with Event1 x132
          then
            x132.host
          else
            let #var"2" =
              print
                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 83:18-83:32>:\nField \'host\' not found\n[0m  let hostIndex = [31mnextEvent.host[0m[0m;\n"
            in
            exit 1
        in
        match
          gti
            (let target74 = nextEvent2 in
             match target74 with Event1 x130
             then
               x130.fromState
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:5-84:24>:\nField \'fromState\' not found\n[0m  if [31mnextEvent.fromState[0m[0m > nextEvent.toState {\n"
               in
               exit 1)
            (let target75 = nextEvent2 in
             match target75 with Event1 x131
             then
               x131.toState
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 84:27-84:44>:\nField \'toState\' not found\n[0m  if nextEvent.fromState > [31mnextEvent.toState[0m[0m {\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/full-model.tppl 27:17-27:36>:\nField \'eventTime\' not found\n[0m    let newAge = [31mnextEvent.eventTime[0m[0m;\n"
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
let newParamFun =
  lam alpha2.
    lam epsilon1.
      lam a35: Float.
        let x129: Float =
          match gtf a35 epsilon1 with true
          then
            match ltf a35 (subf 1. epsilon1) with true
            then
              mulf a35 alpha2
            else
              mulf (subf a35 epsilon1) alpha2
          else
            mulf (addf a35 epsilon1) alpha2
        in
        x129
in
let simplexMove: [Float] -> Float -> Float -> Dist([Float]) =
  lam x128: [Float].
    lam alpha1: Float.
      lam epsilon: Float.
        let newParams = sapply x128 (newParamFun alpha1 epsilon) in
        Dirichlet newParams
in
let scaleMove: Float -> Float -> Dist(Float) =
  lam x127: Float.
    lam lambda6: Float.
      Reciprocal
        (mulf x127 (exp1 (divf (negf lambda6) 2.)))
        (mulf x127 (exp1 (divf lambda6 2.)))
in
let anon31: Int -> Int -> Int = lam start7.
    lam idx3.
      addi idx3 start7
in
let anon32: Int -> [Float] -> Float -> Float -> Int -> Float =
  lam x125.
    lam param5.
      lam currProb1.
        lam nextProb1.
          lam i6: Int.
            let x126: Float =
              match eqi i6 x125 with true
              then
                nextProb1
              else
                divf
                  (mulf (get param5 (subi (addi i6 1) 1)) (subf 1. nextProb1))
                  (subf 1. currProb1)
            in
            x126
in
let categoricalShiftKernel: Int -> [Float] -> Float -> Float -> Dist(Int) =
  lam x124: Int.
    lam param4: [Float].
      lam lambda5: Float.
        lam errMargin1: Float.
          let currProb = get param4 (subi (addi x124 1) 1) in
          match ltf currProb (subf 1. errMargin1) with true
          then
            let nextProb = mulf currProb (subf 1. lambda5) in
            let newParam =
              sapply
                (let start6 = 1 in
                 let end4 = length1 param4 in
                 create1 (addi (subi end4 start6) 1) (anon31 start6))
                (anon32 x124 param4 currProb nextProb)
            in
            Categorical newParam
          else
            Categorical param4
in
let rbLambdaMove: [Float] -> Dist([Float]) =
  lam x123: [Float].
    let _EPSILON = 0.001 in
    let alpha = 25. in
    simplexMove x123 alpha _EPSILON
in
let rbBetaMove: Float -> Dist(Float) =
  lam x122: Float.
    let lambda4 = 1. in
    scaleMove x122 lambda4
in
let rbMuMove: Float -> Dist(Float) =
  lam x121: Float.
    let lambda3 = 0.2 in
    scaleMove x121 lambda3
in
let categoricalMove: Int -> [Float] -> Dist(Int) =
  lam x120: Int.
    lam param3: [Float].
      let lambda2 = 0.9 in
      let errMargin = 1e-06 in
      categoricalShiftKernel x120 param3 lambda2 errMargin
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
let anon33: [Int] -> [Int] -> Float -> Float -> [[Event]] -> ModelParams -> Float -> Int -> Float =
  lam fromRep2.
    lam toRep2.
      lam fromAge2.
        lam toAge2.
          lam eventSeqs2.
            lam modelParams6.
              lam acc5: Float.
                lam h2: Int.
                  let x118: Float =
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
                         (let target73 = modelParams6 in
                          match target73 with ModelParams1 x119
                          then
                            x119.embeddedQMatrix
                          else
                            let #var"2" =
                              print
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/host-rep-lib/independence-model.tppl 23:8-23:35>:\nField \'embeddedQMatrix\' not found\n[0m        [31mmodelParams.embeddedQMatrix[0m\n"
                            in
                            exit 1))
                  in
                  x118
in
let anon34: Int -> Int -> Int = lam start5.
    lam idx2.
      addi idx2 start5
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
                  (anon33 fromRep1 toRep1 fromAge1 toAge1 eventSeqs1 modelParams5)
                  0.
                  (let start4 = 1 in
                   let end3 = length1 eventSeqs1 in
                   create1 (addi (subi end3 start4) 1) (anon34 start4))
              in
              unconditional1
in
let anon35: Float -> Float -> Float =
  lam acc4: Float.
    lam val: Float.
      let x117: Float = addf acc4 val in
      x117
in
let anon36: Matrix Float -> Int -> Int -> Float =
  lam kernel1.
    lam fromState: Int.
      lam toState: Int.
        let x116: Float = log1 (mtxGet (addi fromState 1) (addi toState 1) kernel1)
        in
        x116
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
                let logTotalTransProb = fold anon35 0. (zipWith1 (anon36 kernel) fromRep toRep)
                in
                let conditional = subf unconditional logTotalTransProb in
                conditional
in
type ReturnType in
type Bridge in
con ReturnType1: {mu: Float, beta: Float, tree: HistoryTree, lambda: [Float]} -> ReturnType
in
con Bridge1: {events: [Event], success: Bool} -> Bridge in
let ifCont5 =
  lam left4.
    lam right4.
      lam #var"7": Int.
        match
          geqf
            (let target71 = right4 in
             match target71 with Event1 x114
             then
               x114.eventTime
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 247:6-247:21>:\nField \'eventTime\' not found\n[0m  if ([31mright.eventTime[0m[0m >= left.eventTime) {\n"
               in
               exit 1)
            (let target72 = left4 in
             match target72 with Event1 x115
             then
               x115.eventTime
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 247:25-247:39>:\nField \'eventTime\' not found\n[0m  if (right.eventTime >= [31mleft.eventTime[0m[0m) {\n"
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
            (let target70 = left3 in
             match target70 with Event1 x113
             then
               x113.eventTime
             else
               let #var"2" =
                 print
                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 244:12-244:26>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mleft.eventTime[0m[0m)) {\n"
               in
               exit 1)
        with
          true
        then
          1
        else
          ifCont5 left3 right3 0
in
let anon37: Int -> Int -> Int = lam start3.
    lam idx1.
      addi idx1 start3
in
let anon38: [Float] -> Int -> Dist(Int) = lam param2.
    lam x112.
      categoricalMove x112 param2
in
let anon39: Matrix Float -> Int -> Int -> Int =
  lam msg1.
    lam nodeLabel6.
      lam h1: Int.
        let x110: Int =
          let param1 = mtx3ToSeq msg1 (addi h1 (muli nodeLabel6 0)) in
          let x111 = assume
              (Categorical param1) in
          x111
        in
        x110
in
let suggestNodeRep: Matrix Float -> Int -> Int -> [Int] =
  lam msg: Matrix Float.
    lam nHosts4: Int.
      lam nodeLabel5: Int.
        sapply
          (let start2 = 1 in
           let end2 = nHosts4 in
           create1 (addi (subi end2 start2) 1) (anon37 start2))
          (anon39 msg nodeLabel5)
in
let compAge: Event -> Event -> Int =
  lam left2: Event.
    lam right2: Event.
      match
        isNaN1
          (let target69 = right2 in
           match target69 with Event1 x109
           then
             x109.eventTime
           else
             let #var"2" =
               print
                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 241:12-241:27>:\nField \'eventTime\' not found\n[0m  if (isNaN([31mright.eventTime[0m[0m)) {\n"
             in
             exit 1)
      with
        true
      then
        negi 1
      else
        ifCont6 left2 right2 0
in
let anon40: Int -> Int -> Int = lam start1.
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 323:16-323:47>:\nField \'transitionProbs\' not found\n[0m    let param = [31membeddedQMatrix.transitionProbs[0m[0m[currentState + 1];\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 327:20-327:46>:\nField \'totalRates\' not found\n[0m    let totalRate = [31membeddedQMatrix.totalRates[0m[0m[nextState + 1];\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 345:18-345:39>:\nField \'success\' not found\n[0m      , success = [31mrestOfHistory.success[0m\n"
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
                                   "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 343:10-343:30>:\nField \'events\' not found\n[0m          [31mrestOfHistory.events[0m\n"
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
                    (let target68 = embeddedQMatrix5 in
                     match target68 with EmbeddedMarkovChainMatrix1 x108
                     then
                       x108.totalRates
                     else
                       let #var"2" =
                         print
                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 292:18-292:44>:\nField \'totalRates\' not found\n[0m  let totalRate = [31membeddedQMatrix.totalRates[0m[0m[startState + 1];\n"
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
                                (let target67 = bridge in
                                 match target67 with Bridge1 x107
                                 then
                                   x107.success
                                 else
                                   let #var"2" =
                                     print
                                       "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 304:19-304:33>:\nField \'success\' not found\n[0m  weight bool2real([31mbridge.success[0m[0m) + Real(host) * 0. + Real(nodeLabel) * 0.;\n"
                                   in
                                   exit 1))
                             (mulf (int2float host1) 0.))
                          (mulf (int2float nodeLabel4) 0.)))
                in
                let target66 = bridge in
                match target66 with Bridge1 x106
                then
                  x106.events
                else
                  let #var"2" =
                    print
                      "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 305:9-305:22>:\nField \'events\' not found\n[0m  return [31mbridge.events[0m[0m;\n"
                  in
                  exit 1
in
let anon41: [Int] -> [Int] -> Float -> Float -> Int -> EmbeddedMarkovChainMatrix -> Int -> [Event] =
  lam startRep2.
    lam finalRep3.
      lam startAge2.
        lam finalAge5.
          lam nodeLabel3.
            lam embeddedQMatrix4.
              lam hostIndex: Int.
                let x105: [Event] =
                  sampleHostHistory
                    (get startRep2 (subi hostIndex 1))
                    (get finalRep3 (subi hostIndex 1))
                    startAge2
                    finalAge5
                    hostIndex
                    nodeLabel3
                    embeddedQMatrix4
                in
                x105
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
                   create1 (addi (subi end1 start) 1) (anon40 start))
                  (anon41
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
                      (let target65 = modelParams3 in
                       match target65 with ModelParams1 x104
                       then
                         x104.embeddedQMatrix
                       else
                         let #var"2" =
                           print
                             "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 201:4-201:31>:\nField \'embeddedQMatrix\' not found\n[0m    [31mmodelParams.embeddedQMatrix[0m\n"
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
                            "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 115:14-115:31>:\nField \'interactions\' not found\n[0m    let rep = [31mtree.interactions[0m[0m;\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 121:6-121:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 123:6-123:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
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
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:15-129:43>:\nField \'logModelDensity\' not found\n[0m    logWeight ([31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity) * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                              (let target28 = branchSample in
                               match target28 with CorrectedBranchSample1 x47
                               then
                                 x47.logSamplingDensity
                               else
                                 let #var"2" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:46-129:77>:\nField \'logSamplingDensity\' not found\n[0m    logWeight (branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m) * exp(Real(tree.label) * 0.);\n"
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
                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 129:90-129:100>:\nField \'label\' not found\n[0m    logWeight (branchSample.logModelDensity - branchSample.logSamplingDensity) * exp(Real([31mtree.label[0m[0m) * 0.);\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 132:12-132:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 133:14-133:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 135:16-135:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 138:34-138:45>:\nField \'outMsg\' not found\n[0m    let samplingProb = mtxElemMul([31mtree.outMsg[0m[0m, preorderMsg);\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 139:51-139:61>:\nField \'label\' not found\n[0m    let rep = suggestNodeRep(samplingProb, nHosts, [31mtree.label[0m[0m);\n"
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
                                           "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 141:43-141:53>:\nField \'label\' not found\n[0m    weight bool2real(any(is2, rep)) + Real([31mtree.label[0m[0m) * 0.;\n"
                                       in
                                       exit 1))
                                 0.)))
                    in
                    let nodeLogSamplingDensity = getRepertoireSamplingDensity rep2 samplingProb nHosts
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 149:6-149:14>:\nField \'age\' not found\n[0m      [31mtree.age[0m[0m,\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 151:6-151:16>:\nField \'label\' not found\n[0m      [31mtree.label[0m[0m,\n"
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
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:14-157:42>:\nField \'logModelDensity\' not found\n[0m    logWeight [31mbranchSample.logModelDensity[0m[0m - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
                                 in
                                 exit 1)
                              (let target45 = branchSample1 in
                               match target45 with CorrectedBranchSample1 x71
                               then
                                 x71.logSamplingDensity
                               else
                                 let #var"2" =
                                   print
                                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:45-157:76>:\nField \'logSamplingDensity\' not found\n[0m    logWeight branchSample.logModelDensity - [31mbranchSample.logSamplingDensity[0m[0m - nodeLogSamplingDensity * exp(Real(tree.label) * 0.);\n"
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
                                              "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 157:113-157:123>:\nField \'label\' not found\n[0m    logWeight branchSample.logModelDensity - branchSample.logSamplingDensity - nodeLogSamplingDensity * exp(Real([31mtree.label[0m[0m) * 0.);\n"
                                          in
                                          exit 1))
                                    0.))))
                    in
                    let newMsg = mtxCreate nHosts 3 (observationMessage rep2 1 nHosts)
                    in
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 161:33-161:48>:\nField \'leftKernel\' not found\n[0m    let leftMsg = mtxMul(newMsg, [31mtree.leftKernel[0m[0m);\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 162:34-162:50>:\nField \'rightKernel\' not found\n[0m    let rightMsg = mtxMul(newMsg, [31mtree.rightKernel[0m[0m);\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:6-166:15>:\nField \'left\' not found\n[0m      [31mtree.left[0m[0m, nHosts, leftMsg, rep, tree.age, modelParams, tree.leftKernel\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:39-166:47>:\nField \'age\' not found\n[0m      tree.left, nHosts, leftMsg, rep, [31mtree.age[0m[0m, modelParams, tree.leftKernel\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 166:62-166:77>:\nField \'leftKernel\' not found\n[0m      tree.left, nHosts, leftMsg, rep, tree.age, modelParams, [31mtree.leftKernel[0m\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 169:6-169:16>:\nField \'right\' not found\n[0m      [31mtree.right[0m[0m, nHosts, rightMsg, rep, tree.age, modelParams, tree.rightKernel\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 169:41-169:49>:\nField \'age\' not found\n[0m      tree.right, nHosts, rightMsg, rep, [31mtree.age[0m[0m, modelParams, tree.rightKernel\n"
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
                               "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 169:64-169:80>:\nField \'rightKernel\' not found\n[0m      tree.right, nHosts, rightMsg, rep, tree.age, modelParams, [31mtree.rightKernel[0m\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 173:12-173:20>:\nField \'age\' not found\n[0m      age = [31mtree.age[0m[0m,\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 174:14-174:24>:\nField \'label\' not found\n[0m      label = [31mtree.label[0m[0m,\n"
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
                                "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 176:16-176:36>:\nField \'history\' not found\n[0m      history = [31mbranchSample.history[0m[0m,\n"
                            in
                            exit 1 }
in
let anon42: [Float] -> Dist([Float]) = lam lambda1.
    rbLambdaMove lambda1
in
let anon43: Float -> Dist(Float) = lam mu1.
    rbMuMove mu1 in
let anon44: Float -> Dist(Float) = lam beta1.
    rbBetaMove beta1
in
let hostRepertoireModel: TreeLabeled -> [[Int]] -> [[Float]] -> Float -> ReturnType =
  lam symbiontTree: TreeLabeled.
    lam interactions2: [[Int]].
      lam hostDistances: [[Float]].
        lam dMean: Float.
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
          let postorderTree =
            postorderTraverse symbiontTree qMatrix2 interactions2 nHosts1
          in
          let rootPrior = mtxCreate nHosts1 3 (ones (muli 3 nHosts1)) in
          let rootSamplingProb =
            mtxElemMul
              (let target64 = postorderTree in
               match target64 with MsgNode x102
               then
                 x102.outMsg
               else match target64 with MsgLeaf x103
               then
                 x103.outMsg
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 39:36-39:56>:\nField \'outMsg\' not found\n[0m  let rootSamplingProb = mtxElemMul([31mpostorderTree.outMsg[0m[0m, rootPrior);\n"
                 in
                 exit 1)
              rootPrior
          in
          let rootRep =
            suggestNodeRep
              rootSamplingProb
              nHosts1
              (let target63 = postorderTree in
               match target63 with MsgNode x100
               then
                 x100.label
               else match target63 with MsgLeaf x101
               then
                 x101.label
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 40:57-40:76>:\nField \'label\' not found\n[0m  let rootRep = suggestNodeRep(rootSamplingProb, nHosts, [31mpostorderTree.label[0m[0m);\n"
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
                          (let target62 = postorderTree in
                           match target62 with MsgNode x98
                           then
                             x98.label
                           else match target62 with MsgLeaf x99
                           then
                             x99.label
                           else
                             let #var"2" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 42:45-42:64>:\nField \'label\' not found\n[0m  weight bool2real(any(is2, rootRep)) + Real([31mpostorderTree.label[0m[0m) * 0.;\n"
                             in
                             exit 1))
                       0.)))
          in
          let rootLogSamplingDensity =
            getRepertoireSamplingDensity rootRep rootSamplingProb nHosts1
          in
          let rootLogModelDensity =
            negf
              (log1
                 (subf (pow 3. (int2float nHosts1)) (pow 2. (int2float nHosts1))))
          in
          let foo4 =
            weight
              (mulf
                 (subf rootLogModelDensity rootLogSamplingDensity)
                 (exp1
                    (mulf
                       (int2float
                          (let target61 = postorderTree in
                           match target61 with MsgNode x96
                           then
                             x96.label
                           else match target61 with MsgLeaf x97
                           then
                             x97.label
                           else
                             let #var"2" =
                               print
                                 "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 49:70-49:89>:\nField \'label\' not found\n[0m  logWeight (rootLogModelDensity - rootLogSamplingDensity) * exp(Real([31mpostorderTree.label[0m[0m) * 0.);\n"
                             in
                             exit 1))
                       0.)))
          in
          let newMsg1 = mtxCreate nHosts1 3 (observationMessage rootRep 1 nHosts1)
          in
          let leftMsg1 =
            mtxMul
              newMsg1
              (let target60 = postorderTree in
               match target60 with MsgNode x95
               then
                 x95.leftKernel
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 53:31-53:55>:\nField \'leftKernel\' not found\n[0m  let leftMsg = mtxMul(newMsg, [31mpostorderTree.leftKernel[0m[0m);\n"
                 in
                 exit 1)
          in
          let rightMsg1 =
            mtxMul
              newMsg1
              (let target59 = postorderTree in
               match target59 with MsgNode x94
               then
                 x94.rightKernel
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 54:32-54:57>:\nField \'rightKernel\' not found\n[0m  let rightMsg = mtxMul(newMsg, [31mpostorderTree.rightKernel[0m[0m);\n"
                 in
                 exit 1)
          in
          let embeddedQMatrix2 = rateMatrixToEmbeddedMarkovChain qMatrix2
          in
          let modelParams2 =
            ModelParams1
              { beta = beta,
                hostMetric = nestSeqToMtx hostDistances,
                embeddedQMatrix = embeddedQMatrix2,
                meanDist = dMean }
          in
          let rootAge =
            let target58 = postorderTree in
            match target58 with MsgNode x92
            then
              x92.age
            else match target58 with MsgLeaf x93
            then
              x93.age
            else
              let #var"2" =
                print
                  "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 65:16-65:33>:\nField \'age\' not found\n[0m  let rootAge = [31mpostorderTree.age[0m[0m;\n"
              in
              exit 1
          in
          let leftRepertoireTree =
            sampleTreeHistory
              (let target56 = postorderTree in
               match target56 with MsgNode x90
               then
                 x90.left
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 67:4-67:22>:\nField \'left\' not found\n[0m    [31mpostorderTree.left[0m[0m, nHosts, leftMsg, rootRep, rootAge, modelParams, postorderTree.leftKernel\n"
                 in
                 exit 1)
              nHosts1
              leftMsg1
              rootRep
              rootAge
              modelParams2
              (let target57 = postorderTree in
               match target57 with MsgNode x91
               then
                 x91.leftKernel
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 67:72-67:96>:\nField \'leftKernel\' not found\n[0m    postorderTree.left, nHosts, leftMsg, rootRep, rootAge, modelParams, [31mpostorderTree.leftKernel[0m\n"
                 in
                 exit 1)
          in
          let rightRepertoireTree =
            sampleTreeHistory
              (let target54 = postorderTree in
               match target54 with MsgNode x88
               then
                 x88.right
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 71:4-71:23>:\nField \'right\' not found\n[0m    [31mpostorderTree.right[0m[0m, nHosts, rightMsg, rootRep, rootAge, modelParams, postorderTree.rightKernel\n"
                 in
                 exit 1)
              nHosts1
              rightMsg1
              rootRep
              rootAge
              modelParams2
              (let target55 = postorderTree in
               match target55 with MsgNode x89
               then
                 x89.rightKernel
               else
                 let #var"2" =
                   print
                     "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 71:74-71:99>:\nField \'rightKernel\' not found\n[0m    postorderTree.right, nHosts, rightMsg, rootRep, rootAge, modelParams, [31mpostorderTree.rightKernel[0m\n"
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
                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 76:10-76:26>:\nField \'age\' not found\n[0m    age = [31msymbiontTree.age[0m[0m, label = symbiontTree.label,\n"
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
                        "ERROR </home/ed/treeppl-compiler-chain/treeppl/models/host-repertoire-evolution/simple-HRM.tppl 76:36-76:54>:\nField \'label\' not found\n[0m    age = symbiontTree.age, label = [31msymbiontTree.label[0m[0m,\n"
                    in
                    exit 1,
                repertoire = rootRep,
                history = "" }
          in
          ReturnType1
            { lambda = lambda, mu = mu, beta = beta, tree = historyTree }
in
let anon45: {dMean: Float, interactions: [[Int]], symbiontTree: TreeLabeled, hostDistances: [[Float]]} -> () -> ReturnType =
  lam input1.
    lam #var"5".
      hostRepertoireModel
        input1.symbiontTree
        input1.interactions
        input1.hostDistances
        input1.dMean
in
anon45 input {}
