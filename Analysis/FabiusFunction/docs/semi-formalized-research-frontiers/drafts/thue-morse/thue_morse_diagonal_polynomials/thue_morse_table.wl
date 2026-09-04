(* ::Package:: *)

(*
  Fast exact evaluation of the repeated signed Thue--Morse summation table
  ------------------------------------------------------------------------

  The table is the one defined in the accompanying article by

      s[n,k] = Sum[(k-j) s[n-1,j], {j,0,k-1}],

  with the signed Thue--Morse prefix as row n=0.  Three complementary
  evaluation modes are supplied:

    diagonalPolynomial[r]   symbolic polynomial D_r(x) for any diagonal;
    sDiagonalValue[n,k]     direct exact value from the finite diagonal sum;
    sFast[n,k]              hybrid arbitrary-entry evaluator using the exact
                             dyadic block symmetries before the diagonal sum;
    rowBlock[n]             complete first block, useful for many lookups at
                             one moderate row index n.

  All arithmetic is exact.  No floating-point approximations are used.
*)

ClearAll[
  tmSign, x, z,
  diagonalPolynomial, diagonalRuler,
  sDiagonalValue, rowCoreValue, sFast,
  rowBlockPolynomial, rowBlock, sByBlock
];

(* Signed Thue--Morse value epsilon_q = (-1)^(binary digit sum of q). *)
tmSign[q_Integer?NonNegative] := (-1)^ThueMorse[q];


(* ---------------------------------------------------------------------- *)
(* 1. The polynomial on an arbitrary diagonal                            *)
(* ---------------------------------------------------------------------- *)

(*
  D_r(x) is characterized by

      Sum[D_r(x) z^r, {r,0,Infinity}] = E(z^2)/(1-z)^(2x),

  where E(z)=Product[1-z^(2^j),{j,0,Infinity}].  The following finite sum
  is exact and is usually the fastest way to obtain one symbolic diagonal.
*)
diagonalPolynomial[0] = 1;
diagonalPolynomial[r_Integer?Positive] :=
  diagonalPolynomial[r] = Expand@Sum[
    tmSign[q] Pochhammer[2 x, r - 2 q]/Factorial[r - 2 q],
    {q, 0, Quotient[r, 2]}
  ];

(*
  Numeric exact specialization.  Since r=k-n-1, the work depends on the
  diagonal offset, not on the potentially large row number n.
*)
sDiagonalValue[n_Integer?NonNegative, k_Integer?NonNegative] /; k <= n := 0;
sDiagonalValue[n_Integer?NonNegative, k_Integer?NonNegative] := Module[
  {r = k - n - 1},
  Sum[
    tmSign[q] Binomial[2 n + r - 2 q - 1, r - 2 q],
    {q, 0, Quotient[r, 2]}
  ]
];

(*
  Triangular recurrence for a consecutive family D_0,...,D_R.  This is
  preferable to independent finite sums when many adjacent diagonals are
  required.  IntegerExponent[m,2] is the binary ruler function nu_2(m).
*)
diagonalRuler[0] = 1;
diagonalRuler[r_Integer?Positive] :=
  diagonalRuler[r] = Expand[
    Sum[
      (2 x + 2 - 2^(IntegerExponent[m, 2] + 1))
        diagonalRuler[r - m],
      {m, 1, r}
    ]/r
  ];


(* ---------------------------------------------------------------------- *)
(* 2. Hybrid arbitrary-entry evaluator                                   *)
(* ---------------------------------------------------------------------- *)

(*
  For fixed n, one row is a signed repetition of a nonnegative block of
  length L=2^(2n+1).  The local block value b[n,a], 0<=a<L, obeys:

    b[n,a] = 0 on the two terminal runs of length n+1;
    b[n,a] = M on the central plateau of length 2n+1;
    b[n,a] = b[n,L-a] (circular reflection);
    b[n,a] + b[n,L/2-a] = M on the first half;
    b[n,L/4] = M/2 for n>=1;

  where M=2^Binomial[2n,2].  The ordered Which below maps every nontrivial
  residue into the first quarter before invoking the direct diagonal formula.
  Ordering matters: fixed points and the plateau must be handled before the
  symmetry branches.
*)
rowCoreValue[n_Integer?NonNegative, a_Integer?NonNegative] := Module[
  {len = 2^(2 n + 1), max = 2^Binomial[2 n, 2]},
  Which[
    a >= len,
      rowCoreValue[n, Mod[a, len]],

    a <= n || a >= len - n,
      0,

    len/2 - n <= a <= len/2 + n,
      max,

    a > len/2,
      rowCoreValue[n, len - a],

    n >= 1 && a == len/4,
      max/2,

    n >= 1 && a > len/4,
      max - rowCoreValue[n, len/2 - a],

    True,
      sDiagonalValue[n, a]
  ]
];

(*
  Exact value of an arbitrary table element.  QuotientRemainder finds the
  dyadic block and its local residue.  Only the block number contributes the
  Thue--Morse sign.
*)
sFast[n_Integer?NonNegative, k_Integer?NonNegative] := Module[
  {len = 2^(2 n + 1), q, a},
  {q, a} = QuotientRemainder[k, len];
  tmSign[q] rowCoreValue[n, a]
];


(* ---------------------------------------------------------------------- *)
(* 3. Complete-block precomputation                                      *)
(* ---------------------------------------------------------------------- *)

(*
  For a moderate fixed n and many k values, it can be faster to construct the
  first block once.  Its generating polynomial is

      z^(n+1) Product[1+z+...+z^(2^j-1), {j,1,2n}].
*)
rowBlockPolynomial[n_Integer?NonNegative] :=
  rowBlockPolynomial[n] = Expand[
    z^(n + 1) Product[
      Sum[z^a, {a, 0, 2^j - 1}],
      {j, 1, 2 n}
    ]
  ];

rowBlock[n_Integer?NonNegative] := rowBlock[n] = Module[
  {len = 2^(2 n + 1)},
  PadRight[CoefficientList[rowBlockPolynomial[n], z], len]
];

sByBlock[n_Integer?NonNegative, k_Integer?NonNegative] := Module[
  {len = 2^(2 n + 1), q, a},
  {q, a} = QuotientRemainder[k, len];
  tmSign[q] rowBlock[n][[a + 1]]
];


(* ---------------------------------------------------------------------- *)
(* 4. Small self-checks                                                   *)
(* ---------------------------------------------------------------------- *)

(*
  Examples (evaluate interactively in Wolfram Language):

    Table[Factor[diagonalPolynomial[r]], {r,0,7}]

    And @@ Flatten@Table[
      sFast[n,k] == sDiagonalValue[n,k],
      {n,0,5}, {k,0,2^(2 n + 2)}
    ]

    And @@ Flatten@Table[
      sFast[n,k] == sByBlock[n,k],
      {n,0,4}, {k,0,2^(2 n + 2)}
    ]

  The expected result of each Boolean check is True.
*)
