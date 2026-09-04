(* ::Package:: *)

(*
  Exact diagonal and block formulas for repeated summation of the signed
  Thue--Morse sequence.

  This file accompanies the article
    "Diagonal Polynomials and Dyadic Block Geometry in Repeated
     Thue--Morse Prefix Summation".

  All routines use exact integer/rational arithmetic.  The main function is

      diagonalPolynomial[d, x]

  which returns the polynomial P_d(x) satisfying

      s[n, n + d] == P_d(n),     d >= 1, n >= 0.

  The formula requires only Floor[(d-1)/2]+1 terms.
*)

ClearAll[
  tmSign, risingPolynomial, diagonalVariable, diagonalTemplate,
  diagonalPolynomial, diagonalValue, sClosed,
  diagonalPolynomialBySeriesCoefficient,
  prefixPulsePolynomial, prefixPulseCoefficient, sigmaBlock,
  sBlockClosed, halfGridRootIndices, halfGridFactor,
  negativeHalfGridValue, negativeHalfGridRootQ,
  minimalMonomialDenominator, sigmaReference, sReference,
  verifyPromptDiagonals, verifyClosedFormula, verifyRecurrence,
  verifyNegativeHalfGrid, verifyNegativeRootFamily
];

(* Signed Thue--Morse sequence epsilon_j = (-1)^(binary digit sum of j). *)
tmSign[j_Integer?NonNegative] := (-1)^ThueMorse[j];

(* Rising factorial y (y+1) ... (y+m-1), with the empty product equal to 1. *)
risingPolynomial[y_, 0] := 1;
risingPolynomial[y_, m_Integer?Positive] := Product[y + i, {i, 0, m - 1}];

(*
  Cached polynomial template for the diagonal with offset d.

  If q=d-1, the theorem is

    P_d(x) = Sum[epsilon_j Binomial[2 x + q - 2 j - 1, q - 2 j],
                 {j,0,Floor[q/2]}]

  and the Binomial is interpreted as the polynomial

    RisingFactorial[2 x, q-2j]/(q-2j)!.
*)
diagonalTemplate[d_Integer?Positive] := diagonalTemplate[d] = Module[
  {q = d - 1},
  Expand @ Sum[
    tmSign[j]
      risingPolynomial[2 diagonalVariable, q - 2 j]/Factorial[q - 2 j],
    {j, 0, Quotient[q, 2]}
  ]
];

diagonalPolynomial[d_Integer?Positive, var_: x] :=
  diagonalTemplate[d] /. diagonalVariable -> var;

diagonalValue[n_Integer?NonNegative, d_Integer?Positive] :=
  diagonalPolynomial[d, n];

(* Direct exact evaluation of an arbitrary table entry. *)
sClosed[n_Integer?NonNegative, k_Integer?NonNegative] /; k <= n := 0;
sClosed[n_Integer?NonNegative, k_Integer?NonNegative] := Module[
  {q = k - n - 1},
  Sum[
    tmSign[j] Binomial[2 n + q - 2 j - 1, q - 2 j],
    {j, 0, Quotient[q, 2]}
  ]
];

(*
  Coefficient-extraction version.  The formally infinite product K(z^2) only
  needs factors 1-z^(2^j) whose exponent does not exceed q=d-1.
*)
diagonalPolynomialBySeriesCoefficient[d_Integer?Positive, var_: x] := Module[
  {q = d - 1, jmax, finiteK},
  jmax = If[q < 2, 0, IntegerLength[q, 2] - 1];
  finiteK = Product[1 - z^(2^j), {j, 1, jmax}];
  FullSimplify @ SeriesCoefficient[
    finiteK/(1 - z)^(2 var),
    {z, 0, q}
  ]
];

(*
  Positive pulse polynomial for an order-r prefix sum:

    A_r(z) = Product[(1-z^(2^j))/(1-z), {j,1,r-1}].

  It has degree 2^r-r-1 and strictly positive, palindromic coefficients.
*)
prefixPulsePolynomial[r_Integer?Positive] :=
  prefixPulsePolynomial[r] = Expand @ Product[
    Sum[z^u, {u, 0, 2^j - 1}],
    {j, 1, r - 1}
  ];

prefixPulseCoefficient[r_Integer?Positive, b_Integer] /;
    b < 0 || b > 2^r - r - 1 := 0;
prefixPulseCoefficient[r_Integer?Positive, b_Integer?NonNegative] :=
  Coefficient[prefixPulsePolynomial[r], z, b];

(* Exact signed dyadic block law for sigma_r(q). *)
sigmaBlock[r_Integer?Positive, q_Integer?NonNegative] := Module[
  {a, b},
  {a, b} = QuotientRemainder[q, 2^r];
  tmSign[a] prefixPulseCoefficient[r, b]
];

(* Same table value as sClosed, now evaluated through its block geometry. *)
sBlockClosed[n_Integer?NonNegative, k_Integer?NonNegative] /; k <= n := 0;
sBlockClosed[n_Integer?NonNegative, k_Integer?NonNegative] :=
  sigmaBlock[2 n + 1, k - n - 1];

(*
  Exact nonnegative rational roots of the diagonal polynomial.
  Every rational root is an integer or a half-integer, and m/2 >= 0 is a
  root exactly when the low m+1 binary digits of q=d-1 lie in the terminal
  zero window of length m+1.
*)
halfGridRootIndices[d_Integer?Positive] := Module[
  {q = d - 1},
  If[q == 0,
    {},
    Select[
      Range[0, q - 1],
      Mod[q, 2^(# + 1)] >= 2^(# + 1) - (# + 1) &
    ]
  ]
];

halfGridFactor[d_Integer?Positive, var_: x] :=
  Times @@ (2 var - # & /@ halfGridRootIndices[d]);

(*
  Exact value at a negative half-integer.  The rational-root theorem in the
  article proves that every rational root has this form.  Here m>0 and the
  tested point is x=-m/2.
*)
negativeHalfGridValue[d_Integer?Positive, m_Integer?Positive] := Module[
  {q = d - 1},
  Sum[
    (-1)^j Binomial[m - 1, j] If[q - j < 0, 0, tmSign[q - j]],
    {j, 0, m - 1}
  ]
];

negativeHalfGridRootQ[d_Integer?Positive, m_Integer?Positive] :=
  PossibleZeroQ[negativeHalfGridValue[d, m]];

(* Least positive integer that clears all monomial coefficients of P_d. *)
minimalMonomialDenominator[d_Integer?Positive] := Module[
  {q = d - 1, c, v2},
  c = Ceiling[q/2];
  v2 = IntegerExponent[Factorial[q], 2];
  Factorial[q]/2^Min[v2, c]
];

(* Independent literal repeated-prefix implementation for small checks. *)
sigmaReference[0, q_Integer?NonNegative] := tmSign[q];
sigmaReference[r_Integer?Positive, q_Integer?NonNegative] :=
  sigmaReference[r, q] = Sum[sigmaReference[r - 1, j], {j, 0, q}];
sigmaReference[_, q_Integer?Negative] := 0;

sReference[n_Integer?NonNegative, k_Integer?NonNegative] :=
  sigmaReference[2 n + 1, k - n - 1];

(* The eight explicit polynomials printed in the prompt. *)
verifyPromptDiagonals[] := Module[
  {prompt, computed},
  prompt = {
    1,
    2 n,
    (1 + n) (-1 + 2 n),
    2/3 n (2 + n) (-1 + 2 n),
    1/6 (-6 - 3 n - n^2 + 12 n^3 + 4 n^4),
    1/15 (-1 + n) n (34 + 39 n + 24 n^2 + 4 n^3),
    1/90 (-1 + n) (1 + n) (-1 + 2 n)
      (90 + 75 n + 32 n^2 + 4 n^3),
    1/315 (-1 + n) n (2 + n) (-1 + 2 n)
      (192 + 123 n + 40 n^2 + 4 n^3)
  };
  computed = Table[diagonalPolynomial[d, n], {d, 1, 8}];
  And @@ MapThread[PossibleZeroQ[Together[#1 - #2]] &, {computed, prompt}]
];

verifyClosedFormula[maxN_Integer?NonNegative : 5,
    maxK_Integer?NonNegative : 40] := And @@ Flatten @ Table[
  sClosed[n, k] == sReference[n, k] == sBlockClosed[n, k],
  {n, 0, maxN}, {k, 0, maxK}
];

verifyRecurrence[maxN_Integer?Positive : 5,
    maxK_Integer?NonNegative : 40] := And @@ Flatten @ Table[
  sClosed[n, k] == Sum[(k - j) sClosed[n - 1, j], {j, 0, k - 1}],
  {n, 1, maxN}, {k, 0, maxK}
];

verifyNegativeHalfGrid[maxD_Integer?Positive : 24,
    maxM_Integer?Positive : 16] := And @@ Flatten @ Table[
  diagonalPolynomial[d, -m/2] == negativeHalfGridValue[d, m],
  {d, 1, maxD}, {m, 1, maxM}
];

verifyNegativeRootFamily[maxA_Integer?Positive : 8,
    maxBlock_Integer?NonNegative : 3] := And @@ Flatten @ Table[
  With[{q = block 2^a + 2^a - 1},
    negativeHalfGridRootQ[q + 1, 2^(ell + 1)]
  ],
  {a, 2, maxA}, {block, 0, maxBlock}, {ell, 1, a - 1, 2}
];

(* Suggested interactive commands:

   Table[Factor[diagonalPolynomial[d, n]], {d, 1, 16}]
   Table[minimalMonomialDenominator[d], {d, 1, 16}]
   Table[{d, halfGridRootIndices[d], halfGridFactor[d, n]}, {d, 1, 32}]

   verifyPromptDiagonals[]
   verifyClosedFormula[5, 50]
   verifyRecurrence[5, 50]
   verifyNegativeHalfGrid[24, 16]
   verifyNegativeRootFamily[8, 3]
*)
