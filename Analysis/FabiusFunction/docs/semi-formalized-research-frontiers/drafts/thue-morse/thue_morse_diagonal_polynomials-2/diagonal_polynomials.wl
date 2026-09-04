(* ::Package:: *)

(*
  Exact Wolfram Language implementation for the diagonal-polynomial theory
  of odd iterated Thue--Morse prefix sums.

  Definitions used in the accompanying article:

      epsilon_q = (-1)^ThueMorse[q]
      D_m(x)    = Coefficient of z^m in T[z^2]/(1-z)^(2 x)

  and, for the table in the question,

      s[n,k] = 0                         when k <= n,
      s[n,k] = D_(k-n-1)(n)             when k > n.

  Everything below is exact.  No interpolation or numerical recognition is
  used.  The direct formula is normally the fastest choice for one diagonal
  value; the Newton--Bell generator is convenient when many symbolic
  polynomials are wanted.
*)

ClearAll[
  tmSign, risingTwoX, DiagonalPolynomial, DiagonalValue,
  tmPrefixMoments, DiagonalValueByMoments, DiagonalValueFast,
  $DiagonalDirectCutoff, SClosed, lambda, diagonalFormal,
  DiagonalPolynomialNewton, SReference, VerifyDiagonalCode,
  formalX
];

(* Signed Thue--Morse sequence epsilon_q in {+1,-1}. *)
tmSign[q_Integer?NonNegative] := (-1)^ThueMorse[q];

(* (2 x)^(overline p), written as a literal polynomial product so that
   Expand always produces a polynomial without needing FunctionExpand. *)
risingTwoX[x_, 0] := 1;
risingTwoX[x_, p_Integer?Positive] := Product[2 x + j, {j, 0, p - 1}];

(* Exact polynomial for the m-th diagonal:

     D_m(x) = Sum[epsilon_q (2x)^(overline(m-2q))/(m-2q)!, q].
*)
DiagonalPolynomial[m_Integer?NonNegative, x_] := Expand @ Sum[
  With[{p = m - 2 q}, tmSign[q] risingTwoX[x, p]/p!],
  {q, 0, Floor[m/2]}
];

(* Exact integer value D_m(n).  Generalized Binomial also handles n=0;
   in particular Binomial[-1,0] is 1. *)
DiagonalValue[m_Integer?NonNegative, n_Integer?NonNegative] := Sum[
  With[{p = m - 2 q},
    tmSign[q] Binomial[2 n + p - 1, p]
  ],
  {q, 0, Floor[m/2]}
];

(* Signed prefix moments

       M_d(N) = Sum[epsilon_q q^d, {q,0,N-1}].

   Pairing 2q and 2q+1 gives

       M_d(2N)   = -Sum[Binomial[d,j] 2^j M_j(N), {j,0,d-1}],
       M_d(2N+1) = M_d(2N) + epsilon_N (2N)^d.

   Consequently the entire vector through degree d is computed in
   O[d^2 Log[N]] exact arithmetic operations. *)
tmPrefixMoments[0, maxDegree_Integer?NonNegative] :=
  ConstantArray[0, maxDegree + 1];

tmPrefixMoments[length_Integer?Positive, maxDegree_Integer?NonNegative] :=
  tmPrefixMoments[length, maxDegree] = Module[
    {half = Quotient[length, 2], lower, paired},
    lower = tmPrefixMoments[Quotient[length, 2], maxDegree];
    paired = Table[
      If[d == 0,
        0,
        -Sum[Binomial[d, j] 2^j lower[[j + 1]], {j, 0, d - 1}]
      ],
      {d, 0, maxDegree}
    ];
    If[OddQ[length],
      paired += tmSign[half] Table[(2 half)^d, {d, 0, maxDegree}]
    ];
    paired
  ];

(* Logarithmic-in-m evaluator.  For n>=1 the binomial kernel is a
   polynomial of degree 2n-1 in q, so it can be contracted with the signed
   prefix moments instead of summed term by term. *)
DiagonalValueByMoments[m_Integer?NonNegative, 0] :=
  If[EvenQ[m], tmSign[m/2], 0];

DiagonalValueByMoments[m_Integer?NonNegative, n_Integer?Positive] := Module[
  {degree = 2 n - 1, q, kernel, coefficients, moments, value},
  kernel = Expand[
    Product[m - 2 q + j, {j, 1, 2 n - 1}]/(2 n - 1)!
  ];
  coefficients = CoefficientList[kernel, q];
  moments = tmPrefixMoments[Floor[m/2] + 1, degree];
  value = Together[coefficients . Take[moments, Length[coefficients]]];
  If[Denominator[value] === 1, Numerator[value], value]
];

(* Exact block reduction in the diagonal offset m.  For

       B = 2^(2 n + 1),  m = q B + r,

   one has D_m(n) = epsilon_q D_r(n).  A short reduced offset is handled by
   the direct finite sum; a long one uses the prefix-moment algorithm. *)
$DiagonalDirectCutoff = 128;

DiagonalValueFast[m_Integer?NonNegative, n_Integer?NonNegative] := Module[
  {block = 2^(2 n + 1), q, r, core},
  {q, r} = QuotientRemainder[m, block];
  core = If[r <= $DiagonalDirectCutoff,
    DiagonalValue[r, n],
    DiagonalValueByMoments[r, n]
  ];
  tmSign[q] core
];

(* A compact replacement for the whole two-dimensional definition. *)
SClosed[n_Integer?NonNegative, k_Integer?NonNegative] /; k <= n := 0;
SClosed[n_Integer?NonNegative, k_Integer?NonNegative] /; k > n :=
  DiagonalValueFast[k - n - 1, n];

(* The 2-adic logarithmic cumulants

       lambda_r(x) = 2 x + 2 - 2^(IntegerExponent[r,2]+1).
*)
lambda[r_Integer?Positive, x_] :=
  2 x + 2 - 2^(IntegerExponent[r, 2] + 1);

(* Memoized Newton--Bell generator.  It obeys

       m D_m(x) = Sum[lambda_r(x) D_(m-r)(x), {r,1,m}].
*)
diagonalFormal[0] = 1;
diagonalFormal[m_Integer?Positive] := diagonalFormal[m] = Expand[
  Sum[lambda[r, formalX] diagonalFormal[m - r], {r, 1, m}]/m
];

DiagonalPolynomialNewton[m_Integer?NonNegative, x_] :=
  diagonalFormal[m] /. formalX -> x;

(* Literal reference implementation through (2 n + 1) inclusive prefix
   summations.  This is for verification, not for fast production use. *)
SReference[n_Integer?NonNegative, k_Integer?NonNegative] /; k <= n := 0;
SReference[n_Integer?NonNegative, k_Integer?NonNegative] /; k > n := Module[
  {last = k - n - 1, row},
  row = Nest[Accumulate, Table[tmSign[j], {j, 0, last}], 2 n + 1];
  row[[last + 1]]
];

(* Small exact regression suite.  True means that the direct formula,
   Newton--Bell recurrence, half-step lowering law, and literal prefix sums
   all agree on the tested range. *)
VerifyDiagonalCode[maxDegree_Integer?NonNegative : 10] := And[
  And @@ Table[
    Expand[
      DiagonalPolynomial[m, formalX] -
      DiagonalPolynomialNewton[m, formalX]
    ] === 0,
    {m, 0, maxDegree}
  ],
  And @@ Table[
    Expand[
      DiagonalPolynomial[m, formalX] -
      (DiagonalPolynomial[m, formalX] /. formalX -> formalX - 1/2) -
      DiagonalPolynomial[m - 1, formalX]
    ] === 0,
    {m, 1, maxDegree}
  ],
  And @@ Flatten @ Table[
    DiagonalValue[m, n] === DiagonalValueByMoments[m, n],
    {n, 0, 4}, {m, 0, 40}
  ],
  And @@ Flatten @ Table[
    SClosed[n, k] === SReference[n, k],
    {n, 0, 4}, {k, 0, 28}
  ]
];

(* Examples:

   Table[Factor[DiagonalPolynomial[m, x]], {m, 0, 12}]
   DiagonalValue[40, 1000]
   SClosed[20, 10^9]       (uses the prefix-moment path)
   VerifyDiagonalCode[10]

   The user's displayed rule for a chosen offset m can be produced by

   With[{m = 7},
     HoldForm[s[n_Integer, k_Integer] /; k == n + m + 1] ==
       Factor[DiagonalPolynomial[m, n]]
   ]
*)
