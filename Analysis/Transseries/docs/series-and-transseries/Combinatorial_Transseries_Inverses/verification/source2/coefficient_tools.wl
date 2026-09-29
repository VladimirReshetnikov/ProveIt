(* Coefficient formulas from the companion article.
   This Wolfram Language translation was not executed in the production environment.
   See verify.py and audit_symbolic.py for the executed independent checks. *)

ClearAll[gammaLogCoefficient, balancedInverseCoefficient,
  harmonicInverseCoefficient, catalanCore];

gammaLogCoefficient[data_List, r_Integer] /; r >= 1 :=
  (-1)^(r + 1)/(r (r + 1)) Total[
    (#[[3]] BernoulliB[r + 1, #[[2]]]/#[[1]]^r) & /@ data
  ];

balancedInverseCoefficient[q_List, a_, beta_, n_Integer] /;
    n >= 1 && Length[q] >= n :=
  Module[{t, u, psi},
    psi = -(beta Log[1 + t u] +
       Sum[q[[j]] (t/(1 + t u))^j, {j, 1, n}])/a;
    Simplify[Total[Table[
      SeriesCoefficient[
        SeriesCoefficient[psi^m, {t, 0, n}],
        {u, 0, m - 1}]/m,
      {m, 1, n}]]]
  ];

harmonicInverseCoefficient[m_Integer] /; m >= 1 :=
  Module[{z, c},
    c = -Sum[BernoulliB[2 j, 1/2] z^j/(2 j), {j, 1, m}];
    -SeriesCoefficient[Exp[(2 m - 1) c], {z, 0, m}]/(2 m - 1)
  ];

catalanCore[y_] := -3/(2 Log[4]) ProductLog[-1,
  -(2 Log[4])/3 (1/(Sqrt[Pi] y))^(2/3)];

catData = {{2, 1, 1}, {1, 1, -1}, {1, 2, -1}};
catQ = Table[gammaLogCoefficient[catData, j], {j, 1, 6}];
Table[balancedInverseCoefficient[catQ, Log[4], -3/2, n],
  {n, 1, 3}]
Table[harmonicInverseCoefficient[m], {m, 1, 5}]
