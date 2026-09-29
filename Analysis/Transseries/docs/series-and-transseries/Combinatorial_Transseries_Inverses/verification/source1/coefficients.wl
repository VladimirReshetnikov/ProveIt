(* Exact coefficient formulas. These definitions use no machine literals. *)
ClearAll[ExpCoefficient, GammaRatioCoefficient, EndpointCoefficient,
  NormalHalfMoment, InvolutionCoefficient, QLogCoefficient,
  QInverseCoefficient, StirlingColumnInverse];

ExpCoefficient[d_List, n_Integer] /; 0 <= n <= Length[d] :=
 Module[{t}, SeriesCoefficient[
   Exp[Sum[d[[j]] t^j, {j, 1, n}]], {t, 0, n}]];

GammaRatioCoefficient[aa_, bb_, n_Integer] /; n >= 0 :=
 ExpCoefficient[Table[
   (-1)^(j + 1) (BernoulliB[j + 1, aa] -
      BernoulliB[j + 1, bb])/(j (j + 1)), {j, 1, n}], n];

EndpointCoefficient[alpha_, c_, n_Integer] /; n >= 0 :=
 Total[Table[Binomial[alpha, j] (-c)^j Pochhammer[alpha + 1, j]
   GammaRatioCoefficient[1, alpha + j + 2, n - j], {j, 0, n}]];

NormalHalfMoment[n_Integer] /; n >= 0 :=
 Sum[n! (1/2)^(n - 2 j)/(4^j j! (n - 2 j)!),
   {j, 0, Floor[n/2]}];

InvolutionCoefficient[m_Integer] /; m >= 0 :=
 Module[{t, v, poly},
  poly = Expand[SeriesCoefficient[
    Exp[Sum[(-1)^(r + 1) v^(r + 2) t^r/(r + 2), {r, 1, m}]],
    {t, 0, m}]];
  Total[Table[Coefficient[poly, v, j] NormalHalfMoment[j],
    {j, 0, 3 m}]]];

QLogCoefficient[r_Integer, q_] /; r >= 1 :=
 -2/(r (q^r - 1)) + If[EvenQ[r], 2/(r (q^(r/2) - 1)), 0];

QInverseCoefficient[n_Integer, x_Symbol, a_, q_] /; n >= 1 :=
 Module[{t, hh, apply},
  hh = Sum[QLogCoefficient[r, q] t^r, {r, 1, n}];
  apply[f_] := (D[f, x] - a n f)/(2 a x);
  Simplify[Total[Table[(-1)^m/m! Coefficient[Expand[hh^m], t, n]
    Nest[apply, 1/(2 a x), m - 1], {m, 1, n}]]]];

(* Total-degree truncation, exponential cost in k and maxDegree. *)
StirlingColumnInverse[k_Integer, y_, maxDegree_Integer] /;
    k >= 2 && maxDegree >= 0 :=
 Module[{a = Log[k], xx, kap, terms, indices},
  xx = Log[k! y]/a;
  kap = Table[Log[k/j]/a, {j, 1, k - 1}];
  terms = Table[(-1)^(k - j) Binomial[k, j] (j/k)^xx,
    {j, 1, k - 1}];
  indices = Select[Tuples[Range[0, maxDegree], k - 1],
    1 <= Total[#] <= maxDegree &];
  xx - Total[Map[Function[nu,
    Product[(kap.nu) - h, {h, 1, Total[nu] - 1}]
    Product[terms[[j]]^nu[[j]]/nu[[j]]!, {j, 1, k - 1}]],
    indices]]/a];

(* Examples:
 Table[InvolutionCoefficient[m], {m, 0, 6}]
 Table[EndpointCoefficient[1/2, 3/4, m], {m, 0, 4}]
 QInverseCoefficient[2, x, a, q]
 N[StirlingColumnInverse[3, StirlingS2[30, 3], 4] - 30, 40]
*)
