(* Companion implementation from Appendix A of the article. *)
ClearAll[alpha, pInf, aTail, inverseCoefficient];
alpha[m_Integer, Q_] := Q^m/(m (1 - Q^m));
pInf[Q_] := QPochhammer[Q, Q];
aTail[Q_, t_] := -Log[QPochhammer[Q t, Q]];

inverseCoefficient[m_Integer, a_, lam_, D_, bs_List] :=
 Module[{u, bpoly},
  bpoly = Sum[bs[[j]] u^j, {j, 1, m}];
  -Sum[
    Coefficient[Expand[bpoly^k], u, m]/k *
     Sum[Binomial[k + j - 1, j] If[j == 0, 1, a^j] *
       (m lam)^(k - 1 - j)/
       ((k - 1 - j)! D^(k + j)), {j, 0, k - 1}],
    {k, 1, m}]
 ];

(* General linear group interpolation: work with its logarithm. *)
ClearAll[glLog, glInverseTruncated];
glLog[x_, q_] := x^2 Log[q] + Log[pInf[1/q]] +
                 aTail[1/q, q^(-x)];
glInverseTruncated[logY_, q_, M_Integer] :=
 Module[{h = Log[q], Q = 1/q, s, D, bs},
  s = Sqrt[(logY - Log[pInf[Q]])/h];
  D = 2 h s;
  bs = Table[alpha[j, Q], {j, 1, M}];
  s + Sum[inverseCoefficient[m, h, h, D, bs] q^(-m s),
          {m, 1, M}]
 ];

(* Exact integer examples; q is a prime power for field counting. *)
ClearAll[galoisNumber, qCatalanBinomial, irreducibleCount];
galoisNumber[n_Integer, q_] := Sum[QBinomial[n, k, q], {k, 0, n}];
qCatalanBinomial[n_Integer, q_] :=
  (q - 1) QBinomial[2 n, n, q]/(q^(n + 1) - 1);
irreducibleCount[n_Integer, q_Integer] /; n >= 1 && q >= 2 :=
  Total[(MoebiusMu[#] q^(n/#)) & /@ Divisors[n]]/n;

(* The leading inverse of q^x/x, on the large real branch. *)
ClearAll[necklaceCenter];
necklaceCenter[y_, q_] := -ProductLog[-1, -Log[q]/y]/Log[q];
