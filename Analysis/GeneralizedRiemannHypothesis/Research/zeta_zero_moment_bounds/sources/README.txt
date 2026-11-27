Source notes, 26 November 2026

Upstream Lean project: https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207
Read grh/src/Statements.lean (blob 1cd1bce93344065936b2b392b23306254e0785ef),
grh/src/Main.lean (1adf4187a938510363cdb0dde0a6d628ff39c600),
grh/GUIDE.md (c2acf9584b58efcb39ac1d668d25c107c3e76a0b) and README.
The five entry points cover Mathlib RH, an explicit zeta-zero formulation,
half-plane nonvanishing for Dirichlet L-functions, the open-strip zero theorem
for all Dirichlet characters, and its primitive specialization. This note
imports the zero-location conclusion into a paper proof. Scalar inequalities
used to deduce that conclusion in the upstream work are not reproved here.

ProveIt snapshot: https://github.com/VladimirReshetnikov/ProveIt/tree/244c77760d4dd675372c5bda2438c135e2fc802d/Analysis/GeneralizedRiemannHypothesis
Directory index blob: 6d7cf130b3a595912ca983451a3d6e27b5f4c06b.
The directory's placement index covers 61 archived packets. It describes
1,795 placed files, including 272 Lean files, with no verification at
placement. packet_screen.tsv covers their indexed delivery READMEs.
incoming_screen.tsv covers the 28 additional ZIPs found under the nested
docs/incoming directory of the same snapshot. It records archive blobs
and a lexical screen of primary TeX members, excluding material under prior,
predecessor(s), upstream, previous and source(s) directories. The search
covered such terms as power sums, Jensen, Li coefficients, Taylor coefficients,
Graeffe and root squaring. A lexical search can miss mathematical equivalents.
The comparison in the paper uses direct reading of the relevant texts.

Closest identified overlap: docs/incoming/li_ritz_zero_recovery.zip (Git
blob cd76e9038b0947facd5600274763e0e543cba9d5). It uses Li coefficients to
construct a generalized eigenvalue problem for inverse squared distances
and certifies individual zeros from moment intervals. Its moment generator
and generated JSON are reproduced unchanged in verification/ with attribution
in zeta_finite_provenance.txt. Our new root and sign checks use four of its
moments. Independent web sources and the requested Wikipedia article are
linked in the paper. The present proof and examples have no Lean formalization.
