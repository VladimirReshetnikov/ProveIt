# Source audit — 1 October 2026

## Primary OEIS entries read

- https://oeis.org/A238016 — array p_n(n^k); contains a general asymptotic
  condition labeled as a conjecture with the nonstandard notation f(n)>=O(n^4).
- https://oeis.org/A238608 — p_n(n^3); already posts the factor
  exp(2n+1/4) n^(n-3)/(2*pi), as well as the c*n^3 extension and its cross-references.
- https://oeis.org/A238010 — array p_n(k^n); already posts the leading
  k^(n(n-1))/(n!(n-1)!) asymptotic.
- https://oeis.org/A258670 — p_n((2n)!); repeats the broad asymptotic condition.

The page status alone is not evidence that the corresponding mathematical
question has no published solution.

## Classical literature checked

- E. Rodney Canfield, *From Recursions to Asymptotics: On Szekeres' Formula
  for the Number of Partitions*, EJC 4(2) (1997), R6,
  https://doi.org/10.37236/1321.
  Step 5 and Comment 5 explicitly give the small-number-of-parts estimate
  and attribute it to Erdos and Lehner. This prevents a world-first claim
  for the sufficiency of N/m^3 -> infinity.
- Karl Dilcher and Christophe Vignat, *An explicit form of the polynomial
  part of a restricted partition function*, Research in Number Theory 3
  (2017), 1, https://doi.org/10.1007/s40993-016-0065-3.
  The first Sylvester wave and Bernoulli-polynomial descriptions are classical.
- Andrew V. Sills and Doron Zeilberger, arXiv:1108.4391,
  https://arxiv.org/abs/1108.4391 — abstract and metadata checked for the
  quasipolynomial algorithmic context.
- Cormac O'Sullivan, arXiv:1702.03611,
  https://arxiv.org/abs/1702.03611 — abstract and metadata checked for
  asymptotics of Sylvester waves in another joint-growth regime.
- NIST DLMF 5.11, https://dlmf.nist.gov/5.11 — gamma expansion and remainder
  formulas used as standard analytic input.

No exhaustive negative literature search or independent novelty certification
is claimed. The particular coefficient and probability refinements in the
report are derived explicitly rather than presumed new from their absence
in one OEIS entry.

## Repository scope

Repository: https://github.com/VladimirReshetnikov/ProveIt

The main-branch source inspected directly was:
`Analysis/FabiusFunction/Lean/FabiusFunction/PartitionBoundedParts.lean`.
It contains `Fabius.boundedCount`, `card_restricted_le_eq`, and
`hasSum_boundedCount_mul_pow`, supplying the finite-product generating
function. This was a source inspection, not a Lean build or a complete audit
of every repository file. The new proofs do not depend on unverified claims
from unrelated repository reports. No repository files were changed.
