# Source audit

## Repository anchor

The mathematical baseline is ProveIt commit `04bf92d507588a26abadbaee1beb1e7350c8bffb`, dated 11 October 2026 UTC.

## Inherited mathematical inputs

| Input | Repository location | Role in this package |
|---|---|---|
| General shifted-Hankel reduction | `Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/bernoulli-tornheim-digamma/sections/03b_general_hankel.tex` | Source matrix, fixed-size retained determinant, and exact rational normalization. |
| Small-order completed families | same continuation, especially `03_moment_rank.tex`, `03c_moment_rank_four.tex`, and `03d_moment_rank_six.tex` | Prior cases `p=2,4,6` and consistency checks. |
| Complete order eight and eventual rank | `.../quartic-spectral-reconstruction/sections/02_rank_eight.tex` and `03_eventual_rank.tex` | Complete `p=8`, general eventual nonvanishing, and the order-ten threshold `B_5=1920`. |
| Explicit research target | `.../quartic-spectral-reconstruction/sections/08_research.tex` | Requests exact completion of `6 <= b < 1920` for smaller order ten. |
| Partial order-ten congruence | `.../alternating-tails-spectral-defects/sections/07_rank_refinement.tex` | Five-square contraction and nonvanishing outside `b congruent 962 mod 2048`; establishes that this residue class remained unresolved by that method. |
| Current manuscript | `Analysis/Polylogarithms/docs/manuscript` | Terminology, normalizations, overlap audit, and proposed integration placement. |
| Current incoming collection | `docs/incoming` | Targeted title/content search to avoid duplicating newer continuation packages. |

## Findings

1. The exact retained-matrix normalization used here agrees with the source formula. Direct and retained determinants were compared modulo the certificate prime at `b=10,11,12,13,14`, including the full scalar multiplier.
2. The preceding order-ten congruence theorem leaves an exceptional progression. This package does not reinterpret that progression as a candidate zero set; it checks every remaining finite index exactly.
3. The source's eventual theorem reduces the order-ten claim to a finite set before computation. The modular scan is therefore an exhaustive proof of the remaining lemma, not extrapolation from samples.
4. No contradiction was found in the inherited formulas used here.
5. The Stieltjes and two-tail generator formulas were not found verbatim in the inspected manuscript and continuation tree. Global literature priority is not asserted.

## Status corrections recommended on integration

- Mark the fixed smaller-order-ten reconstruction problem as proved for every `b >= 6`.
- Remove `p=10` from lists of unresolved fixed-order families.
- Retain the unrestricted unequal-even-order conjecture as open.
- Explain that the old exceptional class `b congruent 962 mod 2048` reflected the precision of one congruence argument, not a determinant zero.
- Preserve the mixed definition of the modular proof residues: direct determinants for `b<10`, retained determinants for `b>=10`.

## Post-snapshot repository movement

At the final repository observation, `main` had advanced eight commits to
`81d05cb50cf2d302f5e450e46cc18c1def95c8d2`. The compare inventory showed no
change under `Analysis/Polylogarithms`; it did add the binary incoming archive
`docs/incoming/ProveIt_Lerch_Selectors_2026-10-11.zip`, together with changes
elsewhere in the repository. That archive was not present in the pinned corpus
and is not used as evidence here. Consequently, every local novelty statement
in the article is intentionally relative to the audited commit `04bf92d5`, not
to uninspected post-snapshot binary deliveries. The complete order-ten theorem
itself is independent of that novelty comparison.

