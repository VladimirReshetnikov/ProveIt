# Late proposal-corpus update and nonduplication addendum

## Conclusion

The three proposals added at commit
`51aa1e3b5807c635a6fb6244a9ce4678b9106bc6` do **not** duplicate the
canonical-negative-frame/bordered-Hua replacement or the logarithmic spectral
trace-transfer theorem. This conclusion is based on reading all three main
reports and all three top-level READMEs in full, including the reports' proposed
extensions and implementation alternatives. The six primary texts contain
102,958 bytes. A targeted search of all 22 new TeX/Markdown/text files also found
no additional proposal directed at either of our target mechanisms.

This is a nonduplication judgment relative to the inspected repository corpus,
not a claim of priority in the mathematical literature or an independent
verification of the complete RH/Dirichlet-GRH development.

## Two snapshots and the exclusion union

The original source accounting and 28-directory proposal audit remain pinned to
`f2d6ab6c4b70ea73b2deac9e33ad966bc92ea36f`. The late cutoff is
`51aa1e3b5807c635a6fb6244a9ce4678b9106bc6`, whose Git committer timestamp is
**2026-11-27 20:20:29 PST** (`2026-11-28 04:20:29 UTC`).

| Corpus quantity | Count |
|---|---:|
| Proposal directories at the source-accounting baseline | 28 |
| Newly added directories | 3 |
| Previously inspected directories subsequently removed | 2 |
| Proposal directories at the late cutoff | 29 |
| Old-plus-new union treated as already proposed work | **31** |
| Files present at both cutoffs, with unchanged Git blobs | 298 |
| New primary reports and top-level READMEs read in full | 6 |
| New text files inventoried and screened | 22 |

The removed directories are `grh-class-count-finite-quotient` and
`rh_two_order_tests_proposal`. Their content remains excluded as previously
proposed work. Removal does not restore novelty to those ideas.

All 298 common proposal files have identical Git blob IDs at the two cutoffs;
there are no modified files among the retained proposal bundles. The three new
bundles are therefore the complete substantive late-update scope.

## Mechanism-by-mechanism comparison

| New proposal | Ideas now treated as existing work | Why our two replacements remain additional |
|---|---|---|
| `grh-inert-prime-polynomial-coefficient` | Finite characteristic-\(p\) substitution and coefficient extraction in a truncated polynomial algebra; a recurrence proves a unit coefficient in the inert-prime formal-group calculation. The target is `norm_coeff_taylorVia_translatedX_eq_one` in `New/Derivatives/FormalGroup/FrobeniusCongruence.lean`. | This is a nonarchimedean formal-group/Taylor-coefficient argument. It supplies neither a canonical negative frame nor a fixed-column complex matrix integral, and contains no line-parahoric spectral or trace-moment recovery theorem. |
| `grh_coefficient_contraction` | Evaluate the initial finite gauge average as a character-valued orbit section. Identify the anchored-chain stabilizer, normalize the coefficient budget to one, and collapse the first-column scalar to an endpoint ratio. A complementary contract keeps universal integrality and a complex-conjugate bound only at the trivial twist, deriving both from one terminal finite expansion. | These changes concern `Determinant/AuxiliaryForms`, finite gauge actions, and arithmetic coefficient bookkeeping. They retain the analytic estimates. Neither `OneRealPlace`'s negative-basis/Hua majorant nor `TraceFormula`'s line-operator trace recovery is replaced by the orbit-section theorem or the weaker arithmetic contract. |
| `grh_finite_grids` | Three independent changes: explicit finite-field grids for the deep-forms weighted monomial estimate; two residue charts at one finite prime for Fourier-frequency height counting; and a block differential-equation proof of the principal-minor estimate for three matrix exponentials. | The first two target `ElementaryDivisors/Depth` and `Spanning/MainTerm/Frequencies`. The third targets `Appendix/DiscreteSeries/MinorSecondOrder` and `OneMinor`. None has the hypotheses or conclusion of the real-place bordered-Hua majorant or the mixed-trace transfer theorem. |

### The closest apparent overlap: the principal-minor companion

The third component of `grh_finite_grids` uses a projection, block matrices,
traces, and a logarithmic determinant estimate, so it merits a substantive
comparison rather than a filename-only dismissal. Its input consists of three
small matrices \(A_1,A_2,A_3\), a projection \(P\), and bounds on their norms and
commutators with \(P\). A piecewise matrix flow proves a second-order expansion
of the principal minor of \(e^{A_1}e^{A_2}e^{A_3}\), with a remainder controlled
by the off-diagonal blocks. The argument uses block evolution, Gronwall bounds,
and the derivative of a determinant.

Our Hua replacement instead starts with an indefinite Hermitian geometry and
the canonical lift \(\Omega=JP_y^*D\). It bounds a volume by
\(\det(H+V^*V)\), retains the last column, and integrates over the other columns
using a fixed-column Schur-complement identity. It contains no small-matrix
exponential or flow estimate. Its source consumer is `SchurOrbit` through
`OneRealPlace`, not the principal-minor period estimate.

Our trace theorem instead starts with
\(TT^*=d(I+ce)\), \(e^2=e\), and an operator commuting with both \(T\) and
\(T^*\). A norm-determinant identity on reducing subspaces converts the rank of
\(e\) to a sum of logarithmic eigenvalue moduli. Polynomial interpolation then
transfers a weighted projection trace from finitely many positive mixed
moments. It does not assume a near-identity exponential, estimate a remainder,
or use a differential equation. The principal-minor argument therefore does
not subsume this theorem even though both use a logarithm of a determinant at
some point.

### Proposed extensions were also excluded

The finite-grid report explicitly asks whether more general translated
representations admit shallow coordinates that turn their orbits into products
of finite fields with side lengths matching reciprocal monomial costs. It also
asks whether the height-series convergence for every exponent \(s>2\) can lower
the common decay exponent in the global Fourier sieve. These are not proposals
to replace the fixed-column remaining-term majorant or to recover line-level
projection traces.

The coefficient-contraction report's optional work includes a closed formula
for the congruence-kernel cardinality, a direct transporter-based implementation,
and the arithmetic-contract/terminal-expansion cleanup described in the table.
Those are treated as existing proposals too. The inert-prime report's staged
implementation remains within its finite polynomial coefficient calculation.

Assuming all these changes are implemented leaves the mathematical inputs and
calls targeted by our two proposals in place. That is the relevant distinction;
shared use of determinants, traces, or normalization does not establish overlap.

## Source freshness and accounting

An independent comparison confirms identical Git blobs for all **16** files in
the report's source/configuration freshness check: the 13 inspected Lean files,
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. These include
`OneRealPlace`, `SchurOrbit`, `HolomorphicIntegrals`, `HermitianMatrices`,
`MinorProducts`, `LineDeterminant`, `LevelCut`, and `CuspidalComparison`.

The original line ranges and gross affected-line counts for the target proofs
therefore remain valid at the late cutoff. The **611** affected lines for the
primary replacement remain a gross source footprint, not a measured net
deletion. Global source-size percentages remain explicitly attached to the
original pin. This addendum does not claim that every file in the entire
development is unchanged or that a new full build has been performed.

## Text and Git evidence

The JSON file `latest_proposal_manifest.json` contains the baseline, late, and
union directory inventories; SHA-256 hashes and Git blob IDs for all six new
primary texts; the broader 22-text inventory; and the independently reproduced
16-file source/configuration comparison. The script `check_latest_proposals.py`
reads Git objects without checking out a new branch or modifying the source:

```bash
python3 check_latest_proposals.py --repo /path/to/ProveIt --output latest_proposal_manifest.json
```

The script verifies snapshot facts. It does not infer mathematical novelty from
keyword absence; the comparison above is the mathematical review.

Primary report links at the late cutoff:

- [Inert-prime polynomial coefficient](https://github.com/VladimirReshetnikov/ProveIt/blob/51aa1e3b5807c635a6fb6244a9ce4678b9106bc6/Analysis/GeneralizedRiemannHypothesis/docs/proposals/grh-inert-prime-polynomial-coefficient/report.tex).
- [Initial gauge-average contraction](https://github.com/VladimirReshetnikov/ProveIt/blob/51aa1e3b5807c635a6fb6244a9ce4678b9106bc6/Analysis/GeneralizedRiemannHypothesis/docs/proposals/grh_coefficient_contraction/report.tex).
- [Finite grids, frequency heights, and the principal-minor estimate](https://github.com/VladimirReshetnikov/ProveIt/blob/51aa1e3b5807c635a6fb6244a9ce4678b9106bc6/Analysis/GeneralizedRiemannHypothesis/docs/proposals/grh_finite_grids/report.tex).

## Ready-to-use late-update paragraph

A final freshness check found that `main` had advanced from the source-accounting
pin `f2d6ab6c` to `51aa1e3b` (27 November 2026, 20:20:29 PST). Three proposal
bundles had been added and two removed. We read the three new reports and their
READMEs in full, including the stated extensions, and found no duplication of
either proposed replacement. The exclusions therefore cover the **31-bundle
union**, although the latest tree contains **29** proposal directories. All
298 files common to the two proposal trees are unchanged. The 13 inspected Lean
files and three toolchain/dependency files also have identical Git blobs, so the
original target-source ranges and gross footprint calculations remain valid.
