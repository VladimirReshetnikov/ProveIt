# Inverse Fabius Theory: analyticity, asymptotics, computability, and dyadic sampling

This directory is the canonical source and publication package for
[`inverse_fabius_theory.tex`](inverse_fabius_theory.tex)
([PDF](inverse_fabius_theory.pdf)). It replaces five overlapping reports on
inverse Fabius theory and the Rvachev law: dense-open analyticity and
non-elementarity, positive inverse iterates, inverse-dyadic germs,
Barnes--Rvachev deconvolution, all-orders Lambert--W endpoint inversion,
dyadic self-sampling and Richardson filters, exact inverse moduli, and
certified computation.

Every nonconjectural retained assertion has a complete human-readable proof.
`Lean-proved` is reserved for an exact current declaration with matching
hypotheses and conclusion; other complete proofs are labelled
`human-proved frontier result`. Genuine unresolved obligations remain visibly
labelled as conjectures or open problems, and numerical experiments are used
only as reproducible checks.

The package audit surfaces are:

- [`theorem_concordance.csv`](theorem_concordance.csv): all 194 immutable
  source-result rows, fully dispositioned as 57 Lean-proved, 88 human-proved
  frontier results, 10 conjectures, 15 open problems, and 24 non-applicable
  source environments;
- [`LEAN_CROSSWALK.md`](LEAN_CROSSWALK.md): exact module and declaration
  matches, formalization boundaries, and five separately classified
  post-snapshot additions;
- [`ASSET_DISPOSITION.csv`](ASSET_DISPOSITION.csv): the disposition of all 88
  files in the two superseded source subgroups and the migration from the
  former 63-payload checkpoint to the current 55-file canonical asset tree;
- [`SOURCE_CLOSURE.sha256`](SOURCE_CLOSURE.sha256): a purpose-specific
  23-input source-only record maintained by its approved generator; its merged
  digest belongs to that generated file, while older digests remain historical
  provenance below;
- [`PROVENANCE.md`](PROVENANCE.md): source hashes, arrival lineage, nested
  predecessors, and immutable recovery points.

The two independent check commands are retained for a future authorized ledger
refresh:

```bash
python -B audit/build_source_closure.py --check
python -B audit/build_asset_manifest.py --check
```

The asset audit remains separate. The purpose-specific closure is regenerated
for the merged 23 inputs by its approved generator and has no whole-package or
PDF-parity role. Publication parity is recorded separately by the current
source/PDF receipt in the [authoritative receipt
register](../../MANIFEST.md#current-post-merge-publication-receipts).

`theorem_concordance.csv` records the disposition of all 194 source-result
environments while preserving the ten immutable source fields reproduced from
`audit/SOURCE_REVISION`.  Its current totals are 57 Lean-proved, 88
human-proved frontier results, 10 conjectures, 15 open problems, and 24
nonassertoric rows.  Ten inverse-computability rows now have exact compiled
counterparts: the main theorem, the three tolerant-difference branch
certificates, tolerant-bisection correctness, unit-interval sequential
inversion, computable clamping, and sequential computability of the totalized
inverse.  `FabiusFunction.EffectiveGapInverse` closes the ninth, abstract row:
it derives a computable reciprocal inverse modulus from computable positive
rational gap data and concludes both subset sequential computability and
effective uniform continuity; its companion theorem packages the clamped
inverse as a total computable real function.  The exact-dyadic proposition
described below closes the tenth row.  The centered Appell
deconvolution, positive-degree Appell
mean-zero, and arbitrarily phased polynomial-deconvolution rows also have exact
named Lean counterparts.  The Appell lattice theorem is now Lean-proved:
Lean covers both its arbitrary-phase `0 <= n <= N` formula and its
degree-`N+1` clause at the parity-selected superconvergent phases.  The same
compiled synthesis module gives the exact physical quadrature form of forced
superconvergence, with the phase dictionary and existing positivity,
rational-dyadic-value, and finite-support kernels.  This does not claim a
classification of every superconvergent phase or sharpness beyond the stated
degree.  The static canonical validator passes.  `PROVENANCE.md` records source
and asset lineage.

The new `FabiusFunction.FabiusInverseExactDyadicModulus` module supplies the
complete formal counterpart of `co:prop:exact-dyadic-modulus`: two definitions
and ten theorems cover the exact ceiling, positivity, endpoint bound, fixed-dyadic
arithmetic and strict-modulus leastness, the smaller-denominator endpoint
counterexample, and the logarithmic `1/n` witness with convention `d(0)=1`.
The compiled declarations
`Fabius.inverseFabiusExactDyadicDenominator_primrec` and
`Fabius.inverseFabiusExactLogarithmicDenominator_primrec` close the remaining
recursion clause, so that source proposition is now one of the 57 Lean-proved
rows.  Its leastness is only for the fixed dyadic target; `1/n` is witness-only,
and `d(0)=1` is a convention with no modulus asserted at zero.

There is no package-wide checksum gate. The purpose-specific
`SOURCE_CLOSURE.sha256` and migrated-asset disposition have narrower source
integrity and migration roles. The former root and asset `SHA256SUMS`
workflows are retired and no longer generated; the repository ban applies
exactly to basenames `SHA256SUMS` and `SHA256SUMS.*`. Historical closure
digests remain provenance only, while the approved generator owns the current
23-input record.

The result and asset extractors are pinned by
[`audit/SOURCE_REVISION`](audit/SOURCE_REVISION) to
`0a0cdabeb72a6f7d67cfdfb76d02a8f7381c7bf7`.
The five later notation-normalized source layouts remain recoverable together
at `93db15ad3c0645bd3cfd0a3e6e694e3c86a3aa2b`, a complete pre-retirement
repository snapshot. The old paths are retained as provenance locators, not
as live links.

The thirteen newest exact source-row matches are abstract effective inversion,
centered Appell deconvolution, positive-degree Appell mean-zero,
arbitrary-phase polynomial deconvolution, forced superconvergence, and finite
Appell lattice reproduction, together with the exact-dyadic repository modulus
and the leading Laurent coefficient at every nonzero centered-MGF pole, plus
the exact finite-prefix Appell expansions and their finite Richardson recovery,
the uncentered finite-prefix Thue--Morse collapse, its canonical Prouhet
corollary, and the centered collapse.
The superconvergence pair uses
`FabiusFunction.RvachevSuperconvergentSynthesis`: its phase dictionary
specializes the selected phases at `M = 2^N`, its physical quadrature wrapper
proves polynomial exactness through degree `N+1`, and its Appell wrapper proves
the corresponding finite lattice identity.  These declarations do not assert
an all-phase classification or a sharpness theorem.

`FabiusFunction.RvachevLaurentLeading` supplies the exact one-definition,
six-theorem correspondence for `is:p2:thm:Laurent-leading`.
`Fabius.rvachevCenteredMGF` fixes the manuscript normalization, while
`Fabius.rvachevCenteredMGF_eq_rvachevFourierProduct`,
`Fabius.rvachevCenteredMGF_pi_mul_I_int`,
`Fabius.rvachevCenteredMGF_pi_mul_I_int_ne_zero_of_odd`,
`Fabius.tendsto_sub_pow_mul_inv_rvachevFourierProduct_int`,
`Fabius.tendsto_rvachevCenteredMGF_laurent_int`, and
`Fabius.tendsto_rvachevCenteredMGF_laurent_two_pow_mul_odd` prove the rotation,
odd-core value and nonvanishing, generic cofactor limit, and both general and
manuscript-normalized Laurent limits.  The three limits use punctured
neighborhoods: Lean totalizes the inverse to zero at a pole, so an unpunctured
limit would be false.  This promotion does not cover lower Laurent
coefficients or the later Appell-coefficient asymptotics.

`FabiusFunction.FinitePrefixAppellRecovery` is the exact eleven-definition,
seventeen-theorem compositional package for
`is:p2:thm:finite-prefix-expansion` and
`is:p2:thm:exact-recovery`.  The declarations
`Fabius.uncenteredDyadicPrefixAppellPolynomialRat_eq_sum` and
`Fabius.centeredDyadicPrefixAppellPolynomialRat_eq_sum_even` give the printed
uncentered and centered expansions for every `N,n`, including `N = 0`, with
`mu_r = halfMoment r`, `m_(2r) = moment r`, and exact bases `1/2` and `1/4`.
The two free-scale polynomials, their `eq_eval_scale` bridges, and
`Fabius.natDegree_uncenteredDyadicPrefixAppellScalePolynomialRat` and
`Fabius.natDegree_centeredDyadicPrefixAppellScalePolynomialRat` prove degrees
`n` and `n/2` in `Polynomial (Polynomial ℚ)`.  That coefficient-ring statement
is essential: after fixing the inner variable, the centered leading
coefficient can vanish (for example for odd degree at `x = 0`).  Finally,
`Fabius.kabayaIriAppellPolynomialRat_eq_sum_prefix` and
`Fabius.rvachevAppellPolynomialRat_eq_sum_prefix` recover the full polynomials
from respectively `n+1` prefixes at base `1/2` and `n/2+1` prefixes at base
`1/4`, at every starting depth and without a limit.  The prefix moments are an
algebraic finite-binomial-convolution model; no random-variable, `HasLaw`, or
MGF realization bridge is claimed.

The zero-definition/eight-theorem
`FabiusFunction.FinitePrefixThueMorseCollapse` module makes
`is:p2:thm:TM-uncentered`, `is:p2:cor:Prouhet-canonical`, and
`is:p2:thm:TM-centered` exact.  The uncentered main theorem gives
`(-1)^N (1/2)^choose(N+1,2) n.descFactorial N x^(n-N)` on the complete
depth-`N` signed grid, with companion theorems for the vanishing range `n < N`
and the first constant `(-1)^N N! (1/2)^choose(N+1,2)`.  The centered
successor theorem uses the manuscript's literal grid
`x + (1 - 2^-(m+1)) - k/2^m` and has the sign-free scale
`(1/2)^choose(m+1,2)`; its total common-denominator companion extends the
formula to `N = 0`.  All eight declarations are rational coefficient-model
identities.  They add no random-variable, `HasLaw`, analytic-MGF, or separate
Barnes-identification theorem.

## Inverse-asymptotics subgroup closure

The former `inverse-asymptotics-and-computability/` subgroup is fully
dispositioned and consolidated here, rather than merely summarized. Its three
masters contribute 152 of the 194 concordance rows:

- `Inverse_and_Sampling_Frontiers`: 83 rows;
- `Inverse_Endpoint_All_Orders`: 29 rows; and
- `Inverse_Fabius_Computability_Report`: 40 rows.

Their canonical classifications are 41 exact Lean matches, 70 complete
human-proved frontier results, 18 non-live source environments (seven
definitions, three algorithms, two examples, four editorial obligations, and
two superseded source conjectures), nine explicitly retained conjectures, and
14 explicitly labelled open problems. The three package directories contribute
67 audited files, and the subgroup README is a 68th disposition row.
`ASSET_DISPOSITION.csv` accounts for all of them: unique scripts, exact tables,
figures, generated fragments, and captured checks were retained in the
deduplicated asset tree; superseded masters and renderings remain recoverable
from the immutable pre-retirement revision. Thus the historical subgroup
contains no live theorem, proof, or reproducibility payload that is absent or
unaccounted for here.

## Publication receipt chronology

The following tuple was accepted for the first-merge source snapshot:

- `inverse_fabius_theory.tex`: 293 lines, 11,514 bytes, SHA-256
  `92fab1fae38bbcf86a45b51bfe7ff34e2801361df9d2f3d6aa3de4dc966eaa3c`;
- ordered 14-file TeX graph: 10,909 lines, 438,542 bytes, aggregate
  `24bdab6491f5ca84fbb9e716f92c7923e8961b6acbc793d9aa5e0faa68852444`;
- purpose-specific source-only closure digest
  `e07cb51f4fe072cd79a014cc891cb8cede62880593d7659b17da9377a21099bc`;
- passes 132/137/137;
- 137-page / 2,045,463-byte PDF, SHA-256
  `ca403c74e2b46923ce9ac1eda547ab1bcb5e71039b35c8ee394acdd2014c4f8e`;
- 1,569-line / 64,081-byte log, SHA-256
  `d4aa25579c958e11c59d914c74dfca331fc2bbccf7bba4715dcd18fa050e771f`.

The incoming `b899` checkpoint used the same driver, a 17-file /
10,682-line / 431,748-byte closure with digest
`6e4e6fde424fd5046467b1f1cec0c19b6c10eb681fae4ba7cc53e14b6a5bf61e`,
and a 137-page / 2,045,486-byte PDF with SHA-256
`cee0de894656562fbdb75d6304055fc03fae06203985119419e465a5cd213995`.
Both 137-page builds passed their recorded gates. The preceding 134-page /
2,027,726-byte PDF, SHA-256
`22bc68d855ad04dde9654e9fbd20b3ba7f05a33e3c5df0e5b80bb8991c94b41d`,
and older closure digests remain explicit history.

The accepted current inverse source/PDF tuple is recorded in the
[authoritative receipt
register](../../MANIFEST.md#current-post-merge-publication-receipts).
Package checksum manifests are retired repository-wide;
`SOURCE_CLOSURE.sha256` and `ASSET_DISPOSITION.csv` retain scoped evidence
without acting as whole-package checksum gates.

The mathematical consolidation and provenance gate are complete.  The five
source packages and their retained renderings are historical inputs represented
by the immutable revision, concordance, migrated evidence, and repository
history; they are not parallel renderings of this canonical master.
