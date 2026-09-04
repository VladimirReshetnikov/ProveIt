# Repository audit

This note records the repository review performed after archival intake.  It is
bookkeeping, not a mathematical source, and it does not elevate any manuscript
claim to Lean-proved status.

## Arrival provenance

The package arrived on 2026-08-30 in
`inverse_fabius_iterates_nowhere_analytic.zip` (1,137,032 bytes; outer SHA-256
`8b1c05d59e120ecd20d69cd5aeb0009639f2b3b9a6c9fef32bdf82270eee16bd`).
The submitted `SHA256SUMS.txt` had SHA-256
`c270903631b0942aa7f7742b84ea0117bb9f2f4cc0d0eb374889077ba37873a0`;
all 13 listed payload entries verified before any normalization.  Its exact
bytes were preserved as `SHA256SUMS.arrival.txt`; the post-review
`SHA256SUMS.txt` intentionally differed from that arrival copy. Both
package-local ledgers were retired repository-wide on 2026-09-01 and remain
recoverable from Git history. `MANIFEST.txt` remains the unchanged submitted
13-file inventory.

Arrival source and PDF hashes were respectively
`f4757daa3be451bf208cc858897d21b66e2dab4c9982f74d0c536d67b8beb6ab`
and
`0ac2b507168d1cc73624a425852658c3a2d46ddb51cf0a19b1a057d095f8462a`.

## Hostile claim review

The report is a derived companion to
`drafts/representations/fabius_iterates_nowhere_analytic/`, not an
independent forward-iterate result.  Its forward-engine source substantially
reused the submitted forward report and retained four defects that had already
been repaired in the current sibling.  The TeX now ports those repairs:

- the weighted partition-defect proof gives an explicit estimate uniform in
  the excess parameter, rather than only comparing `O(e log m)` with
  `-Omega(e m)`;
- the outer function in the two-spine lemma is smooth near its evaluation
  point `h(x)`, not merely near `x`;
- the finite tie-set union is literally empty at `n = 1`;
- the source map names the live `Monotonicity.lean`, not the nonexistent
  `StrictMonotonicity.lean`.

The inverse theorem was checked separately.  Interior nowhere analyticity
follows soundly from the analytic inverse-function theorem and the corrected
forward theorem.  Formal Taylor-radius convergence is invariant under smooth
local inversion with nonzero derivative because the two Taylor series are
unique formal compositional inverses; convergence of either series gives an
analytic inverse germ with the other Taylor series.  The iterated endpoint
scale follows by a finite induction from the one-step quadratic logarithmic
law.  No concrete mathematical gap was found in those arguments.

The status and novelty boundary is narrower than the submitted prose implied:

- inverse nowhere analyticity for every positive iterate already appears as a
  corollary in the corrected forward report;
- Lean proves the one-fold inverse analytic locus through
  `fabiusInv_not_analyticAt` and `fabiusInv_analyticAt_iff` in
  `InverseNotElementary.lean`;
- Lean proves the one-fold positive-order endpoint Hölder obstruction through
  `not_exists_fabiusInv_le_const_mul_rpow_near_zero` in
  `FabiusInverseAsymptotic.lean`;
- the `n >= 2` forward and inverse iterate theorems, formal-radius transport,
  all-order affine center jet, and iterated endpoint scale have no exact proved
  Lean counterparts in the current corpus.

The report now has 19 nonconjectural labelled manuscript results, two live
conjectures, and three numbered warning quarantines.  Former Conjecture 14.1
incorrectly claimed that formal reversion transports eventual jet-vanishing.
At the quarter point the forward Taylor germ is the finite quadratic
`5/72 + z + 4z^2`, while its inverse germ is the infinite convergent series
`(sqrt(1 + 16w) - 1)/8`; formal reversion transports positive radius, not
polynomiality.  The forward-only Taylor-locus classification remains open.
Former Conjecture 14.2 is already discharged: a forward tie forces the dyadic
orbit point to be `1/4` or `3/4`, whose next image is the non-dyadic `5/72` or
`67/72`; eventual vanishing of the dyadic amplitude and the binary-transition
lemma exclude persistent cancellation.  Former Conjecture 14.4 is identical
to Conjecture 14.3 in the corrected forward report and is not an independent
inverse claim.  Only the direct inverse-spine and nested-Lambert statements
remain live, explicitly manuscript conjectures with no Lean counterparts.
Finite-order numerics establish neither.

## Numerical replay and limitations

The submitted command through order 22 was replayed outside the package with
`MPLBACKEND=Agg`, CPython 3.12.13, NumPy 2.3.5, SciPy 1.16.3, Matplotlib
3.10.8, and mpmath 1.4.1. All seven generated files reproduced byte-for-byte
before repository line-ending normalization, including the maximum
formal-reversion residual reported in the submitted metadata. The CSV writer
now requests LF explicitly, and the current CSV is the same numerical table
with deterministic LF endings.

Three figures (`fabius_iterates.png`, `spine_comparison.png`, and
`spine_remainder.png`) are byte-identical to the forward package and retain
that provenance.  The Taylor-root figure differs from the forward version and
the inverse Taylor-root figure is new.

The replay is reproducibility evidence, not proof.  The submitted requirements
are unpinned.  The script writes five PNG files, the CSV, and metadata to its
chosen `--output-dir`, whereas the TeX reads PNG files from `figures/`; the
documented command therefore does not refresh embedded figures without an
explicit copy step.  The archived `numerical_output/` intentionally contains
only the CSV and metadata.  Although five anchor values are printed, only
`up(0)` and `F(1/2)` are enforced by tolerance checks.

## Document normalization

The submitted PDF was 23 A4 pages in Latin Modern.  The source has been moved
to the primary document's verbatim A4/27 mm canonical preamble, with only
allowed metadata/running-head changes and used local notation after that
block.  The current PDF and current ledger are validated separately after the
required clean three-pass build.
