# Fresh continuation replay commands

Run from `docs/manuscript`, with Python, mpmath and sympy available. These
commands preserve the historical code and receipts, writing only into the
manuscript verification directory. Core, build and render commands are in
the [manuscript README](../README.md).

```powershell
python ../reports/rational-grid-distribution-ranks/code/10-exact-structure-verify_mixed_and_euler.py --quick --output verification/inverse-euler-results.json
python verification/replay_ranks.py
python verification/replay_spectral.py
python ../reports/rational-grid-distribution-ranks/code/10-exact-structure-modular_rows.py --dps 65 --rows 36 --output verification/modular-row-results.json
python ../reports/alternating-harmonic-polylogarithms/code/11-reflection-transition-polylog_research.py --full --output verification/harmonic-replay
python ../reports/stieltjes-derivative-zeros/code/06-zero-geometry-exact_verify.py --input ../reports/stieltjes-derivative-zeros/data/06-zero-geometry-certificates.json --output verification/zero-sign-results.json
python ../reports/corpus-corrections/code/12-relation-spaces-verify_cubic_class_numbers.py --output verification/cubic-class-results.json
python verification/replay_cyclotomic.py
python ../reports/herglotz-cyclotomic-obstructions/code/verify_J_evaluations.py --digits 65 --max-even-m 40 --output verification/J-evaluation-results.json
python ../reports/herglotz-cyclotomic-obstructions/code/certified_intervals.py --output verification/Herglotz-interval-results.json
python ../reports/herglotz-cyclotomic-obstructions/code/verify_truncation.py --quick --digits 55 --output verification/Herglotz-truncation-results.json
```

The rank wrapper checks q<=20 and bridge orders through 3. The cyclotomic
wrapper performs exact elimination through q=40 and checks the rank and J
criteria through q=1000. The spectral wrapper uses the bounded `--quick
--no-figure` configuration and redirects the source module's output root.
The harmonic `--full` run uses its longer exact-certificate configuration.
Counts and arithmetic scopes are in [VALIDATION.md](../VALIDATION.md).

The SHA manifests pin a particular reviewed release. Replaying may change
execution-time or environment metadata. Do not refresh hashes to disguise a
changed source, failed check or unreviewed PDF; perform the relevant checks
and rendered review before recording a new release.

## Gaussian parity, ladders, moments and certified evaluation

```powershell
python verification/replay_gaussian.py --part 14
python verification/replay_gaussian.py --part 16
python verification/replay_gaussian.py --part 17
```

These runs restore the delivered filenames inside the ignored, isolated
`verification/.scratch-gaussian/` directory. Historical placed files are read
only. Fresh reports are copied to `verification/gaussian-replay/`. Part 14
replays the word algebra, exact depth and ladder substitutions, cubic moment
certificate and independent numerical depth/ladder checks. It bypasses the
delivery's plotting dependency, which its original driver required even in
fast mode. Part 16 tests interval arithmetic, symbolic specialization and 89
interval residuals with eight independent quadratures. Part 17 replays its
symbolic solver and six positive-measure midpoint certificates. The source
hashes and restored-file maps are recorded for each part.

## Signed Euler kernels and Holder certificates

```powershell
python verification/replay_gaussian.py --part 18
python verification/replay_gaussian.py --part 19
python verification/replay_gaussian.py --part 19b
```

Part 18 uses 400 Euler terms, even weights through 16 and odd matrix ranks
through 31, plus a separate numerical diagnostic entry point. Part 19 uses
384-bit atom precision and independently replays every Holder center and
tail budget through finite nested sums. Part 19b generates 24 one-two rows
and compares them with integrals, checks the general closed formula, and
checks all positions through weight 8 at both sixth roots at 100 digits.
These runs read the immutable prefixed sources and write fresh receipts in
`gaussian-replay/18`, `/19` and `/19b`. The complete analytic arrival excerpts
in `gaussian-arrival-sources/` came from commit 412dbd0048 and are provenance
inputs; the canonical text is the edited chapter files.

## Five incoming packages

```powershell
python verification/replay_incoming.py --part rigidity
python verification/replay_incoming.py --part distribution
python verification/replay_incoming.py --part conductor
python verification/replay_incoming.py --part complement
python verification/replay_incoming.py --part reflection
wolfram -script verification/check-incoming.wls
python verification/check_reflected_sharp.py
```

The five wrappers restore full delivered layouts in `.scratch-incoming/`.
They never run the upstream flattening or manuscript patchers. Result files
are copied only if freshly modified by the run. Replays distinguish exact
finite arithmetic, outward rational certificates and floating-point
diagnostics; their summaries preserve the specific configurations. The
reflected sharp-corollary script uses 180-digit diagnostics, not intervals.

For a new release, run `check_document.py`, `build.py` (three serial passes),
`inspect_pdf.py`, and manually review the rendered PDF before running
`refresh_manifests.py` and `verify_receipts.py`. The refresher refuses changed
immutable package dependencies and raw archive/member hashes; when an arrival
archive has been retired upstream, it reads its pinned Git blob. It records
hashes and cannot itself confer a mathematical or visual review.

## Continuing research: new batch and higher zero thresholds

```powershell
python verification/replay_research.py --part rank
python verification/replay_research.py --part cm-zero
python verification/replay_research.py --part formal
python verification/replay_research.py --part angular
python verification/replay_research.py --part cayley
python verification/replay_research.py --part lerch
python verification/explore_higher_zero_transitions.py
python verification/certify_higher_zero_transitions.py
python verification/replay_higher_zero_independent.py
wolfram -script verification/check-research.wls
python verification/redraw_zero_profiles.py
```

Exploration proposes rational brackets; it supplies no accepted sign or
completeness assertion. The two exact higher-index certifiers enclose all
126 signs, using distinct coefficient implementations and cutoffs. Native
S2 quadrature is an independent numerical diagnostic. The plot redraw uses
Matplotlib, NumPy and SciPy; its dependency versions and preserved source
hash are recorded in zero-profile-redraw.json. It changes the notation,
not the historical mathematical curves, and writes a separate canonical
figure. Full incoming package layouts remain immutable; replays run in
.scratch-research. The active broader audit and research goal remain open.

## CM proofs and the two latest incoming batches

```powershell
python verification/replay_third.py --part herglotz
python verification/replay_third.py --part phase
python verification/replay_third.py --part uniform
python verification/replay_third.py --part boundary
python verification/replay_third.py --part signed
python verification/replay_fourth.py --part jets
python verification/replay_fourth.py --part integral
python verification/replay_fourth.py --part fractional
python verification/replay_fourth.py --part threshold
python verification/replay_fourth.py --part golden
python verification/certify_cm_nonvanishing.py
python verification/derive_cm_genus_extensions.py
python verification/certify_cm_single_and_weber.py
python verification/verify_cm_weber_field.py
wolfram -script verification/check-cm-research.wls
python verification/plot_cm_genus_embeddings.py
```

The wrappers copy immutable packages into ignored `.scratch-third` and
`.scratch-fourth` layouts. Exact reconstruction and optional Smith checks
are separate from the notation diagnostics. New CM scripts use rational
lattice caps and quadratic arithmetic, directed coefficient intervals with
CM integrality, and an independent finite-field irreducibility witness.
Native Wolfram checks and the finite-lattice plot are numerical diagnostics.
The all-parameter CM conclusions require the manuscript's written proofs.
The saved S8 coordinate receipt is an exact Fraction check of the displayed
normalized coefficients and primitive vector; it does not prove equality.
The signed replay reconstructs both frozen S6/S8 proximity enclosures.
Neither zero-containing residual interval proves a period identity.

## Separable multivariable distribution jets

```powershell
python verification/check_multivariable_distribution.py
```

The standard-library verifier expands original point symbols times all
truncated monomials, constructs the raw prime and reflection rows, and
computes their binary ranks with integer bit vectors. It imports no
normal-form or Koszul implementation. The 210-case sweep tests the new
all-level formula's finite consequences; its proof is in the manuscript.
