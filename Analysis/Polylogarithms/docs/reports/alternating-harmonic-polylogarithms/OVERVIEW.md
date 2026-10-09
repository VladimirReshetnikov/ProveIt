# Alternating harmonic polylogarithms: overview of the sources

Reconciliation note, 2026-10-09. `README.md` here is the base delivery's own
README, kept as delivered; this file says how the merged report's sources
fit together. Delivered files are not edited. All sources are AI-assisted,
unrefereed research drafts; nothing is formalized. Placement `06039f4794`;
the status of every claim and correction of the PolyLog programme is kept in
the project README,
[Status of claims, and known defects](../../../README.md#status-of-claims-and-known-defects).

## Files by source

**11 `polylogarithms_reflection_depth_transition_2026-10-07`: the base**
(unprefixed manuscript)

- `article.tex`: *Reflection, certified evaluation, and a depth–exponent
  transition for alternating harmonic polylogarithms*
- `README.md` (delivered)
- `code/11-reflection-transition-Makefile`,
  `code/11-reflection-transition-additional_diagnostics.py`,
  `code/11-reflection-transition-polylog_research.py`,
  `code/11-reflection-transition-test_core.py`,
  `code/11-reflection-transition-transition_polynomials.py`
- `data/11-reflection-transition-additional_diagnostics.json`,
  `data/11-reflection-transition-build_and_test_status.json`,
  `data/11-reflection-transition-certified_intervals.json`,
  `data/11-reflection-transition-environment.json`,
  `data/11-reflection-transition-odd_weight_checks.json`,
  `data/11-reflection-transition-reflection_checks.json`,
  `data/11-reflection-transition-requirements.txt`,
  `data/11-reflection-transition-source_manifest.json`,
  `data/11-reflection-transition-transition_checks.csv`,
  `data/11-reflection-transition-transition_checks.json`,
  `data/11-reflection-transition-transition_polynomials.json`,
  `data/11-reflection-transition-transition_polynomials.tex`,
  `data/11-reflection-transition-verification_run.txt`,
  `data/11-reflection-transition-verification_summary.json`
- 11's seven correction proposals, its replacement parity statement and its
  patcher `apply_goncharov_fix.py` are in
  [`../corpus-corrections/`](../corpus-corrections/) (prefix
  `11-reflection-transition-`).

**Members placed elsewhere:** 10's odd alternating Euler sums and
inverse-argument mixed doubles `Li_{a,b}(z,1/z)` (`sections/euler.tex`,
`code/10-exact-structure-verify_mixed_and_euler.py`) in
[`../rational-grid-distribution-ranks/`](../rational-grid-distribution-ranks/);
12's Gaussian-ladder reduction (`sections/gaussian_reduction.tex`,
`code/12-relation-spaces-verify_gaussian.py`) in
[`../corpus-corrections/`](../corpus-corrections/).

## `S_{2m+1}`, delivered three times

For every `m ≥ 0`,
`S_{2m+1} = (2m+1)β(2m+2) − 2β(2m+1)log 2 − Σ_{j=1}^{m}(2 − 2^{−2j})β(2m−2j+1)ζ(2j+1)`,
the even-total-weight half of `thm:alternation` (`S₅`, `S₇` are `m = 2, 3`).

- **Base: 11**, which proves the incomplete-beta reflection for
  `T_{p,r}(a) = Σ(−1)ⁿe_r(n)/(n+a)^p` at *every* harmonic index `r`;
  `S_{2m+1}` is the case `r = 1`. 11 alone adds signed first-omitted-term
  truncation bounds, eight rational interval certificates and the joint
  depth-exponent transition at `p/r = log r + c`.
- **10** proves the same family with a generator (and joins this report as a
  part for its inverse-argument mixed doubles, the same Gaussian/Eisenstein
  depth thread).
- **12** proves it as `S_{2m−1}` at every weight (11's secant form in other
  notation).

Credit all three. These are the intake dossier's (dossier138_POLYLOG)
findings; it checked `S₁ … S₉` in both printed forms numerically, but the
comparison is not re-proved in this note.

## Caveats

- The "depth" of the transition is the harmonic index (displayed nesting
  length), not minimal motivic or numerical depth, as 11 itself says.
- The prefixed scripts still name their delivered paths (11's Makefile builds in
  a delivered `article/` directory; `polylog_research.py` writes to
  `../results/` beside `code/` by default); rerun on copies in a scratch
  directory under the delivered names, or pass `--output`.
- `apply_goncharov_fix.py` (in `../corpus-corrections/code/`) patches a
  historical draft; it has not been run, and must not be applied without
  Vladimir's decision. The correction is recorded in the project README.
