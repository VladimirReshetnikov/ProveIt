# Rational-grid distribution ranks: overview of the sources

Reconciliation note, 2026-10-09. `README.md` here is the base delivery's own
README (10's `README.txt`), kept as delivered; this file says how the merged
report's sources fit together. Delivered files are not edited. All sources
are AI-assisted, unrefereed research drafts; nothing is formalized.
Placement `06039f4794`; the status of every claim and correction of the
PolyLog programme is kept in the project README,
[Status of claims, and known defects](../../../README.md#status-of-claims-and-known-defects).

## Files by source

**10 `polylogarithms-exact-structure`: the base** (unprefixed manuscript)

- `article.tex`: *Exact Structure and Certified Computation in the
  Polylogarithm Drafts*; `references.tex`; `sections/asymptotics.tex`,
  `sections/audit.tex`, `sections/bridges.tex`, `sections/distribution.tex`,
  `sections/euler.tex`, `sections/modular.tex`, `sections/research.tex`
- `README.md` (delivered `README.txt`)
- `code/10-exact-structure-build.sh`,
  `code/10-exact-structure-modular_rows.py`,
  `code/10-exact-structure-parameter_asymptotics.py`,
  `code/10-exact-structure-verify_distributions_and_bridges.py`,
  `code/10-exact-structure-verify_mixed_and_euler.py`
- `data/10-exact-structure-distributions_and_bridges.json`,
  `data/10-exact-structure-mixed_and_euler.json`,
  `data/10-exact-structure-modular_rows.json`,
  `data/10-exact-structure-parameter_asymptotics.json`,
  `data/10-exact-structure-requirements.txt`,
  `data/10-exact-structure-source-manifest.json`,
  `data/10-exact-structure-verification-summary.json`
- `figures/10-exact-structure-derivative-profile.pdf`,
  `figures/10-exact-structure-derivative-profile.png`
- 10's correction register (`X1`-`X17`) is in
  [`../corpus-corrections/`](../corpus-corrections/) as
  `10-exact-structure-CORRECTIONS.txt`.

10 is an omnibus manuscript. Besides the ranks it carries parts that the
merge credits to other reports: the spectral expansion of `γ_n^{(k)}(1)` and
the normalized bridges (`sections/asymptotics.tex`, `sections/bridges.tex`;
spine of [`../stieltjes-derivative-zeros/`](../stieltjes-derivative-zeros/)),
and the odd alternating Euler sums and inverse-argument mixed doubles
(`sections/euler.tex`; spine of
[`../alternating-harmonic-polylogarithms/`](../alternating-harmonic-polylogarithms/)).

**Members placed elsewhere:** 12's rank sections
(`sections/distribution_ranks.tex`, `code/12-relation-spaces-verify_ranks.py`,
`code/12-relation-spaces-verify_jet_ranks.py`) in
[`../corpus-corrections/`](../corpus-corrections/); 13's distribution-module
theorem in the `article.tex` of
[`../stieltjes-derivative-zeros/`](../stieltjes-derivative-zeros/).

## The rank theorem, delivered three times

The formal quotient by the distribution rows has dimension `φ(q)`, and
`φ(q) − 1` with the endpoint as background, for every denominator `q`; finite
jets form a free module of the same rank; with reflection rows the rank is
`φ(q)/2 − 1` (`k` odd) or `φ(q)/2` (`k` even). This proves `thm:rank` of
`stieltjes-parameter-derivative-tower` and `prop:jetrank` of
`stieltjes-antiderivative-ladder` as formal statements.

- **Base: 10**, the most general proof: prime weights arbitrary in any
  commutative `C`-algebra, including nilpotent and resonant ones (resonance
  changes which coordinates are adequate, not the rank).
- **12** gives the same character proof with rational weights, then jets.
- **13** needs `Re s > 0`, so it covers the nonresonant case only.

Credit all three. These are the intake dossier's (dossier138_POLYLOG)
findings; it recomputed the exact ranks for `q ≤ 60` (and with reflection
for `q ≤ 40`, `k ≤ 4`), but the comparison is not re-proved in this note.

**A fourth proof (batch 139, dated note 2026-10-09).** 15
(`polylogarithm_research_20261009`, placed in
[`../gaussian-parity-reductions/`](../gaussian-parity-reductions/), files
`15-parity-ranks-*`) proves the same all-denominator laws again from the manuscript's
labels (`stieltjes:prop:jetrank`, `tower:thm:rank`): the weighted distribution module
with any completely multiplicative rational weight is the regular representation of
`(Z/qZ)^×` (`thm:distribution`), with the jet, first-Stieltjes and parameter-derivative
counts as corollaries, 1,087 exact rank checks, and, for weight `m^s` with `s` a
nonzero integer, a `Q`-basis on the primitive residues with eight rational
elimination certificates (`cor:primitive`). The basis statement is the rational form
of the top-denominator basis proved here (paragraph after `eq:dist-top-coordinate`,
`Re s ≠ 0`); 15 did not cite this report. Credit it as a further proof, not a new
result.

## Caveats

- The ranks are dimensions of formal quotients, not arithmetic independence
  of the evaluated constants (all sources say so).
- The prefixed scripts still name their delivered paths, and `article.tex`
  expects its figure under the delivered name; rerun on copies in a scratch
  directory under the delivered names.
