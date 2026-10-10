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

## Later sources (batch 141, 9 October 2026)

Dated note, 2026-10-09. Two continuations of the unified manuscript's chapter-8
distribution-rank observation (`tower:thm:rank`) are added to this report as sources 20
and 22 (placement `3b0bae5f5a`; arrival commit `a2a4cf58c4`). Their
manuscripts, PDFs and delivery READMEs are not staged; they are retrievable from the
arrival commit. Three companions of the same arrival went to
[`../gaussian-parity-reductions/`](../gaussian-parity-reductions/) (21, 23, 24). Both were
pinned after this report was placed (20 at `29d9344771`, 22 at `85c89e5d0b`), but
neither cites it or 15: both work from the manuscript alone and credit only the classical
universal-distribution antecedents (Kubert; Ouyang). Both are unrefereed and say they were prepared with OpenAI assistance (22:
ChatGPT); neither claims a proof-assistant check.

**20 `ProveIt_Polylogarithms_Distribution_Jets_2026-10-09`**, *Finite Distribution
Modules, Spectral Jets, and Cyclotomic Trace Identities* (26 pp.):
`20-distribution-jets-{AUDIT,RESULTS}.md`, the proposed manuscript fragments
`20-distribution-jets-integration-*` (README, chapters 4, 7 and 8, a bibliography item),
`code/20-distribution-jets-*` (exact and character verifiers, numerical diagnostics,
`S₄` row generator and standard-library certificate replay, `build.sh`, `test.sh`),
`data/20-distribution-jets-*` (rank and character check records, primitive-grid
certificates for `q = 12, 21, 30, 60`, the `S₄` row matrix and annihilator, numerical
records, `provenance.json`).

**22 `polylogarithms_conductor_descent_2026-10-09`**, *Conductor Descent and Flat
Distribution Ranks* (21 pp.): `22-conductor-descent-{CORRECTIONS,INTEGRATION,STATUS}.md`,
the proposed fragments `22-conductor-descent-integration-chapter08_distribution_rank.tex`
and `…-integration-editorial_ledger_entry.md`, `code/22-conductor-descent-*` (the
delivered `src/` scripts and `Makefile`), `data/22-conductor-descent-*` (exact checks, the
level-12 polynomial normal form, trace coefficients, the `S₄` obstruction, identity
catalogue, `SOURCE_SNAPSHOT.json`, `MANIFEST.sha256` as delivered).

### The rank theorem, fifth and sixth times

Both prove this report's theorem again, over a polynomial ring in independent prime
weights over a characteristic-zero character splitting field: the distribution quotient
is free of rank `φ(q)` with a conductor basis (20 `thm:universal`, 22 `thm:free`; the
coefficient `A_{d,f,χ}` is 10's `eq:dist-normal-coefficient`), the endpoint-fixed rank is
`q − φ(q)` at every specialization (20 `cor:anchored`, 22 `cor:rank`), and finite jets
are free of the same rank (20 `thm:jet-rank`, 22 `thm:jets`). 20's local Smith factors
and single-prime resonances (`thm:smith`, `cor:central`) are 10's
`thm:dist-jet-defect` and `prop:dist-resonance-multiplicity` (the same count
`#{p | q : p ∤ f, p^{s₀} = χ(p)}`). Credit 10 as the base and 20, 22 as further proofs,
as for 12, 13 and 15.

### What is new in 20 and 22

- **Both:** all-order Hurwitz–Stieltjes reductions for every index `n ≥ 0`, including
  the principal pole correction at parameter order `k = 0` (20 `thm:underived`, 22
  `prop:kzero`); and cyclotomic polylogarithm traces
  `Σ_{a ∈ U_q} χ(a) ∂_s^j Li_s(e^{2πia/q})|_{s=1}`: the principal trace vanishes to exact
  order `ω(q) − 1` with leading value `(−1)^{ω}(ω−1)! Π_{p|q} log p` (20 `thm:principal`,
  22 `thm:principalzero`), so at level 30 the second derivative is `−2 log2 log3 log5`.
- **20:** the factored primitive-grid determinant (`thm:determinant`), finite residue
  formulas with negative spectral parameter, exact support, signs, complete monotonicity
  and a uniform denominator (`thm:finite-C`, `cor:support`, `cor:monotone`,
  `prop:denominator`), and nonprincipal trace zeros (`thm:trace-zero`).
- **22:** finite Möbius conductor descent for every Stieltjes layer
  (`thm:stieltjes`), descent of the primitive-root traces (`thm:polylogdescent`), the
  next two principal coefficients, and the twisted level-260 identity
  `Σ_{a ∈ U_260} χ₄(a) ∂_s² Li_s(e^{2πia/260})|_{s=1} = iπ log5 log13` (`thm:twisted`).
- Both also ship a finite `S₄` row-space obstruction (96 rows); see
  [`../gaussian-parity-reductions/`](../gaussian-parity-reductions/), where `S₄` is
  proved by 24's exact rational certificate (911 double-shuffle and distribution rows
  plus one convergent duality), replayed at intake with the delivered standard-library
  verifier (empty residual), row schemas checked by hand and the identity confirmed to
  40 digits; no independent re-derivation of all 911 rows has been made. That relation
  family is larger than these 96 rows. Both repeat corrections already recorded in the
  project README (the mixed-point antisymmetry, the weight-one endpoint, the cubic
  moment's attribution).

### Caveats for 20 and 22

- Intake checked the level-30 and level-210 principal traces and the level-260 twisted
  trace independently (Cauchy coefficients of `q^{−s} Σ_b c_b ζ(s, b/q)` on a circle about
  `s = 1`, 30 digits; dossier141_POLYLOG); the general theorems were not re-derived.
- The ranks are formal-quotient dimensions; 20 and 22 say they did not recover the
  historical matrices of the manuscript's finite observation.
- Their chapter-8 replacement texts are superseded: the rebuilt manuscript already
  states `tower:thm:rank` as a uniform corollary.
- The prefixed scripts resolve delivered relative paths and rewrite their records;
  rerun on copies under the delivered names.
