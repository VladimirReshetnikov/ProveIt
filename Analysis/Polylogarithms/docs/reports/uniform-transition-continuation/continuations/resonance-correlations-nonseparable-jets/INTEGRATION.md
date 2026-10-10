# Proposed integration into ProveIt

Baseline: `570b0567f311cf1890865065896be2665f469e4f`.
This package has not changed or published anything in the GitHub repository.

## Intake

The package can first be placed under a new thematic report directory such as
`Analysis/Polylogarithms/docs/reports/resonance-correlations/`, with an intake
entry in `docs/incoming/README.md` following the repository's current process.
This path is a proposed destination, not an assertion that it already exists.

The main article sources use a single preamble and modular section files.
The following map supports selective integration into the canonical manuscript.

| File | Main content | Proposed canonical placement |
|---|---|---|
| `sections/01_scope.tex` | Baseline, notation, proof status | Intake/source note |
| `sections/02_resonance.tex` | Uniform resonance and Stieltjes finite parts | Lerch boundary layer; links to Chapter 07 |
| `sections/03_gamma.tex` | Hurwitz products, strict convexity, mixed cusps, balanced tower | Chapter 07 integration and log-Gamma calculus |
| `sections/04_herglotz.tex` | Joint high-order transition and profile calculus | Chapter 09 after `09-herglotz-jets.tex` |
| `sections/05_nonseparable.tex` | Two-generator theorem and boundary examples | Chapter 08 after `08-integral-jets.tex` |
| `sections/06_audit.tex` | Audit, normalization, scope, replay evidence | Editorial ledger plus relevant local remarks |
| `sections/07_questions.tex` | Sixteen concrete research questions | Topic agendas |

## Principal labels

- `res:main`: uniform all-order resonance, all integer k.
- `res:highorder`: limiting coefficient function pi w / sin(pi w).
- `gamma:thm:shifted-product`: shifted Hurwitz product and convergence domain.
- `gamma:thm:jet-cusp`: all mixed spectral-jet increments.
- `gamma:thm:loggamma-concavity`: exact convergent series and strict concavity
  of S, hence strict convexity of R.
- `gamma:cor:tail`: analytic one-sided truncation bound.
- `gamma:cor:half-maximum`: exact half-shift extremum.
- `gamma:thm:balanced-correlation`: integrated polygamma correlation ladder.
- `herg:thm:mixture`: exact gamma mixture and finite-order remainder.
- `herg:thm:expansion`: uniform complete x/r transition expansion.
- `herg:thm:profilezeros`: centered reciprocal profile and all its zeros.
- `herg:thm:dual`: convergent odd-zeta and Bessel profile formulas.
- `herg:thm:primitives`: Gamma and dilogarithm normalized primitives.
- `ns:thm:two-generator`: Frobenius two-generator colength theorem.
- `ns:prop:counterexample`: genuinely three-generator obstruction.
- `audit:lerch-typo`: corrected external-source Lerch normalization.

The local macro definitions in the article should be reconciled with the
canonical preamble. In particular, `\zeta^{[r]}` and `\Li_s^{[r]}` mean
spectral order derivatives, while argument derivatives are distinguished in
the text. `F`, `S`, and `G` are local notation in different sections, not
global identifiers. Rename them if sections are merged into a single larger
discussion. Adjust figure paths when moving the Gamma section. The theorem
labels have semantic prefixes, but still check for existing label collisions
before integration into a later revision.

## Existing results that should retain credit

- Lerch pole cancellation and fixed-order endpoint regularity already occur
  in the preserved `lerch-boundary-continuation` report.
- The normalized Stieltjes primitives and zero-shift Hurwitz/Gamma integral
  calculus are established inputs, not claims of new evaluation.
- The all-ring distribution basis, characteristic-two reflection–Koszul
  model, and finite-free integral torsion theorem are inputs from Chapter 08.
- The fixed-argument Herglotz high-order expansion and its oscillatory
  correction are established inputs from Chapter 09.

## Resolved directions and remaining boundaries

The joint-limit question at the end of `09-herglotz-jets.tex` is resolved
on compact positive ratio intervals, together with leading endpoint limits.
The all-order endpoint matching problem remains open.

For formal jets, every two-entry active sequence over a rectangular jet
algebra now has an explicit dimension and abelian Smith formula. More active
entries are also covered when the active ideal still needs at most two
generators. The formula is not unrestricted: the three-generated ideal
`(xy,xz,yz)` in `F_2[x,y,z]/(x^2,y^2,z^2)` has Koszul dimensions
`(4,14,14,4)`. At level 105 its reflected dimension is 210, not the naive 208.

Even when the dimension law applies, replacing every torsion module by
copies of `S/I` is invalid. The level-15 mixed example distinguishes
`S/I` from its Frobenius dual annihilator.

None of these formal results establishes arithmetic independence of
evaluated periods. No S6 special-value proof or Stark identity is claimed.

## Correction ledger entry

**External source only:** Gay–Sebbar, *Pseudo-differential operators on the
circle, Bernoulli polynomials* (2024), printed page 4, the unnumbered display
between Eqs. (1) and (2). Insert the factor z in
`Li_s(z) = z Phi(z,s,1)`. This was verified in the published PDF. The pinned
canonical manuscript's `zeros:eq:lambda` and following a=1 specialization
are already correct; no patch to them is needed.

## Replay artifacts

Keep the exact finite-field verifier and its output beside the algebraic
section. The analytic data are numerical diagnostics and should retain that
designation. In particular, omitted-term tail estimates are not complete
roundoff certificates. The `gamma_correlation.py` module provides reusable
evaluation with an explicit analytic tail estimate, and the plotting source
reproduces the supplied vector figure.

