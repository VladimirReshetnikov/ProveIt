# Integration proposal

Suggested new report directory:

`Analysis/Polylogarithms/docs/reports/stieltjes-harmonic-resonance/continuations/lerch-selectors/`

Preserve the complete article and verification artifacts. The short fragment
in `integration/lerch_selectors_summary.tex` is optional; it is not a substitute
for the full proofs. It assumes the manuscript already provides `amsmath`,
`amssymb`, and a `theorem` environment. It introduces no global macros and
uses the `plsint:` label namespace. The standalone article uses `pls:`.

## Proposed ledger entries

| Claim | Status in this delivery | Main article |
|---|---|---|
| Integer-length single-order Lerch/polylogarithm selector classification | Proved for a>0, integer L>=1, 0<abs(z)<=1, modulo the declared finite remainder over C(s) | Theorem 3.1; Proposition 2.1 and Lemma 2.2 |
| Nonresonant double-endpoint obstruction | Proved at every degree | Theorem 4.2 |
| Finite-mixture resonance and exact support count | Proved at every even degree | Theorem 5.2 |
| Removable-integer order jets | Proved at every jet order | Theorem 6.1 |
| Euler-weighted Gamma/odd-zeta family | Proved at every degree in the family | Theorem 7.1 |
| Generalized Stieltjes weighted identities | Proved at every Stieltjes order | Section 8 |
| Joint twist/order confluence | Joint holomorphy and all mixed jets proved | Theorem 9.1 |
| Anchored shift primitives | Proved at every primitive order | Theorem 10.1 |
| arXiv:2609.13796v1 coefficient problem | Explicit binomial solution for every v>=2 | Theorem 11.1 |
| External Mellin and interpolation corrections | Derived from the paper's Definition 1; version-specific | Section 11.2 |

## Source questions

For the inspected *Affine Gamma Polarization* report's Section 11:

- Question 4: the integer-length functional classification is resolved;
  arbitrary rational, noninteger interval lengths remain separate.
- Question 5: resolved in the specified polynomial/functional setting.
  The proposed one-order, double-flat nonresonant deformation is impossible;
  an exact finite mixture is the replacement.
- Question 6: all-order coefficient and anchored-primitive results advance it,
  but the requested compact degree/order bivariate generator and complete
  multiple-Gamma classification are not supplied.

Do not change the status of S6, revised S8, or the general unequal-tail prefix
conjecture based on this report. Do not infer numerical period independence
from the C(s)-linear independence theorem.

## Attribution and dependencies

Credit Kim and Kim's classical Frobenius–Euler basis theorem. Credit the
classical Hurwitz/Lerch calculus, Eulerian real-rootedness, and existing
Espinosa–Moll work on weighted Hurwitz/log-Gamma integrals. The new report
supplies the selector interpretation with a full functional independence
proof, endpoint and resonance consequences, the resulting identity calculus,
and the explicitly identified external coefficient resolution.

Keep the external corrections separate from the canonical manuscript's
correction register until the relevant external reference is introduced.
The report does not assert that the canonical manuscript copied the erroneous
external formulas. Do not overwrite historical sources.

## Verification scope

969 exact assertions and 33 floating-point diagnostics passed. Six exact
assertions are deliberately corrupted-formula rejection controls. These tests
are finite evidence, not proof-assistant verification or interval certificates.
The theorem status is supported by the self-contained proofs in the article.
No repository writes were performed in preparing this package.
