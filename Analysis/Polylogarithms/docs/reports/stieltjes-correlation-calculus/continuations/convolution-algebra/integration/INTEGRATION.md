# Proposed ProveIt integration

## Placement

Suggested thematic report path:

`Analysis/Polylogarithms/docs/reports/stieltjes-convolution/`

Keep this delivery's TEX, PDF, scripts, and recorded outputs together. The intake instructions distinguish placement of delivered reports from later editing of the consolidated manuscript. This package does not apply patches or change remote files.

## Manuscript mapping

| Article material | Suggested manuscript location |
|---|---|
| Fourier normalization and meromorphic periodic Hurwitz family | New short foundational subsection before finite-part identities. |
| Canonical Stieltjes finite parts; Bell normal form; Gamma-quotient product rule; convergent integrals | New identity-focused subsection in or beside `07-integration.tex`. |
| Contact correction; full differentiated-convolution calculus; polygamma collapse | Companion subsection to the master identity in `08-differentiation.tex`. |
| Centered Stieltjes primitives and all log-Gamma convolution powers | After the ordinary antiderivative ladder in `07-integration.tex`. |
| Reflected master identity and shifted correlation | Adjacent to the second-moment material, with the distinction from ordinary cubic moments stated explicitly. |
| Rational-shift conversion | Cross-reference the existing cyclotomic/character-coordinate chapters; do not infer new arithmetic ranks from it. |

## Stable LaTeX labels in the report

`thm:Bell`, `thm:product`, `thm:integral`, `thm:anomaly`, `cor:fulltower`, `thm:polygamma`, `thm:integrated`, `thm:gammapowers`, `thm:reflected`, `cor:correlation`, `prop:cyclotomic`.

When merging into a larger source tree, prefix these labels (for example `stconv:`) to prevent collisions. The standalone article has a complete preamble and bibliography; it should not be directly `\input` into the book without extracting its body and reconciling macros.

## Dependencies that must survive condensation

- Specify `T = R/Z`, Fourier sign, and the logarithm of `2*pi*i*k`.
- Specify `I = delta_0 - 1` as the mean-zero convolution unit.
- Retain the exact finite-part subtraction and the higher-order cutoff constant-term convention.
- Retain the delta-derivative contact terms before taking convolutions.
- State that all stars are circular convolution, not pointwise multiplication.
- Attribute the nonsingular semigroup to Sun, and retain the classical second-moment attribution.
- Retain the warning that polynomial freeness of a distribution algebra is not arithmetic independence of its values.

## Verification integration

The exact product catalog uses `zj` for a formal symbol denoting zeta(j). Its entries are not floating-point conjectures. The only even-zeta relation used in the four printed short rules is explicitly tested. Keep finite exact checks separate from numerical residuals in the consolidated validation ledger.

The 40- and 50-digit runs test 31 cases each. They support the audit but are not proofs or certified numerical enclosures. The report's proofs are ordinary mathematical arguments; no Lean support is included.
