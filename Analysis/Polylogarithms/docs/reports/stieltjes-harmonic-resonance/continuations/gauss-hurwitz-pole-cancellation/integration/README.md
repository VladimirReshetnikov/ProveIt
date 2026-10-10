# Suggested ProveIt integration

No repository file has been changed by this package.

## Suggested placement

Place the complete package under a new report directory such as
`Analysis/Polylogarithms/docs/reports/gauss-hurwitz-resonances/`.
Review the paper before integrating statements into the canonical manuscript.

The main mathematical dependency order is:

1. Gamma/Stirling and Hurwitz notation.
2. Coefficient recursion, normal convergence, and the Gauss–Hurwitz identity.
3. Reference and numerator-parameter differential laws.
4. The all-resonance value and all-order jet formulas.
5. Harmonic families, primitive telescope, and polylogarithmic endpoints.

The existing canonical Hurwitz/Stieltjes integration chapter is the natural location for the main bridge, with cross-references from the harmonic and polylogarithm chapters. The section sources are modular. `gauss-hurwitz-summary.tex` is a short manuscript-facing entry point; it is not a replacement for the full proofs.

## Notation to preserve

- `r_n(u)` includes the full gamma normalization.
- `A_j(u;c)` depends on the reference shift; it is not Bühring's `A_k^(p)`.
- `zeta^[q]` denotes an order derivative; ordinary parentheses on polygamma denote argument derivatives.
- `S_(N,m)^(K)` is a Taylor coefficient, not an m-th derivative.
- Reciprocal-Gamma zeros require the entire Taylor factorization.
- The reference shift is part of the definition of each subtracted sum.

Prefix equation/theorem labels (for example `gh:`) when moving the section sources into a larger manuscript, and reconcile local macro names with the canonical preamble.

## Optional editorial patch

`pslq-wording.patch` replaces the overly strong claim that supplied PSLQ atoms must be rationally independent. It is based on lines 35–55 of the exact inspected file:

- Commit: `e0d9463bdee9685dfb1dddb819059cc738540c57`
- Path: `Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex`
- Blob: `52c8487a618429fb8a0cd3978705614b9a193505`

From the repository root, review and check before applying:

```sh
git apply --check path/to/pslq-wording.patch
git apply path/to/pslq-wording.patch
```

The patch was checked against the complete inspected excerpt in an isolated fixture. It has not been checked against or applied to a full current repository checkout. If upstream already changed the wording, do not apply a redundant patch.

## Status boundaries

Do not promote S6 or S8, call regression tests a proof-assistant formalization, describe asymptotic-tail residuals as certified enclosures, or treat finite algebraic closure as numerical/algebraic independence. Keep the historical attribution paragraph accompanying the constant-term evaluation.
