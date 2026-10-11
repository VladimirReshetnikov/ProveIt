# Suggested integration

This directory contains an additive core section, not a patch against a
moving repository revision. Nothing was written to the remote repository.

## Placement

A suitable location is the canonical integration/differentiation material,
after the Gauss–Hurwitz continuation has been integrated. Suggested target:

`Analysis/Polylogarithms/docs/manuscript/chapters/07-centered-dougall-resonance.tex`

The core file has no document class or preamble. It uses standard AMS math,
`proposition` and `proof` environments, and labels prefixed `dr-core:`.
Copy `centered-dougall-resonance.tex` to the target and insert the appropriate
`\input{chapters/07-centered-dougall-resonance}` line. Add the bibliography
items from `bibliography-items.tex` inside the manuscript's existing
`thebibliography` environment, adapting keys only if necessary.

The supplied `core-preview.tex` driver demonstrates the required environment
and has been compiled to `core-preview.pdf`. The standalone article remains
the comprehensive source for the harmonic examples, primitive families,
and detailed audit.

## Review requirements

Preserve the centered coordinate n+kappa and doubled spectral arguments.
Do not replace the subtraction by an unnamed finite part. Keep the
reciprocal-Gamma zero convention next to the all-jet theorem. The generic
Bell formula must not supersede the entire-germ definition at zeros.

Record the result as an analytic proof of the **fixed Rogers–Dougall 5F4
extension** proposed in the Gauss–Hurwitz article. Do not mark the broader
classification problem, S6, revised S8, or any period-independence question
as resolved. Classical summation, harmonic differentiation and zeta
antiderivative results retain their classical attribution.

## Further optional integration

The full article contains the half-integer tower, exact truncation loci,
three explicit Stieltjes/harmonic identities, the continuous-shift harmonic
formula, all first-jet Euler-primitive endpoint values, and all
center-parameter resonance primitives. These can be moved into separate
subsections using the `dr:` equation labels in `article.tex` and the index
in `identities.json`.

The table and Python checks can live with the existing special-function
experiments. Keep the numerical reports labeled as diagnostics, not
proof-assistant certificates or interval enclosures.
