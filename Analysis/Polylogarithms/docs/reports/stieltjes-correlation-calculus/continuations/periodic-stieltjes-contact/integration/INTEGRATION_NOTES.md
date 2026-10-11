# Integration notes

## Suggested destination

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/periodic-contact-calculus/`

Preserve the delivered files and their manifest under the repository intake procedure. Do not merge this package into a previous archive or overwrite the previous article. The self-contained source is `article.tex`; it depends on `data/validation_summary.tex`.

## Research status to update

In the inspected *Coincident-Point Stieltjes Calculus* manuscript, the further-research subsection “The remaining distributional collision law” asks for a fixed periodic extension and an all-index delta-term comparison. Theorem `pc:main` now supplies that comparison under exactly the unit-coordinate convention stated in this delivery. A suitable editorial replacement is:

> Under the unit-coordinate Hadamard convention, the periodic-contact continuation proves that the convolution of the individually extended Stieltjes derivatives differs from the coordinate extension of the off-collision correlation by one explicitly generated delta derivative of total order p+q. The coefficient kernel, harmonic differentiation anomaly, and normalized primitive corrections are given in that continuation. Coordinate-rescaling laws, higher-point collisions, and nonperiodic polynomial weights remain separate questions.

This wording is a proposal, not a patch applied to an unread or changing file.

## Canonical-book placement

The natural location is after the shifted/coincident Stieltjes correlation material in the integration/differentiation chapters. Introduce the distinction among an off-point function, its shift-variable coordinate finite part, and the convolution distribution before quoting any formula. Use the `pc:` labels as a disjoint namespace. If integrating source fragments, reconcile the theorem environments and macros with the book rather than inputting the article preamble.

The main dependencies are:

1. Unit-coordinate finite parts and the periodic Hurwitz Fourier formula.
2. `pc:resonant`, `pc:derivative`, and `pc:fourier`.
3. The recalled off-point kernel, then `pc:main`.
4. `pc:polygamma`, `pc:edge`, `pc:stabilization`.
5. Weighted ordinary integrals and normalized primitives.

The weighted Hurwitz theorem `pc:Hurwitzkernel` also has an independent proof from the classical Fourier formula and can be placed before the distributional development if preferred.

## Essential conventions

- Fourier coefficient is the pairing with exp(-2*pi*i*k*x).
- Correlation is reflected-first-factor convolution: check(T_m,p) * T_n,q.
- The delta derivative has order p+q and changes sign by (-1)^(p+q) under reflection.
- The constant distribution 1 is not delta_0.
- Unit subtraction coordinates are x, x-(1-a), a, and 1-a as appropriate.
- The scalar coincident moments Q_mn^(p,q) are different objects from the shift-distribution contact coefficients Delta_mn^(p,q).
- Negative-order polylogarithms are Abel-limit distributions when used globally on the circle.
- All inverse derivatives have zero Fourier mode fixed to zero.

## Do not change these statuses

This delivery does not resolve the S6 or revised S8 period-reduction candidates, numerical independence of period coordinates, pointwise cubic Stieltjes products, arbitrary nonperiodic polynomial weights, or the general coordinate-transport problem. It does not claim to audit the other incoming archives. Numerical validation is not interval arithmetic, and no result is proof-assistant formalized.
