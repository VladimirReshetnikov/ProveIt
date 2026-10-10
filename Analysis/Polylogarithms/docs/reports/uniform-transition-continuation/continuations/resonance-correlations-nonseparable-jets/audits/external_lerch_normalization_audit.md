# One verified external normalization typo

**Scope:** A targeted check of the proposed Lerch/polylogarithm equality,
not an audit of the rest of the external paper.

## Published source and exact locator

Roger Gay and Ahmed Sebbar, *Pseudo-differential operators on the circle,
Bernoulli polynomials*, Quantum Studies: Mathematics and Foundations 11
(2024), 1–25, DOI: 10.1007/s40509-024-00316-9.

Official published PDF:
https://link.springer.com/content/pdf/10.1007/s40509-024-00316-9.pdf

**Printed page 4, Section 1, unnumbered display immediately after Equation
(1) and before Equation (2).** It identifies `Li_s(z)` with `Phi(z,s,1)`
without the required factor z. Equation (1) immediately above uses the
standard zero-based series for Phi. The PDF was visually checked on its
fourth page (zero-based page index 3), so this is not merely an HTML
transcription issue.

## Minimal correction and proof

Replace the first equality in the unnumbered display by

    Li_s(z) = z Phi(z,s,1).

Indeed, for |z|<1,

    z Phi(z,s,1)
      = sum_{n>=0} z^(n+1)/(n+1)^s
      = sum_{m>=1} z^m/m^s
      = Li_s(z).

This then extends by analytic continuation on compatible branches. At z=0,
Phi(0,s,1)=1 while Li_s(0)=0, which immediately detects the missing factor.

## Repository comparison

At pinned commit `570b0567f311cf1890865065896be2665f469e4f`, the canonical
manuscript already uses the correct convention:

* `chapters/09-zero-geometry.tex`, equation label `zeros:eq:lambda`, lines
  25–31, defines `Phi(rho,s,a)=sum_{m>=0} rho^m/(a+m)^s`.
* The unnumbered specialization immediately after `zeros:eq:Dfamily`, lines
  40–43, includes the correct factor `1/rho`:

      ell_n(rho,1)=(-1)^n/rho * [partial_s^n Li_s(rho)]_{s=1}.

Thus this item belongs in an **external-source correction note**. No change
to the inspected canonical manuscript is indicated. The present article's
definition `F(s,t,a)=exp(-at) Phi(exp(-t),s,a)` likewise correctly gives
`F(s,t,1)=Li_s(exp(-t))`.

