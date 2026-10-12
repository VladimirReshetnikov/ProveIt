# Correction and reuse register

## Confirmed external source correction: equation (52)

Source: D. H. Bailey, J. M. Borwein, R. E. Crandall, *Computation and theory of extended Mordell–Tornheim–Witten sums*, author-hosted 29-page PDF at `https://carmamaths.org/jon/MTW1.pdf`. Printed pages 12–13 (PDF indices 11–12) were visually inspected.

Equation (49) defines its resonant coefficient with a minus sign before the Gamma-series coefficient. Equation (52) has a plus sign at the corresponding location despite being obtained by differentiation. The consistent replacement in (52) is

```text
((-1)^m gamma_m + m! b_{k,m+1}(L))
    ->
((-1)^m gamma_m - m! b_{k,m+1}(L)).
```

Here `m` and `k` are the source's variables, not the article's m and r. The article avoids this ambiguity by renaming the source coefficient `q_{m,j}`.

At integer order 2, derivative order 1, and argument exp(-1), the printed expression minus the actual derivative is exactly

```text
-((EulerGamma-1)^2 + zeta(2) + 1),
```

which is nonzero. The proof is Proposition 9.1 and Corollary 9.2; numerical values are in `data/source_sign_audit.json`. No claim is made about every published edition, effects on unrelated theorems, or priority in noticing the defect.

## Precautions established by this report (not claimed defects in ProveIt)

- Differentiate the root-of-unity Fourier prefactor as well as the polylogarithms when taking order jets.
- Include the Gamma normalizer and the stated lower Taylor and Stieltjes counterterms. An unnormalized jet has a whole logarithmic polynomial, not just its highest monomial.
- Use `W_{-1}` for the small positive logarithmic core. `W_0` is the other local regime.
- Dilation filtering decreases the guaranteed common analytic disc. The original radius cannot simply be retained.
- The monodromy index for actual germs differs from the index modulo holomorphic germs.
- The finite inverse coefficient pole is an auxiliary rational-function fact, not a global inverse-singularity theorem.
- A convergent tail plus logarithmic monodromy does not establish a divergent resurgent expansion or a Stokes phenomenon.
- The bounded-resonance theorem is uniform for bounded epsilon*L, not for all unbounded products.

No new error in a canonical repository theorem was established during the targeted inspection.
