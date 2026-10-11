# Proposed integration into ProveIt

This is a reviewable research contribution based on commit `5a790187c8e186e41e2b990b4941cb7a1a3c7b6b`. It makes no direct repository edits.

## Section placement

| Package source | Suggested destination | Dependency to preserve |
|---|---|---|
| `sections/02_ordered.tex` | After the incoming Ordered Hurwitz Resonances independent-slope discussion | Common-shift regular germs, raising spectral convention, Taylor-coefficient normalization of rho |
| `sections/03_reflected.tex` | Following coincident Stieltjes/contact calculus and the distinct-seam reflected theorem | Unit endpoint coordinates and complete local resonant amplitude |
| `sections/04_harmonic.tex` | Harmonic polylogarithms / endpoint regularization | Raw powers differ from elementary-symmetric numerators; inner harmonic sum remains unshifted |
| `sections/05_cayley.tex` | After the bounded S6 obstruction and depth-preserving Cayley projector | Full ideal versus the fixed additional finite family |
| `sections/06b_tin_sign.tex` | Literature audit / harmonic Stieltjes identities | Version-1 equation (14) Laurent convention and equation (22) sign |

Labels have distinct prefixes `oq:`, `ct:`, `hp:`, and `gf:`. Merge the associated bibliography keys. The generic `theorem`, `lemma`, `proposition`, and `corollary` environments can inherit canonical numbering. The parent article defines `\shuffle` as `\mathbin{\amalg}` when needed. It uses `mathrsfs` for the named finite relation family.

## Suggested status text

1. **Ordered depth four:** proved spanning normal form for every transverse straight direction, with absolutely convergent coordinates, exact shift laws, and three-ray reconstruction. In the displayed normal form, the additional coordinate coefficients cancel exactly when the last three slopes agree. Arithmetic independence and a classification modulo all possible future relations remain open.
2. **Coincident reflected closure:** proved for every Stieltjes index and every nonnegative argument derivative order, allowing arbitrary finite coincident reflected products. Repeated seams reduce by rational partial fractions. The generic unreflected cubic Tornheim coordinate remains open.
3. **Raw harmonic powers:** all nonpositive Laurent principal coefficients and finite parts have polynomial dependence on the continuous outer shift. Centering at one half removes every nonpositive even pole. The first positive regular spectral coefficient generally requires additional global data.
4. **S6 proof search:** completing all convergent Cayley relations and arbitrary shuffle multiples still does not place the target in the span generated with the inherited 5,131 additional rows. S6 remains conjectural; this is formal nonmembership, not a period inequality. Do not extrapolate the result to S8 or to a universal lower bound on proof depth.
5. **Tin sign correction:** equation (22) of arXiv:2507.03058v1 has the wrong sign on its first harmonic Stieltjes term under that version's own convention. The all-logarithmic identity in the contribution proves the corrected minus sign.

## Normalization details that must survive editing

- Use `zeta(1+u,a) = 1/u + sum (-1)^m gamma_m(a) u^m/m!`.
- In the ordered section, rho is a difference of Taylor coefficients, not the unscaled difference of second derivatives.
- The ordered formula requires every prefix slope to be nonzero, including the total slope.
- The Gamma generating relation is interpreted coefficientwise as a formal series in its depth variable.
- The reflected coordinate finite part uses `x` and `1-x` at the endpoints, and the full `P_p(u)/u` subtraction at odd `p+r`.
- Finite-part integration by parts retains endpoint constant differences. In particular, the integral of `(psi K)'` is `-2 zeta(2)`.
- The harmonic shift derivative contains a simple-pole correction: `C'_{p,m}=m C_{p,m-1}-R_{p,m-1,1}`.
- Generalized harmonic orders in the extension are positive integers. Arbitrary generalized-harmonic products need not inherit the raw-power centered parity cancellation.
- Parse the functional data as exact integers; JavaScript/IEEE-754 conversion of the large integers would corrupt the certificate.

## Files to retain

Retain `certificates/cayley/code/`, `certificates/cayley/data/`, and its provenance as one unit. The verifier reconstructs all relation rows and does not need a cached matrix. Retain the new verification scripts and JSON results alongside the manuscript contribution. Keep the full-run numerical receipts distinct from exact algebraic certificates.

The package supplies complete TeX and a compiled PDF. The root `build.py` regenerates the standalone source from the modular sources, so editorial changes should be made in `sections/` and rebuilt rather than made independently in two copies.
