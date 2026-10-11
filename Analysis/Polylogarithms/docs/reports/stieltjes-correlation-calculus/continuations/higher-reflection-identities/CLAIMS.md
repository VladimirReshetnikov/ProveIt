# Claim ledger

All analytic statements below are proved in the article. Numerical values and finite symbolic checks are separately documented in `verification/README.md`.

| Result | Location | Status and boundary |
| --- | --- | --- |
| Gamma Fourier coefficients and Euler–polylog transform of the sine weight | Section 2, `beta:transform` | Proved from the beta integral, recurrence, and Hurwitz Fourier expansion. The transform mechanism and several integer/logarithmic specializations are classical. |
| Completed generator for all Stieltjes indices, argument derivatives, and logarithmic powers | Section 2, `beta:completion` | Proved joint holomorphy after removing the entire crossing numerator. Coefficients are the specified unit-coordinate finite parts. |
| Digamma/log-sine-square bridge and cubic cancellation | Section 2, `beta:secondmoment` | Proved. The cube evaluation used to eliminate the harmonic coefficient is inherited from the pinned cubic report. The individual harmonic coefficient is not evaluated in ordinary constants. |
| Necessary and sufficient centered harmonic-polynomial criterion | Section 3, `hc:main` | Proved for every polynomial in finitely many generalized harmonic variables over C. Necessity uses a fully proved formal independence lemma. |
| Algebraic-coefficient strengthening | Section 3, `hc:algebraic` | Proved using the established transcendence of pi, without assumptions on odd zeta values. |
| All centered even moments of a trigamma square | Section 3, `hc:trigamma` | Proved finite Bernoulli formula. The bracketed examples are ordinary convergent series; the raw divergent series are not assigned ordinary sums. |
| Arbitrary-factor geometric subtraction | Section 4, `gc:main` | Proved for unit-frequency periodic digamma factors and paths in a fixed ordering chamber. The fully subtracted remainder extends analytically and has the merged value. |
| Every argument-derivative order in geometric collisions | Section 4, `gc:derivative` | Proved by direct repeated-pole Hermite interpolation. Stieltjes index is zero. No derivation by naively differentiating an extended scalar distribution is used. |
| Hierarchical cubic and equally spaced quartic constants | Section 4, `gc:hierarchy`, `gc:quartic-example` | Exact corollaries and independently checked finite expansions. The fixed-rate triple anomaly is credited to the mixed-spectral report. |
| Complete fourth Tornheim ray derivative | Section 5, `qt:main` | Proved for `(a+c)(b+c) != 0`. Three retained coordinates have convergent representations. This is not a claimed reduction of each coordinate to ordinary constants. |
| Cyclic quartic formula and coordinate-free weighted difference | Section 5, `qt:cyclic`, `qt:short-difference` | Proved exact cancellations. The short difference contains only the displayed ordinary zeta derivatives and log(2*pi). |
| All-order formal residual and cyclic dimensions | Section 5, `qt:all-order-space`, `qt:cyclic-dimension` | Proved for the stated symmetry, divisibility, and Euler boundary conditions. No assertion that these exhaust all global functional equations or period relations. |
| Fifth-order obstruction to diagonal-only cyclic reconstruction | Section 5, `qt:fifth-obstruction` | Proved polynomial counterexample within that formal system. It does not assert arithmetic independence of any evaluated periods. |
| Gaussian S6 and revised S8 | Section 6 and source audit | Remain open. No new proof or refutation is claimed. |

The research questions in Section 6 are proposals, not unstated conjectural equalities promoted to theorems. Proposed integer-frequency and weighted geometric extensions are not included in the current theorem scope.
