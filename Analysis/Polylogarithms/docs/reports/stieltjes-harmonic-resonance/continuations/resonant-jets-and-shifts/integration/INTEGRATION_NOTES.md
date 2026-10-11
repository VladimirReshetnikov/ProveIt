# Integration notes

## Baseline and editorial intent

The package targets ProveIt revision `16c7e342d7a4a15f59911f322eb90b7f96c2a8b5` and the five incoming archives at that revision. Preserve their current theorem/conjecture statuses. This is a standalone article intended to be reviewed and then incorporated; no repository mutation is part of the deliverable.

## Suggested placement and dependency order

| Module | Suggested placement | Dependencies |
|---|---|---|
| Discrete Stieltjes products | Nonperiodic Stieltjes identities or an exact summation subsection | Stieltjes shift law; fixed-order Hurwitz Euler–Maclaurin expansion |
| Ordered double-Hurwitz germ and paths | After the incoming equal-direction Laurent theory | Shift conventions and depth-two stuffle; discrete sums `S_{m,n}` for the all-jet formula |
| Fully symmetrized directions | Immediately after the ordered depth-two result | Labelled set partitions and the classical symmetric-sum formula |
| Gamma-zero derivatives | After Nested Harmonic Jets' first zero-flow proposition | The incoming spectral product and its exact counterterm; Bell polynomials |
| Two-shift inverse-colour reflection | Alongside the manuscript's inverse-colour and parity sections | Lerch definition and cotangent partial fractions |
| Polynomial spectral products | A separate spectral-products subsection or appendix | Hurwitz meromorphic continuation, coefficient extraction, standard Barnes normalization |
| Audit and further questions | Research agenda / editorial ledger | The exact scope table in Section 8 |

The article uses self-contained proofs and explicitly repeats necessary conventions, so the sections may initially be retained as a separate research continuation without changing the canonical chapter numbering.

## Most useful theorem entry points

| Label | Content |
|---|---|
| `thm:discrete` | Arbitrary Stieltjes product sum and exact remainder |
| `cor:Stwo` | All-index symmetric Stieltjes sum |
| `thm:doublegerm` | Exact polar germ at `(1,1)` |
| `cor:direction` | Every transverse straight-direction finite part |
| `thm:curved` | Cubic-jet curved finite part |
| `thm:Hcoeff` | Complete regular two-variable Taylor coefficients |
| `thm:symcoeff` | All-depth fully symmetrized Laurent coefficient algorithm |
| `mz:thm:primitive` | Finite Stieltjes-antiderivative coordinate construction |
| `mz:thm:zero` | Every higher spectral derivative at each Gamma zero |
| `mz:thm:coefficients` | Harmonic–Hurwitz coordinate expansions |
| `gap:thm:seed` | Two-shift Lerch reflection seed |
| `gap:thm:all` | Explicit arbitrary-index reflection |
| `gap:cor:diagonal` | Complete complementary-diagonal reduction |
| `sp:thm:germ` | Exact polynomial-spectrum meromorphic germ |
| `sp:thm:polynomial` | Polynomiality in normalized exponents |
| `sp:thm:polarization` | Exact local finite differences |
| `sp:thm:sixterm` | Six-term second-jet Vandermonde identity |
| `sp:thm:alternant` | General alternating identity at order `binom(m,2)-1` |
| `sp:thm:log` | Logarithmic multiplicities and higher-pole Laurent jets |

`theorem_index.json` records the actual compiled numbering and source files. Most moving-zero, shifted-gap, and spectral labels are prefixed; generic section/theorem labels should be namespaced when merged into the collective manuscript to avoid collisions.

## Status changes justified by the proofs

- Nested Harmonic Jets question 7: mark the finite algorithm and a sufficient Stieltjes–zeta coordinate construction as resolved. Retain minimality as open. The source's first derivative is an antecedent, not a new result.
- Question 4: record the exact ordered depth-two answer and the fully symmetrized arbitrary-depth answer, with their transverse-direction/curve hypotheses. Retain ordered higher-depth and algebra-preserving renormalization questions.
- Question 3: record the fully symmetrized independent-direction algorithm. Do not claim a general ordered two-colour finite-product model.
- Keep both the canonical `S6` and current frozen `S8` short evaluations conjectural. The distinct old rejected `S8` candidate must not be conflated with the current one.

## Corrections and safeguards

No new substantive correction to an audited current repository theorem is proposed. Section 8.2 derives one external typographical correction: Gurel, arXiv:2504.14563v2, Theorem 1.1, printed p. 2, has `k` in a sum indexed by `ell`; the denominator is `ell`.

Retain the exact regulator, labelled permutation multiplicities, ordinary-sum grouping, normalized primitive base points, and the distinction between fixed-argument derivatives and moving-zero derivatives. For polynomial spectra, normalized weights sum to one; arbitrary weights require the stated power of their total `W`. For logarithmic multiplicities, the base `b` is part of the spectrum and the jets are Laurent coefficients, generally not ordinary derivatives.

## Attribution

The symmetric-sum mechanism is classical (Hoffman); multivariable Laurent expansions and algebra-compatible renormalizations have established antecedents (Matsumoto–Onozuka–Wakabayashi and Guo–Zhang). The general parity and shifted cyclotomic symmetry principles predate this continuation (Panzer, Rui, Xu). First-derivative multiplicative anomalies are classical in substance (Dowker, Gurel, Mizuno). Retain those citations when moving proofs.

The finite constructive Gamma-zero answer, explicit directional/curved formulas, continuous-argument shifted identity, and all-order spectral cancellation calculus are proved developments relative to the inspected baseline. No claim of exhaustive historical priority or arithmetic independence is made.

## Verification boundary

The analytic proofs establish the identities. The code checks exact finite algebra and floating-point diagnostics with independent analytic representations. The package does not contain proof-assistant formalizations or certified interval enclosures. Do not relabel the numerical reports as certificates.

