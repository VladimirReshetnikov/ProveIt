# Claim status and audit boundary

This file distinguishes the mathematical content from the evidence used
to verify its implementation. All source references use commit
`09812e81e578c3f13f54b2d0c46a95a0e0665b19`.

| Claim | Status | Proof or artifact |
|---|---|---|
| Five Gaussian imaginary double rows at weight 6 | Proved; original coefficients unchanged | Depth-two inversion theorem; exact differential certificate; `sections/parity.tex` |
| Seven Gaussian imaginary double rows at weight 8 | Proved extensions of the displayed table | General finite Bernoulli coefficient formula |
| General even-weight Gaussian imaginary reduction | Proved specialization of known parity | `thm:gaussian-inversion`, `cor:gaussian-coefficient-rule` |
| Three Gaussian imaginary triple rows at weight 4 | Proved; original coefficients unchanged | Logarithmic moment, classical complementary-argument formula, lower half-point values |
| Every position of one 2 among 1s | Proved at the function level on the stated branch domain | `one2:thm:closed` |
| Top two possible series-depth layers | Proved corollary | `one2:cor:toplayers` |
| At most one imaginary direction modulo stated lower-weight products | Proved upper bound; not an independence assertion | `one2:cor:primitive` |
| Sixth-root closure and pure-parity component | Proved corollary, including an explicit rational coefficient formula | Sixth-root subsection and its independent script |
| Four proposed mixed Gaussian/Eisenstein directions | All reduce exactly | Inverse-color parity theorem and four explicit rows |
| Mixed diagonal antisymmetry always vanishes | False as stated | Positive exact counterexample in `sections/corrections.tex` |
| `Li_{3,3}(i,i)` software-vocabulary description | Replaced by the exact homogeneous weight-6 formula | Stuffle and known single values |
| Shifted-polygamma known component | The source commentary reverses the stated parity | All-order differentiated reflection identity |
| Every real single value is a rational zeta multiple at order 1 | Requires an exception | Explicit logarithms for the Gaussian and Eisenstein values |
| Exact rational Hölder enclosure | Proved, with explicit tail and arithmetic/bit-complexity bounds | `thm:certificate`; exact producer and independent replay |
| Same enclosure over a fixed imaginary quadratic field | Proved corollary | `cor:quadratic-certificate`; core implementation remains Gaussian |
| Small quadrature residuals | Independent numerical cross-checks | Recorded mpmath outputs; not rigorous quadrature certificates |
| 58 residual intervals containing zero | Rigorous numerical compatibility checks | Exact rational enclosures; equality follows from the separate analytic proofs |
| Strictly positive mixed antisymmetry interval | Rigorous nonvanishing certificate | `results/verification_summary.json` |
| Numerical dimensions of remaining source spaces | Not established here | Requires an independent theorem or appropriately stated period conjecture |
| Exact ranks of absent historical relation systems | Not reconstructed or certified here | Proposed as a concrete follow-up task |
| Priority for general parity, Hölder convolution, or classical height-one reducibility | Not claimed | Prior literature is cited in the article |

The source audit is focused on the displayed conjectures and their
surrounding depth/dimension statements, together with the identified
Chapter 6 parity comment. It is not an exhaustive certification of the
whole manuscript. Earlier related work, including the mixed-root
reductions, is treated as corroborated context rather than rediscovered
novelty.
