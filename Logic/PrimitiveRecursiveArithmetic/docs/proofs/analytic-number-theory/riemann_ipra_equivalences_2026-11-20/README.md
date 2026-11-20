# Three Riemann hypotheses in intuitionistic primitive recursive arithmetic

Read **report.pdf**. Page 2 maps criteria to families and proof levels. The default Lean entry point is **RiemannIPRA.lean**. The meanings used here are ordinary RH, Dirichlet GRH for all primitive characters, and Dedekind ERH for all number fields.

## Build and reproduce

Use the Lean version in `lean-toolchain` (4.32.0) and the checked-in Lake manifest. The first dependency download needs internet access. From this directory:

```sh
lake exe cache get Mathlib.Data.Fin.Tuple.Basic Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.LinearAlgebra.Matrix.Block Mathlib.Data.Rat.Cast.Order Mathlib.Algebra.Order.BigOperators.Ring.Finset Mathlib.Tactic.Linarith Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.NormNum
lake build
lake env lean verification/Audit.lean
python3 check_packets.py
python3 check_equivalences.py
latexmk -pdf report.tex
```

The cache command accelerates compilation. The Python programs need only the standard library (Python 3.9+). A PDF can also be built by running `pdflatex report.tex` twice. The .tex files in this directory are the source for the included report. Local Lean test evaluations intentionally use small inputs; the PR encodings were chosen to make their finite bounds transparent.

## Formalization map

| Module | Contents |
| --- | --- |
| Hypotheses, Hierarchy, RHCounterexamples | Original closed Π₁ sentences, internal hierarchy and absence of a failed tuple |
| ObjectForms | Internal proof families for failure counts, first failure, eventual and cofinal cleanliness, every fixed PR sampling offset, and a function extracting the first failure from a supplied failing input |
| SlackForms | Internal equivalences for exact arithmetic slack and its certificates at each cutoff |
| DiscreteForms, DiscreteSyntax | 3 families × 6 readings. All 18 object formulas and their equivalence under the standard interpretation |
| SparseEvents | Standard-model equivalence for testing the initial cutoff and the actual prime-power breakpoints; verified against the compiled prime product |
| PrimeForms | Prime-only and prime-power data, cyclotomic gcd and congruence sums, arbitrary dilation and summation order, uniform and witness bounds |
| DivisorMatrices, MatrixIdentity | Four object determinant criteria and a checked mathematical identity for the ordinary integer determinant with a replaced column |
| MertensSyntax | Four direct Mertens witness sentences in object syntax, including the polynomial reciprocal coefficients |
| FareyEnergy, EnergyInequality | Integralized gcd energies, weighted recovery and Jordan-totient estimates |
| DyadicSeries, AbelIdentity | Bounded and effectively Cauchy weighted reciprocal series; finite Abel estimate |
| FareyRH | Franel and Landau rank-discrepancy statements, ordinary and with reduced progression denominators |
| Lagarias | Non-strict upper and positive strict lower divisor-sum formulations, using only integers |
| PacketLanguage, CompilerSemantics, ArithmeticReading, PolynomialCode, StandardReading | ProveIt PR compiler and numeral semantics, finite polynomial factor searches, and interpretation of the original formulas |
| MertensForms, DirichletData, ERHData | Earlier executable natural-number Mertens readings and field/character computations |
| SmokePR, ExtraChecks | Small evaluations on the actual syntax trees |

The formulas in **MertensSyntax** use the same four polynomial parameters as the primary prime-product formulas: degree offset, coefficient base offset, and two words. **ERHData** uses the earlier single-number code explained in Appendix C. The proofs identify the two at corresponding polynomials; numerical codes should be decoded according to their own convention.

## Proof scope

A proof of type `Prf PRAAx [] (Fm.iff A B)` is an internal biconditional in iPRA. A theorem using `naturalTerms.Holds` is a proof in Lean about the standard interpretation. The determinant identity and rational inequalities have ordinary mathematical Lean types. The Mellin transforms, prime-ideal estimates, connections with the classical complex zeros, and several finite witness transformations are proved or cited in the report. The report specifies the remaining links to the deep embedding. No conjecture is introduced as a Lean axiom.

## Provenance

The project extends the supplied archive. Four files in **ConciseIPRA/** are unchanged ProveIt sources, checked against GitHub's main-branch blob identifiers during this build. The original pinned snapshot is [ce0e3ceaf41a](https://github.com/VladimirReshetnikov/ProveIt/tree/ce0e3ceaf41a83e653857e5f60e0460733cc230c/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA). See **UPSTREAM_LICENSE**.

| Source | Git blob |
| --- | --- |
| Syntax | a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348 |
| Deduction | 0969040f77fdd3ed9526e360e7a998584b4d9d8c |
| PR | 3251631592070d9ed3687cc0bf7dbd5eb452e46f |
| Semantics | c39a700459dd7d7c5d54d3810c13af7d4b23d0e1 |

Mathlib is pinned to revision 81a5d257c8e410db227a6665ed08f64fea08e997. The audit transcript and numerical receipts are in **verification/**.
