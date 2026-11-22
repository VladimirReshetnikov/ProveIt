# Three Riemann hypotheses in intuitionistic primitive recursive arithmetic

Read **report.pdf**. The first page gives the single-cutoff prime criterion for Dirichlet GRH. The second page maps the new results to their proofs. The family conventions are ordinary RH, GRH for all primitive Dirichlet characters, and ERH for the Dedekind zeta functions of all number fields.

## New results and entry points

| Modules | What to check |
| --- | --- |
| `SplitPrimes.lean` | The three single-cutoff sentences with the same numerical bound. A single residue class covers Dirichlet GRH. The ERH matrix selects completely split primes and introduces polynomial presentations as the cutoff grows. The module checks readings of the compiled tests, unary vs. all-moduli GRH, and a degree-one specialization, and the split predicate down to coefficient convolution and a bounded quotient-word search. |
| `TaylorPackets.lean` | Three schedules of disks for each family. `statement_reading` interprets the fixed PR matrices as integer numerator/denominator comparisons. The precision bound, analytic continuation and overlap calculation are in the report. |
| `PowerDivisorSyntax.lean`, `PowerDivisorBounds.lean`, `PowerDivisorInversion.lean`, `LiouvilleCriterion.lean` | Perfect-power convolution, finite Möbius inversion, uniform-in-power arithmetic witness conversion, and an equivalence for the actual Mathlib Möbius and Liouville sums. The report gives the passage through reduced residue classes. |
| `CubeTests.lean`, `UniversalCriteria.lean` | A generic internal theorem for a universal block, synchronized over every coordinate. Positive counterexamples and the least global failing radius have internal proof terms. |
| `SymmetricPrefixes.lean`, `CoefficientTest.lean`, `ProductCertificate.lean` | High moments, exponential sums, coefficients and signs of a split polynomial, and an internal derivation for a prefix product equal to one. |

The default entry point is **RiemannIPRA.lean**. All submitted local modules are included in the Lake build. The original `Hypotheses`, `Hierarchy`, `DiscreteSyntax`, `ObjectForms`, `SlackForms` and `SparseEvents` modules and the determinant, Farey, energy, series, progression and Lagarias criteria remain available. The new eight-argument interpretations reuse the generic family closure of `DiscreteSyntax`. Two helpers in that module are now public.

## Reproduction

Use the Lean toolchain identified by `lean-toolchain` (4.32.0) and the checked-in Mathlib manifest. From the archive’s project directory:

```sh
lake exe cache get Mathlib.Data.Fin.Tuple.Basic Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.LinearAlgebra.Matrix.Block Mathlib.Data.Rat.Cast.Order Mathlib.Algebra.Order.BigOperators.Ring.Finset Mathlib.Tactic.Linarith Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.NormNum Mathlib.NumberTheory.ArithmeticFunction.Moebius Mathlib.NumberTheory.ArithmeticFunction.Liouville
lake build
lake env lean verification/Audit.lean
python3 check_packets.py
python3 check_equivalences.py
python3 check_power_divisors.py
python3 check_new_criteria.py
latexmk -pdf report.tex
```

The cache step accelerates a first build. Dependency retrieval needs network access unless the packages are already present. The four numerical checkers require only the Python standard library (3.9+). The PDF figure is bundled. Regenerate it optionally with `python3 figures/disk_cover.py` using matplotlib and NumPy. With a standard LaTeX installation, repeated `pdflatex report.tex` runs also build the report.

## What the formal statements prove

* An object derivation has type `Prf PRAAx [] (Fm.iff A B)`. Its rules are those of first-order intuitionistic arithmetic with quantifier-free induction.
* A `naturalTerms.Holds` theorem interprets closed syntax in the standard natural numbers. A Mathlib theorem about the growth of integer sums is a separate Lean judgment. The kernel-axiom audit is in `verification/lean-audit.txt`.
* The paper proves the links to complex zeros using analytic number theory. These include the explicit prime ideal theorem, noncancellation in cyclotomic products, the Taylor-radius argument, and Aramata–Brauer for Galois descent. The paper identifies finite bridges whose translation to object derivations is still open.

The numerical receipts in `verification/examples.txt` check finite identities and sample cases. In particular they give the exact maximizers at three Dirichlet cutoffs and 9,100 forward/inverse comparisons in reduced residue classes.

## Provenance

This project extends the two supplied archives, **riemann_hypotheses_ipra.zip** and **riemann_ipra_equivalences.zip**. Four files in `ConciseIPRA/` match the blobs returned by the ProveIt repository on its main branch on November 20, 2026. The original pinned ProveIt snapshot is [ce0e3ceaf41a](https://github.com/VladimirReshetnikov/ProveIt/tree/ce0e3ceaf41a83e653857e5f60e0460733cc230c/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA). See **UPSTREAM_LICENSE**.

| ProveIt source | Git blob SHA |
| --- | --- |
| Syntax | a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348 |
| Deduction | 0969040f77fdd3ed9526e360e7a998584b4d9d8c |
| PR | 3251631592070d9ed3687cc0bf7dbd5eb452e46f |
| Semantics | c39a700459dd7d7c5d54d3810c13af7d4b23d0e1 |

Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997`. No additional axioms asserting RH, GRH or ERH are introduced.
