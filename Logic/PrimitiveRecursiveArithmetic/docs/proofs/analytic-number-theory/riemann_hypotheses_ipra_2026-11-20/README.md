# Three Riemann hypotheses in iPRA

Read **report.pdf** for the statements and the classical equivalence proofs. The primary Lean entry point is **RiemannIPRA.lean**. The three statements in **Hypotheses.lean** have type `LeanProofs.ConciseIPRA.Fm LeanProofs.ConciseIPRA.PTm 0`. They are closed sentences of the ordinary first-order iPRA in ProveIt.

| Declaration | Numerical family | Standard mathematical interpretation |
| --- | --- | --- |
| `RiemannIPRA.RH` | One linear polynomial, all cutoffs | Riemann zeta |
| `RiemannIPRA.GRH` | All polynomials X^m − 1, all cutoffs | All primitive Dirichlet L-functions |
| `RiemannIPRA.ERH` | All monic integer polynomials of positive degree, all cutoffs | All number fields and their Dedekind zeta functions |

The report derives the correspondence to critical-strip zeros in both directions. Its use of classical prime ideal estimates, functional equations and meromorphic continuation is external to the Lean development. Finite-field correctness for arbitrary polynomials is a human proof in section 2. The conjectures are defined as formulas.

## Run

Use the Lean toolchain specified in `lean-toolchain`. Network access is needed for the first dependency fetch. From this directory, run

```sh
lake exe cache get Mathlib.Data.Fin.Tuple.Basic
lake build
python3 check_packets.py
latexmk -pdf report.tex
```

The cache command accelerates the initial Mathlib build. The default Lake target checks the object-language derivations, standard-model theorems, six computations on actual PR trees, and supplementary Mertens modules. The Python program requires Python 3.9 or later and uses only the standard library. For an individual test use `python3 check_packets.py d H u v n`. Its degree d must be positive and its cutoff n at least 100. The internal parameters are d − 1 and n − 100. For example, `python3 check_packets.py 5 0 0 1 256` tests X^5 − 1 and yields B(256) = 732, B(512) = 1436. The TeX source uses the two companion files `dirichlet.tex` and `erh.tex`.

## Lean files

| Files | Contents |
| --- | --- |
| `PacketLanguage.lean`, `CompilerSemantics.lean`, `ArithmeticReading.lean` | Checked scoped language for bounded numerical operations, compilation into actual ProveIt PR symbols and standard-number evaluation theorems |
| `PolynomialCode.lean`, `Hypotheses.lean` | Fixed primitive-recursive factor searches, integer prime product, dyadic inequality and the three closed sentences |
| `Hierarchy.lean`, `RHCounterexamples.lean`, `RiemannIPRA.lean` | Internal implications by specialization and internal equivalence to absence of a finite failing tuple |
| `StandardReading.lean` | Model of ProveIt's term syntax on the naturals, soundness, and interpretations of the literal three formulas |
| `SmokePR.lean` | Vector interpreter with equivalence proof and six concrete checks |
| `DirichletData.lean`, `ERHData.lean`, `MertensForms.lean` | Supplementary executable sums, with witness formulations as Lean propositions over natural numbers |
| `check_packets.py` | Independent exact finite-field gcd implementation with examples and cross-checks |

The primary statements encode fields using four natural polynomial parameters. The Mertens appendix uses a different single-natural polynomial encoding, specified in Appendix C. Programs consuming one encoding should use the indicated decoder.

## Provenance

The unmodified files in `ConciseIPRA/` come from [ProveIt at ce0e3ceaf41a83e653857e5f60e0460733cc230c](https://github.com/VladimirReshetnikov/ProveIt/tree/ce0e3ceaf41a83e653857e5f60e0460733cc230c/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA). Their upstream license is in `UPSTREAM_LICENSE`. The local Lake configuration lists just the modules needed for this project. The manifest pins Mathlib to `81a5d257c8e410db227a6665ed08f64fea08e997` and retains the transitive dependency revisions.

| ProveIt module | Verified upstream Git blob |
| --- | --- |
| Syntax | `a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348` |
| Deduction | `0969040f77fdd3ed9526e360e7a998584b4d9d8c` |
| PR | `3251631592070d9ed3687cc0bf7dbd5eb452e46f` |
| Semantics | `c39a700459dd7d7c5d54d3810c13af7d4b23d0e1` |
