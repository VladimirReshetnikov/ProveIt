# Arithmetic criteria for three Riemann hypotheses

Start with **report.pdf**. Section 1 defines the primary sentences, including the primitive recursive integer that each one tests. Section 2 proves that one polynomial at each cutoff suffices for a single-variable universal test for each hypothesis. Sections 3–7 develop other criteria and their proofs. Section 8 records the status of the formalizations and includes the source-level analytic statements.

We use **RH** for the Riemann zeta function, **Dirichlet GRH** for every primitive Dirichlet character, and **Dedekind ERH** for every number field. The files formalize propositions and their relationships. The zero theorems on which their standard interpretations depend are identified in the paper.

## Where to look

| Mathematical question | Lean entry points |
| --- | --- |
| What are the three closed iPRA sentences? How does specialization work? | `Hypotheses.lean`, `Hierarchy.lean`, `StandardReading.lean` |
| How can a single signed sample at each cutoff represent an entire family? | `OneSided.lean`, `GridInterpolation.lean`; see `split`, `rotating_reading`, `compiled_log_grid`, and `selectedData_return` |
| Can one real Taylor center, one sign, and one prescribed precision suffice? | `CayleyPackets.lean`; see `statement_reading`, `translation_step`, `finite_propagation` |
| How are finite Taylor polynomials tested by convolution, quadratic forms and determinants? | `HardyToeplitz.lean`; see `statement_check`, `contraction_iff_block`, `leadingStatement` |
| How are Robin’s and Nicolas’s inequalities stated using rational comparisons? | `RobinNicolas.lean`; see `strict_rational_reading`, `weak_rational_reading`, `scaled_rational_reading`, `strict_iff_first` |
| How is discrete Nyman–Beurling approximation converted into an integer test? | `ResidueSpace.lean`, `ResidueGram.lean`; see `closed_fixed_iff_prefix`, `eliminate` |
| Which changes of a terminal zero test have derivations inside iPRA? | `CountdownTests.lean`, `PrecisionBounds.lean`; see `CountdownTests.equivalence`, `PrecisionBounds.bounded_iff` |
| How does a functional equation exchanging characters reduce the zero-line statement to either half of the strip? | `StripReflection.lean`; see `fromFunctionalEquation`, `line_iff_right`, `line_iff_left` |

**background/report.pdf** is the full cumulative report supplied with the prime-criteria archive. Its TeX sources and figure are beside it. Its splitting-prime, perfect-power, Mertens, Liouville, determinant, Farey, Lagarias and Taylor criteria remain in the Lean project. **RiemannIPRA.lean** imports all the developments into one environment.

## Proof status

- A declaration of type `Prf PRAAx [] (Fm.iff A B)` is a derivation of a biconditional in the stipulated first-order intuitionistic calculus. The project contains actual proof terms, including the implications ERH → GRH → RH.
- A theorem about `naturalTerms.Holds` identifies the standard-natural-number meaning of an object formula. Further Lean theorems certify finite algebra, number-theoretic identities, witness conversions and abstract zero reflection.
- The report proves the links to complex zeros in ordinary mathematics. These use analytic continuation, explicit prime ideal estimates, Landau’s positivity argument, and for some ordinary-RH criteria published oscillation and density theorems. The full analytic equivalences are not kernel-verified. The illustrative concrete Mathlib listing in section 8 is explicitly source-level. The abstract reflection module is compiled.
- Section 8 gives a criterion-by-criterion proof-status table. The two papers give bibliographic links alongside the analytic results they use.

## Reproduction

Use the toolchain in `lean-toolchain` (Lean 4.32.0) and the bundled Lake manifest. From the directory containing this README, on a system with Lean/Lake and Python 3.10 or newer:

```sh
lake exe cache get
lake build
lake env lean verification/Audit.lean
for test in check_*.py; do python3 "$test" || exit 1; done
```

The first command downloads Mathlib’s release cache and can be skipped with a suitable pre-existing dependency cache. The Python scripts use the standard library. The build result, the representative theorem-type and axiom audit, and all ten check-script outputs are in **verification/**. The examples use exact integers and rational numbers. They exercise finite inputs.

To reproduce either PDF with a standard TeX Live installation:

```sh
latexmk -pdf report.tex
(cd background && latexmk -pdf report.tex)
```

## Sources and versions

The three supplied archives were compared. They form a cumulative series, and the prime-criteria archive supplied the baseline project and companion report. The main report and the additional Lean and Python files above extend that baseline. The four foundational source files were compared to [ProveIt’s ConciseIPRA sources](https://github.com/VladimirReshetnikov/ProveIt/tree/ce0e3ceaf41a83e653857e5f60e0460733cc230c/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA). The library’s license is included as **UPSTREAM_LICENSE**.

| File in ConciseIPRA/ | Git blob SHA |
| --- | --- |
| Syntax.lean | a3c8ec9700382e34df9ffdeaa2f2066bbfaf1348 |
| Deduction.lean | 0969040f77fdd3ed9526e360e7a998584b4d9d8c |
| PR.lean | 3251631592070d9ed3687cc0bf7dbd5eb452e46f |
| Semantics.lean | c39a700459dd7d7c5d54d3810c13af7d4b23d0e1 |

Pinned Mathlib revision: `81a5d257c8e410db227a6665ed08f64fea08e997`.
