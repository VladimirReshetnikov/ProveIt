# Theorem and claim ledger

Statuses distinguish human mathematics, executable finite tests, and literal
object-iPRA formalization. “Lean outline” never means kernel checked.

| ID | Result | Human argument | Lean / executable status |
|---|---|---|---|
| FQ1 | Finite-query package theorem: a bounded reflected verifier, producer, and extractor yield an explicit selected-certificate theorem. | Complete, Paper Theorem 5.3. | `FQNF/Query.lean` target; depends on FQ4. |
| FQ2 | Uniform-base single-code normalization for bounded arrays, including code bound and digit recovery. | Complete, Theorem 6.2. | `FQNF/Digits.lean` exact definitions and milestones; not formalized. Python exhaustive tests pass. |
| FQ3 | Mixed-radix master-certificate normalization. | Complete, Theorem 6.5. | Lean target in `Digits.lean`; Python exhaustive tests pass. |
| FQ4 | Least accepted certificate from an explicit or existential bounded witness. | Complete, Theorems 7.2 and 7.3; direct reduction to repository `Search.search_found`. | `CertificateSearch.lean` target; Python tests pass. |
| FQ5 | Whole-path certificate theorem: finite future-dependent relational choice reduces to one bounded search. | Complete, Theorem 8.1. | `PathCode.lean` outline; worked Python example proves greedy failure and whole-code success. |
| FQ6 | Stepwise least-successor trace theorem under local seriality. | Complete, Proposition 8.4, by `primitiveRecursionAt`. | Exact integration plan; existing object recursion transformer is reused. |
| FQ7 | Fixed proof graph flattening into one master certificate and one QF checker. | Complete, Theorem 9.2. | Lean follows FQ3 plus Boolean folds; no implementation claim. |
| FQ8 | Logical proof-graph composition by simultaneous cut. | Complete, Proposition 9.4. | `KernelCore.compileLocal` and `compileAndExtend`, no placeholders; uncompiled in artifact runtime. |
| FQ9 | QF loop with arbitrary terminal extraction. | Complete, Proposition 10.1. | `KernelCore.invariantAt` and `loopProduces`, no placeholders; uncompiled here. |
| FQ10 | Independent-certificate stable observable. | Complete, Proposition 11.2. | `KernelCore.stableOfIndependent`; same proof pattern is already reported compiled upstream. |
| FQ11 | Exact discrete recovery requires an explicit separation/gap premise. | Complete, Theorem 11.5. | Structural adapter in `KernelCore.exactFromGap`; domain gap arithmetic remains specific. |
| FQ12 | Height-bound / complete-list equivalence for decidable bounded codes. | Complete, Theorem 13.1. | Reference enumeration and tests included; object implementation uses FQ4 and bounded folds. |
| FQ13 | Finite-consumer demand closure needs only the finite query, not a global Cauchy modulus. | Complete, Theorem 12.3. | Exact Python reference for fixed pipelines; Lean is a fixed PR recursion target. |
| FQ14 | Fixed-program specialization avoids a total universal PR evaluator. | Complete metatheoretic argument, Section 14. | Architectural restriction, not a new object theorem. |
| EX1 | Exact rational bisection for `y^3+y=x` with explicit fuel and trace verifier. | Complete worked example, Section 17. | Exact `Fraction` producer/verifier; 12-step example JSON; no object derivation claimed. |
| EX2 | Finite relational path where greedy least choice fails but whole-code selection succeeds. | Complete worked example, Section 8. | Exact JSON and regression test. |

## Explicitly unfinished work

1. Elaborate `KernelCore.lean` in the current ProveIt checkout.
2. Prove the digit and mixed-radix lemmas in `Prf PRAAx`.
3. Complete Boolean checker reflection and bounded-fold constructors.
4. Instantiate `Search.search_found` as `select_of_witness` and discharge the
   existential witness by `Prf.exE`.
5. Move or reprove the checked object recursion and observation glue under the
   `IPRADerivations` library.
6. Instantiate domain adapters theorem by theorem.
7. Supply deep producer data where mathematics genuinely requires it: height
   bounds, analytic constants, covering representatives, compactness moduli,
   separation gaps, or other theorem-specific inputs.
