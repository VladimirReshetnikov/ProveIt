# Computability

[`TuringDegrees/`](TuringDegrees/) formalizes Turing reducibility and
equivalence for sets of natural numbers, the degree partial order and zero,
the exact even/odd join, cardinality results, the halting degree and c.e.
completeness in Lean, and jump, incomparability, limit, hierarchy, and Post-
problem results in Rocq. Its
[`coverage ledger`](TuringDegrees/COVERAGE.md) records theorem-by-theorem parity
and every explicit logical or effective-enumeration hypothesis.

[`HilbertTenthProblem/`](HilbertTenthProblem/README.md) holds corrected
editions of six articles by J. P. Jones and coauthors (1974–1984) on
Diophantine representation of recursively enumerable sets and universal
Diophantine equations, with per-article editorial notes, and their Lean
formalization (library `Diophantine`): MRDP in both directions, the universal
pair `(58, 4)`, prime-representing polynomials, and the register-machine
proof of the exponential Diophantine representation.

[`CombinatoryLogic/`](CombinatoryLogic/) contains independent Lean and
Rocq/Coq proofs that pure SK, SKI, and the one-combinator Iota calculus
simulate closed weak untyped lambda calculus.  The checked chain includes
scope-safe substitution, occurs-aware bracket abstraction, positive
context-closed simulations, compiler-size bounds, and a faithful injective
operational embedding of Iota back into closed lambda terms.  The exact
Turing-completeness and non-full-abstraction boundaries are explicit.

[`BusyBeaver/`](BusyBeaver/) contains the repository-authored Busy Beaver
machine model, domination theorems, exact small-state score certificates, and
bridges to the vendored time certificates under [`../lib/Coq-BB5/`](../lib/Coq-BB5/).
The external [ZFC closure-kernel report](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/README.md)
compares theories for a smaller ZFC-inconsistency search machine. It now
includes a mathematical PSC-only hereditary-saturation interpretation,
an empty-input equivalent schema, attributed prior 253-state work and separate
compiler experiments. A reviewed finite-sort model rules out the reduced raw
C/G abstract calculus, including the new primitive-Bottom variant; its
248–252-state tables remain compiler benchmarks. Complete Hilbert and
ground-clause, binding-witness and shared-template tableau references restore
general substitution but have no new binary state bound. A separate 268-state
control retains all original logical rows; two delivered standalone Lean files
prove narrow binding/obstruction results, not checker or compiler correctness. The
[Lean minimization project](BusyBeaver/Research/ZFC/README.md) checks subset-PSC
calibration and specific quotient, coding and table lemmas. Its current
target remains an internal ZFC proof of a sub-254 blank-tape halting equivalence.

The score and time functions are distinct measures. The proved values
`Sigma(2)=4`, `Sigma(3)=6`, `Sigma(4)=13` and `BB(2)=6`, `BB(3)=21`,
`BB(4)=107` therefore intentionally differ.

The Lean BB2/BB3 classifications are large opt-in targets. The Lean BB4 TNF
reduction is sound, while its exhaustive root equality remains conditional.

Coarse Turing degrees (coarse equivalence, the failure of the statement C1,
coarse hyperdegrees) are a second Lean library of the Turing-degree project,
[`TuringDegrees/Lean/CoarseDegrees/`](TuringDegrees/Lean/CoarseDegrees/README.md).
Unlike the rest of this topic it admits eight published results with `admit`;
its README lists them.

[ZFC machine minimization](BusyBeaver/Research/ZFC/README.md) adds Lean
closure and codec lemmas, the literal 254-state baseline, and a certified
obstruction to exact state quotients, with executable coding/compiler
experiments. A smaller verified machine and its end-to-end ZFC theorem
remain open. The new proofs are an opt-in `BusyBeaver.ZFC` surface.
