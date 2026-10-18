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
[Lean minimization project](BusyBeaver/Research/ZFC/README.md) now checks the
external equivalence between the exact 252-state machine's blank nonhalting
and Con(ZFC). The user's target remains an equivalence provable inside PA.
The [batch 162 reconciliation](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-162.md)
adds another audit of the identical 247 table and a 246-state candidate with
one further contextual pulse fold. Its nine main checks and two additional
audits pass, including its own complete 410,735-step blank startup. The
ordinary proof and executable evidence do not yet supply an exact-table Lean
endpoint. Earlier relative-consistency seed criteria remain in
[batch 161](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-161.md).

The [batch 163 reconciliation](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-163.md)
adds source rewrites, arithmetic contracts, stronger prepared-frame obstructions
and two different alternate 246-state tables. Thirty substantive checks pass;
one additional full symbolic replay times out, leaving that result inherited.
The 201-node result is a source DAG count, and no complete sub-246 machine is
established. The [current project criterion](BusyBeaver/Research/ZFC/README.md)
allows stronger target theories within well-understood, widely accepted
consistency benchmarks, with an explicit upper bound as well as the lower bound
to ZF. These intake findings and the separately checked exact246 proof components
do not by themselves discharge the internal PA comparison.

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

[ZFC machine minimization](BusyBeaver/Research/ZFC/README.md) retains the
attributed literal 254-state baseline and its checked 252-state successor.
The shared-carry 250 construction now has checked local table, pulse, marking,
register-operation, symbolic-execution, per-site and whole-tape frame lemmas.
Complete simulation and startup for the new 250, 247 and 246 tables, and the
internal PA comparison, remain open.
The proofs are an opt-in `BusyBeaver.ZFC` surface.
