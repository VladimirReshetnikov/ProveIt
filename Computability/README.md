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
external equivalence between the exact compensated 244-state machine's blank
nonhalting and the stated ZF and ZFC consistency propositions, improving its
earlier routed 245-, 246- and 252-state endpoints. The user's target remains an
equivalence provable inside PA.
The [batch 162 reconciliation](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-162.md)
adds another audit of the identical 247 table and a 246-state candidate with
one further contextual pulse fold. Its nine main checks and two additional
audits pass, including its own complete 410,735-step blank startup. The
ordinary proof and executable evidence did not supply an exact-table Lean
endpoint at that intake checkpoint; the maintained 246 endpoint has since closed. Earlier relative-consistency seed criteria remain in
[batch 161](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-161.md).

The [batch 163 reconciliation](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-163.md)
adds source rewrites, arithmetic contracts, stronger prepared-frame obstructions
and two different alternate 246-state tables. Thirty substantive checks pass;
one additional full symbolic replay times out, leaving that result inherited.
The 201-node result is a source DAG count, and no complete sub-246 machine is
established. The [current project criterion](BusyBeaver/Research/ZFC/README.md)
allows stronger target theories within well-understood, widely accepted
consistency benchmarks, with an explicit upper bound as well as the lower bound
to ZF. These intake findings and the separately checked binary endpoints
do not by themselves discharge the internal PA comparison.

The [batch 165 reconciliation](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-165.md)
adds positive multi-instruction source blocks, numerical invariants and a
whole-frame relation that forgets unused workspace. Its 14 main jobs and eight
supplemental checks pass; scoped discovery results remain inherited. It provides
no smaller calibrated machine or new Lean theorem. Its two rejected 245 tables
are distinct from the maintained routed 245 endpoint.


The [batch 166 reconciliation](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-166.md)
adds a compensated 244-state reduction, with exact
[maintained candidate inputs](BusyBeaver/Research/ZFC/candidate-compensated244/README.md).
Its ordinary all-tape halting proof compares the exact routed 245-state baseline
using seven local transition blocks. The portable and complete 8,391-case
replays pass, covering all 488 rows and the 407,951-step blank startup. At this
intake checkpoint the closed 245-state external Lean endpoint supplies the
baseline; intake does not establish a complete 244-state kernel endpoint or
internal PA comparison. The equational backend has a 2,324-bit packet but no
compiled binary machine; no further state bound is inferred.

Subsequently, on 18 October 2026, the exact
[244-state external Lean endpoint](BusyBeaver/Research/ZFC/compensated244_binary.md)
passed its source and audit checks. It proves blank nonhalting equivalent to
the stated ZF and ZFC consistency propositions. Internal PA calibration remains
open.

The current primary contender is the [218-state machine](BusyBeaver/Research/ZFC/candidate-k218/README.md),
with an ordinary proof formalizable in ZFC that blank nonhalting is equivalent
to Con(ZFC). Fresh checks cover all 6,167 primitive cases and complete 312,909-step
initialization. Its exact-table Lean and internal PA endpoints remain open;
the [240-state PA theorem](BusyBeaver/Research/ZFC/rotation240_binary.md) and
[221-state Lean endpoint](BusyBeaver/Research/ZFC/candidate-k221/README.md)
retain their separate formal status. The active size target is 217 or fewer.
The following paragraphs preserve earlier construction milestones.

The [loop-rotation 244-state candidate](BusyBeaver/Research/ZFC/candidate-rotation244/README.md)
from `d91a27b462` saves a different state. Combining it with the compensated fold
gives a [243-state candidate](BusyBeaver/Research/ZFC/candidate-combined243/README.md).
Its complete replay passes 8,390 cases and 2,314,868 symbolic rules, and its
independently computed blank prefix has 407,967 transitions. Five Lean units
prove exact halting equivalence between the rotated 244 and combined 243 tables
(83 probes, 39 callers, zero warnings). The ordinary proof supports the ZFC
consistency calibration; the rotation's source/runtime connection and the
internal PA proof remain open in Lean. At that stage, compensated244 was the smallest
machine with the complete external Lean consistency endpoint.

The [batch 168 reconciliation](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-168.md)
records the 241-state candidate's ordinary proof and fresh replay: 19 jobs,
including five complete 8,390-case universal runs; primary 241 has 2,319,442
symbolic rules, 482 rows and exact 408,419-step startup. The
[six-report comparison in batch 169](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-169.md)
identifies all six later 242 tables with primary A, up to one state rename,
so their composition gives the existing 241 candidate. A fresh joint
equational packet has **1,750 complete bits**, without supplying a further
binary-state bound or internal PA endpoint. The closed external Lean baseline at that stage was compensated244;
the complete 241 consistency endpoint remained open.

The [source-rotation 240-state candidate](BusyBeaver/Research/ZFC/candidate-rotation240/README.md)
combines a previously proposed source rotation with a fold of inherited state
90 into 72. The [batch 170 reconciliation](../SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/intake-170.md)
records all ten fresh checks passing, including 8,386 complete final runtime
cases, 2,322,575 symbolic rules, all 480 rows and the exact 409,691-step blank
startup. The exact 240-state external Lean and internal PA comparisons
have since been completed, as linked above. The theory countermodel,
GIC/Collection-plus-Separation equivalence and bounded search limits are
preserved separately from the machine claim.

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
attributed literal 254-state baseline and the checked 252-, 246-, routed
245- and compensated 244-state external successors.
The shared-carry 250 construction now has checked local table, pulse, marking,
register-operation, symbolic-execution, per-site and whole-tape frame lemmas.
The exact 246 and routed 245 tables have complete external simulations and
blank startups. Checked positive-block transport from routed 245 establishes
the compensated 244 external endpoint. The displayed local 250 results,
separate 247 candidate, and internally provable PA comparison retain their
stated limits.
The proofs are an opt-in `BusyBeaver.ZFC` surface.
