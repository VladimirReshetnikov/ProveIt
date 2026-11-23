# Verification report

## Executed checks

**All checks passed.** The recorded run used Python 3.12.14. The complete machine-readable record, including measured runtime, is
`validation_results.json`; rerun `python3 validate.py` to reproduce it. No
third-party package is needed.

| Check family | Cases |
| --- | ---: |
| All formulas of at most five nodes over bottom and two variables | 516 |
| Canonical DNF/CNF semantic equivalences | 1,032 |
| Substitution semantic equalities | 51,600 |
| Tseitin extension assignments, including uniqueness/projection | 9,258 |
| All CNFs over two variables, checked by resolution and DPLL | 512 |
| Forgetting projection equalities | 2,836 |
| Entailments checked with a common-variable interpolant | 830 |
| IPC saturated proof DAGs and canonical model truth lemmas | 516 |
| IPC sequents with nonempty contexts | 35 |
| Exported IPC proof certificates replayed | 142 |
| Exported rooted IPC countermodels replayed | 409 |
| Constructed CPC proof certificates replayed | 150 |
| Exported Boolean countervaluations replayed | 401 |
| Complete certificate JSON round trips replayed | 1,102 |
| Public witness mode/article regressions | 3 |
| Targeted IPC decisions beyond the exhaustive formula universe | 7 |
| Explicit classical-valid principles refuted by finite Kripke models | 9 |
| Invalid proof / incorrect-mode / incorrect-target rejections | 14 |
| Positive exact-target proof check | 1 |
| Empty Kripke-frame rejection | 1 |
| Source article non-tautology regression | 1 |

These counts describe distinct test families; they should not be added as
though they were disjoint mathematical theorems. A normal-form case checks
all valuations of its finite support. A saturated IPC case replays every
accepted derivation node and checks every world/formula pair in the finite
canonical truth lemma. In the exhaustive five-node family, the maximum
formula universe had 5 elements, the maximum
canonical model had 8 worlds, the maximum complete
saturation scan count was 4, and the maximum proof
DAG contained 144 nodes.

The negative proof cases include self-reference, a forward reference, a
negative reference, a hypothesis absent from its context, deleting a needed
assumption by purported weakening, discharging the wrong antecedent,
combining premises with mismatched contexts, a malformed LEM conclusion,
using LEM in IPC mode, and asking for a target not supplied by the proof.
An empty DAG is a valid empty list of derivations, but it cannot pass an
exact-target proof check.

The article regression evaluates
`p -> ((q or r) -> (r -> not p))` at `p=true,q=false,r=true` and obtains false.
The finite Kripke regressions include excluded middle, double-negation
elimination, Peirce's law, material-implication expansion, weak excluded
middle, prelinearity, a classical De Morgan implication, disjunction of
double negations, and the Kreisel-Putnam formula used to distinguish an
admissible rule from a theorem schema. Some instances are interdefinable;
the count records concrete tested formulas.

## Complete witness export

`decide_ipc(context,goal)` returns a tagged `ProofResult` or
`IPCCountermodelResult`. A positive result contains a proof DAG pruned to the
chosen conclusion's ancestors and an explicit final root reference. A
negative result contains the canonical counterworld's upward cone, renumbered
as a nonempty rooted finite model with root zero. The caller need not search
for an existential witness. `check_ipc_result` independently checks the exact
proof target or every model condition and the refuted sequent.

`truth_table_prove(context,goal)` returns a `ProofResult` in CPC mode or a
`BooleanCountervaluationResult`. Positive leaves contain actual IPC proofs
of a true formula or the negation of a false formula under the valuation
literals. False assumptions yield contradiction leaves. The constructor
merges all branches by LEM and disjunction elimination. Thus positive
certificates do not ask the checker to trust a truth-table verdict.

All 551 exported sequents (516 formulas and 35 nonempty-context cases) were
replayed for each logic. Every result also survived a full JSON encode,
decode and replay. `demo.py` emits four complete portable certificates to
`demo_certificates.json` and checks them after importing their JSON:
IPC identity, IPC failure of excluded middle, a CPC proof of excluded
middle, and the source article's Boolean counterexample.

## Lean audit

No `lean`, `lake`, or `elan` binary was available on the path or in the
inspected standard tool locations. **No Lean file in this package is
represented as compiled or kernel checked.**

The source audit checked the following points:

- All recursive formula definitions recurse on direct subformulas. The four
  substitution lemmas follow the same structural induction and simplification
  pattern as the inspected upstream substitution lemmas.
- `ND.sound` supplies a context-preserving semantic argument for each rule.
  Implication introduction and disjunction elimination extend the valuation
  assumptions exactly once; excluded middle is an explicit assumption enabled
  only for the classical mode.
- IPC soundness eliminates the impossible equation `false=true`. CPC
  soundness uses the explicitly defined `Decidable` result for the finite
  Boolean interpretation. It does not invoke a classical oracle.
- The eight small object-logic proofs use the inspected `Prf` constructors,
  `hyp0` and `hyp1`. Nested contexts were checked by hand against the
  source signatures. The quantified arithmetic example uses `Fm.all` and
  `PTm.app` with the inspected arity-indexed PR syntax.
- The two completeness sentence templates are definitions of object
  formulas. They are not declared as theorems. No missing numerical
  arithmetization step is represented by an axiom or proof hole.
- `atomOccurrences` deliberately permits repetitions; the complete support
  enumeration in the numerical development must deduplicate it before using
  the support cardinality.

No definite elaboration error was found by inspection. Actual parsing,
termination checking, tactic elaboration, inference of implicit indices and
imports remain to be checked with a Lean toolchain. The source files and
README prominently retain that limitation.

## Agreement with the report

The mathematical formula grammar agrees between the report, Python AST and
Lean datatype. The report and formalization plan give exactly the same
numeric coding: bottom 0, atom i as 5i+1, and binary code
`5*((a+b)^2+a)+tag`, with tags 2, 3 and 4. Python uses dataclasses rather than
claiming to implement these numeric codes.

Python uses finite-set contexts, while the report's natural-deduction
presentation and Lean use lists. The report's proved structural rules
justify the correspondence. Python's explicit `weak` and `cut` steps must
be expanded when exporting to the base calculus. The relative saturation
implementation uses in-place scans with backward proof references; the
report's synchronous closure and this scan order have the same least fixed
point and the same finite ascending-measure termination argument.

The finite Kripke checker rejects an empty frame. The canonical truth lemma
is checked against the special constructed prime-theory model, not asserted
for every model that merely passes the generic frame checker.

## Scope of the evidence

The tests provide reproducible implementation checks on specified finite
input families. They do not prove the universal mathematical statements and
do not establish that an encoded theorem has an iPRA derivation. The report
supplies the human proof; `FormalizationPlan.md` identifies the precise
object-level obligations still needed for complete Lean verification.
