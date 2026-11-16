# KIFC formalization plan

## Upstream pin

Use ProveIt commit `7c1f2594117c15a980d24300593d625722812768`
or explicitly re-audit a later revision. Add this artifact's `lean/KIFC`
directory under
`Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/KIFC`
and adjust import prefixes.

## Phase 0: compile the kernel adapter

1. Compile `KernelCore.lean` against `IPRADerivations.Core.Basic`.
2. Resolve namespace or notation drift only; do not weaken theorem conclusions.
3. Run `#print axioms` for `Schedule.compile` and `LoopCertificate.compile`.
4. Compile the algebra adapters in `Examples.lean`.

Exit criterion: no `sorry`; every public proof field concludes `Prf PRAAx`.

## Phase 1: reflected Boolean library

Implement PR symbols and object proofs for Boolean not/and/or, zero test,
equality, `<`, `≤`, maximum, conditional selection, and fixed-radix table
access. Prove range and reflection. Build a metalevel syntax-directed compiler
for one fixed formula; do not build an object-level formula evaluator.

## Phase 2: reuse checked bounded search

1. Import `IPRADerivations.Core.Search`.
2. For a truth code `chi`, prove that `1 ∸ chi = 0` iff `chi = 1`, using the
   Boolean range theorem.
3. Instantiate `Search.mu`, `search_spec`, `search_found`, and
   `search_minimal` with the adapted body.
4. Package the result as `SearchCertificate`.
5. Test first on least divisor and bounded table lookup.

Exit criterion: no duplicate generic least-search induction is needed.

## Phase 3: bounded folds and existential normal form

Generate `allB` and `anyB` by primitive recursion for a fixed predicate. Prove
zero/successor equations, range, and reflection while keeping object induction
on term equalities. Construct `BoundedExistsCertificate`: existence iff found,
found iff the QF least-witness certificate.

## Phase 4: one deterministic generated loop

Use checked pairing/simultaneous recursion to compile exact rational bisection
of `y^3 + y = x`:

1. exact monotonicity identity through `ipra_ring`;
2. initial bracket;
3. packed bisection recurrence;
4. QF bracket/width invariant;
5. terminal interval theorem;
6. ordinary and native closed theorems;
7. axiom audit.

## Phase 5: finite tables and relational viability

Choose one rectangular table code and derive lookup/write equations. Compute
viability backward by forward recursion on reverse time. Prove the row
recurrence, a bounded path checker, viability iff compatible suffix, and least
viable path validity using the checked search adapter.

## Phase 6: observers and shrinking names

Reuse signed integer/rational codes. Derive exact observer elimination,
diameter observer elimination, adjacent cloud/edge/cloud estimates, finite sum
monotonicity, and the shrinking-cloud tail theorem. Retain metastable or finite
contracts when no tail modulus is supplied.

## Phase 7: retained classical transfer

Work through `RetainedTransferBlueprint.lean` in dependency order:

1. equality/QF decidability;
2. stability of translated formulas;
3. recursion over classical derivations;
4. QF and retained recovery;
5. context replacement by `Prf.trans`;
6. lifting of intuitionistic proofs to the classical source.

Replace the duplicate syntax declarations with the repository's
`ipra_local_global/lean/NegativeSyntax.lean` definitions. The main engineering
risk is binder/substitution bookkeeping, not a missing logical principle.

## Phase 8: relational generated example

Use a Cauchy input for `x`, retain both child intervals when a sign test is not
certified, compute finite viability, and export a diameter-stable midpoint or
interval observation. Do not force an exact branch at equality.

## Phase 9: typed graph elaborator

Only after deterministic and relational examples compile, generalize their
shared metalevel code into a finite graph AST. The generator emits specialized
PR symbols, local `KernelRule`s, a `LoopCertificate`, and a `Schedule`; the
object theory never evaluates graph codes.

## Completion gates

A theorem is complete only when:

- its object formula and producer assumptions are explicit;
- the public theorem has type `Prf PRAAx`;
- no `sorry`, `admit`, or theorem-specific axiom occurs in its dependency
  closure;
- `#print axioms` is recorded;
- a clean build from the pinned commit passes;
- finite reference tests are reported as tests, not proof;
- native transfer is applied only after the ordinary derivation.
