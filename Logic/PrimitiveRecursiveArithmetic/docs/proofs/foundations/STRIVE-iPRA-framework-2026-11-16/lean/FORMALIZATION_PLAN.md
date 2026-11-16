# STRIVE-iPRA Lean formalization plan

Pinned repository commit: `58627ed89814ba122e1f0f012f1aba103cda267b`.

The acceptance criterion is never merely a semantic Lean theorem.  Each public
mathematical claim must end as an ordinary object derivation
`Prf PRAAx Γ φ`; optional `pra_iff_native` or Foundation bridge exports come
only after that endpoint is checked.

## Phase 0 - integrate and replay the structural kernel

1. Place `STRIVE/Kernel.lean` under
   `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Foundations/`.
2. Change its import to the repository-local canonical path if needed.
3. Run Lean on the file, then add its declarations to the axiom audit.
4. Compare `boundary`, `replaceContext`, `specialize`, and `seal` with the
   equivalent scoped-certificate candidate already filed in `docs/proofs`;
   retain one maintained implementation.

Expected dependencies: `ConciseIPRA.PR` only.

## Phase 1 - mixed-radix arithmetic

Create `IPRADerivations/Core/MixedRadix.lean` from `STRIVE/MixedRadix.lean`.
Prove in this order:

1. `pack_zero` and `pack_succ` by the existing `sum2_zero/sum2_succ` equations.
2. positivity of powers of a successor base;
3. `digit_lt` from the remainder half of `div_mod`;
4. interval arithmetic for `code + d * B^i`;
5. `digit_of_append` using `div_mod_unique` twice;
6. `pack_lt_power` by quantifier-free induction;
7. the prefix/suffix decomposition of `pack`;
8. `digit_pack` and `pack_ext`.

Reuse, do not duplicate:

- `IPRADerivations.Core.Division`: `rem`, `quo`, `div_mod`,
  `div_mod_unique`;
- `Core.Powers`: `pw`, `pw_add`, `pw_succ`;
- `Core.MultiSums`: `sum2_zero`, `sum2_succ`,
  `sum2_congr_bounded`;
- `Core.Order` and `Core.Semiring` for interval algebra.

Add executable numeral tests and object-level checks for bases 1, 2, and 3,
including the empty table.  Base zero is not used as a radix; all total PR
functions remain defined there, but the decoding theorems require a successor
base.

## Phase 2 - Boolean folds and bounded disjoint sums

Add a small `Core/BooleanFolds.lean` if no current module already exports the
needed exact interfaces.  Required lemmas:

- Boolean normalization and closure under multiplication/`any`;
- `allBelow` and `anyBelow` defining equations;
- elimination/introduction at `N+1`;
- prefix sums of heterogeneous code bounds;
- selecting the unique disjoint-sum interval;
- prefix products and digit access for heterogeneous mixed radix.

The induction predicates are equations and order atoms only.  The existing
`Search.mu` should be adapted for least success rather than reimplemented.

## Phase 3 - compile fixed atoms and binary connectives

Implement `CompiledFormula` and then:

1. `compileAtom` from a reflected Boolean atom;
2. `compileAnd` using product coding for positive certificates and disjoint
   coding for negative certificates;
3. `compileOr` with the dual coding.

At this stage test formulas with no quantifiers.  Check every field of the
structure and add closed instantiations to `Checks/Axioms.lean`.

## Phase 4 - bounded quantifiers

Implement `compileExists` first.

- Positive side: prefix sum of positive child bounds, least successful witness,
  and the selected child code.
- Negative side: prefix product of negative child bounds, one packed code, and
  an `allBelow` checker of every decoded child.
- Empty bound: positive code bound zero, negative code bound one, with the empty
  table code zero.

Then implement `compileForall` by duality.  Prove checker soundness by
quantifier-free induction on the numerical bound.  The body is a fixed
compiled module one scope level higher; no recursion over formula codes occurs
inside iPRA.

## Phase 5 - generated formula modules

Write a metalevel generator that accepts a restricted Lean/JSON description of
one fixed bounded formula and emits:

- concrete `PR` symbols for value, bounds, checkers, and canonical codes;
- a Lean module assembling the constructors;
- a theorem ledger naming the final `Prf PRAAx` endpoints;
- fixtures cross-checked against `reference/strive_reference.py`.

The generator is untrusted convenience.  Lean checks the emitted derivations.

First generated regressions:

1. the modular success challenge in `examples/bounded_challenge_success.json`;
2. the failure challenge and least counterchallenge in
   `examples/bounded_challenge_failure.json`;
3. empty existential and universal bounds;
4. a formula mixing conjunction and disjunction.

## Phase 6 - contract graph and certificate escape

Use `CompiledContract` as the public boundary.  Implement three explicit modes:

- **local**: producer proves an existential certificate and `Prf.exE` erases it;
- **observed**: prove pairwise observer invariance and return only the observer;
- **named**: use `Search.mu` to expose the least accepted code, with its bound
  and acceptance theorem.

Never use least search merely to make a proof compose.  Local certificates
should remain under their existential binder.

## Phase 7 - finite demand closure and trace replay

Specialize each finite demand graph to one packed state recurrence.  Prove the
finite-chain rank theorem, then compile the stabilized demands into an acyclic
clocked schedule.  Reuse existing FINER/CBIP trace-reflection work where it has
been checked; otherwise make the exact local base, step, and final obligations
visible as residual formulas.

## Phase 8 - observers and approximate mathematics

Add interfaces in dependency order:

1. exact observer invariance;
2. equivalence-respecting observers (no quotient type required);
3. rational pseudo-distance and diameter bounds;
4. reverse error-demand propagation for a fixed finite DAG;
5. finite-net optimization and metastable window schemas.

Every analytic application supplies explicit coverage, modulus, lower-bound,
or separation producers.  The framework must not synthesize them from a bare
classical existence theorem.

## Phase 9 - bridge and native exports

After ordinary derivations are complete:

1. use `IPRABridge` open-sequent transport for Foundation clients;
2. preserve every residual formula and free-variable assignment;
3. use `pra_iff_native` only for the final closed/native corollary;
4. replay the exact endpoint and axiom audit.

## Completion checklist

A module is complete only when:

- no `sorry` or added axiom remains;
- its public theorem literally has a `Prf PRAAx` judgment;
- all generated PR symbols have defining equations available at arbitrary terms;
- empty bounds and zero conventions are tested;
- positive and negative checker soundness are separate theorems;
- canonical acceptance does not replace checker soundness;
- unresolved producers are explicit formulas, not prose assumptions;
- `lake build IPRADerivations` and the axiom audit pass;
- any Foundation/native export is replayed independently.
