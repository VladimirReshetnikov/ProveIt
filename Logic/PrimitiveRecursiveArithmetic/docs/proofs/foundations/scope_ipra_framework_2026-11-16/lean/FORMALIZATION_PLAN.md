# SCOPE-iPRA Lean formalization plan

Repository baseline: `VladimirReshetnikov/ProveIt` main commit
`58627ed89814ba122e1f0f012f1aba103cda267b` (2026-11-16).

## Proposed integration paths

- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations/Framework/SCOPE/`
- umbrella import: `IPRADerivations.Framework.SCOPE`
- Foundation adapters, only after the ordinary implementation is checked:
  `Logic/PrimitiveRecursiveArithmetic/Bridge/Lean/IPRABridge/SCOPE.lean`

## Milestones

1. **Structural kernel.** Elaborate `StructuralKernel.lean`. Add every theorem
   to `Checks/Axioms.lean`. The expected dependencies are only
   `ConciseIPRA.PR` and the existing structural lemmas of `Prf`.
2. **Boolean algebra.** Define `bnot`, `band`, `bor`, `bimp`; prove Booleanity
   and truth tables at arbitrary terms and contexts.
3. **Arbitrary-arity folds.** Use `PTm.toPR`, `recDef`, `rec_zero`, and
   `rec_succ` for finite universal and existential folds. Prove their equations
   before attempting reflection.
4. **Fixed bounded formulas.** Implement `BForm`, `denote`, and the compiler
   returning a `Reflection` package. Reuse `eqb` and `Search.mu`. Test nested
   alternation with a parameter under both binders.
5. **Least accepted adapter.** Wrap `Search.search_found`, `search_minimal`,
   and `search_spec` with the accepted-bit convention and prove the sentinel
   case.
6. **Mixed-radix certificates.** Reuse `Core.Division` and finite products to
   prove digit extraction and encode/decode laws for a fixed dimension.
7. **Capped cyclic demand closure.** Define the inflationary iteration and
   prove boundedness, strict rank increase, fixedness by total capacity, and
   leastness. Keep the induction matrix quantifier-free by using reflected
   coordinate bits.
8. **Trace reflection.** Package `recDef` plus `IPRA.ind` into a reusable
   theorem whose hypotheses are base, step, and terminal object derivations.
9. **Finite strategies and viability.** Begin with `forall-exists`; then add a
   meta-level recursion over fixed alternation shapes. Formalize backward
   viability before path selection.
10. **Observer interfaces.** Exact, quotient, metric-diameter, gap-guarded, and
    spanning-tree descent. Exercise each with two different valid certificates.
11. **Scope-normalization compiler.** Define a host-side finite graph whose
    nodes carry local derivation builders. Compile in dependency order and
    return `ResidualResult`. The compiler itself may use Lean data structures;
    its output must be a `Prf PRAAx` value.
12. **Bridge and pilots.** Use the already checked open-sequent bridge. Migrate
    one finite arithmetic theorem, one quantitative-analysis contract, one
    finite-complex theorem, and one height-bounded Diophantine enumeration.

## Acceptance gates

- `LAKE_JOBS=1 lake build IPRADerivations`
- focused builds of each new module
- no `sorry`, `admit`, `axiom`, `Lean.ofReduceBool`, or new trusted declaration
- `#print axioms` consistent with the repository policy
- substitution at non-variable terms
- one QF induction with parameters under a binder
- a nested bounded `forall-exists-forall` reflection test
- a cyclic demand example requiring more than one pass
- a viability example where greedy local selection fails
- two valid certificates with one stable public observation
- a residual theorem whose missing producer remains visible in its type
- both directions of a scoped Foundation bridge replay

## Proof-size engineering

Keep generated proof graphs shared rather than expanded. Prefer reusable
object lemmas for Boolean truth tables, digit equations, and trace steps. A
future certificate language may reduce serialized size, but its checker
soundness must itself produce the ordinary `Prf PRAAx` judgment; external
Python acceptance is never a substitute.
