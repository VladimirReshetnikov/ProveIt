# SCOPE-iPRA Lean formalization plan

Target checkout: the ProveIt revision recorded in `../metadata/SOURCE_AUDIT.md`.
The canonical endpoint of every public theorem is an ordinary open judgment
`Γ ⊢[PRAAx] φ`.

## Milestones

1. **Elaborate `SCOPE/Kernel.lean`.** It uses only the checked constructors and
   structural theorems of `ConciseIPRA.Deduction`. Add it to the existing axiom
   audit. No `sorry` or new axiom is permitted.
2. **Generalize bounded search to arbitrary parameter arity.** Refactor the
   proof of `IPRADerivations.Core.Search` from one packed parameter to `k`
   parameters using `recDef` and `PTm.toPR`. Keep the existing two-argument API
   as a corollary.
3. **Implement bit combinators.** Provide fixed PR symbols for Boolean not,
   and, or, implication, equality and strict order, together with Booleanity
   and truth/false reflection at arbitrary terms and contexts.
4. **Implement `BCode.char`.** Return a `PR k`, not a `PTm k`. This is the
   critical schema-first choice: later substitution changes only arguments.
5. **Prove `reflect`.** Structural recursion returns Booleanity, `one_iff`, and
   `zero_iff`. The bounded quantifier cases invoke arity-generic search; no
   quantified formula is used as an induction invariant.
6. **Add exact and quotient observers.** First prove the existential output
   relation and uniqueness modulo an explicit equivalence. Add metric diameter
   as a separate module.
7. **Implement the indexed `Plan` compiler.** Begin with exact, specialize,
   supply, seal, and boundary. The result of `compile` must be a literal `Prf`.
8. **Implement graph normalization.** This is metalevel code that moves witness
   scopes to their consumer regions and collects reachable residuals. Its only
   trusted output is the `Prf` returned by `compile`.
9. **Add trace and demand modules.** Reuse `IPRA.ind`; all loop invariants are
   equations between reflected bits or packed state terms and are explicitly
   quantifier-free.
10. **Pilot migrations.** Use one checked finite-arithmetic theorem, one
    bounded-search example, one relational observer, and one theorem with a
    genuine height/modulus residual.

## Acceptance gates

- `lake build IPRADerivations` and focused SCOPE modules succeed.
- No `sorryAx`, theorem-specific `axiom`, or semantic shortcut appears.
- `#print axioms` matches the repository's accepted metatheoretic footprint.
- Tests include nested alternating bounded quantifiers and substitutions by
  compound terms.
- Every named witness has a direct term or a proved finite bound.
- Executable Python tests remain labelled semantic reference only.
