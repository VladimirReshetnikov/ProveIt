import OCiPRA.Contracts

/-!
# Minimal object-language examples and application targets

The first theorem is intentionally elementary: it tests that existential
packaging really concludes in `Prf PRAAx`.  Larger applications should be
built only after their local arithmetic lemmas have the same endpoint.
-/

namespace LeanProofs.ConciseIPRA.OCiPRA.Examples

open Syn
open scoped Fm
open LeanProofs.ConciseIPRA.OCiPRA

/-- Output slot 0 equals input slot 1. -/
def identity : ProgramContract 1 where
  pre := PTm.zero ≐ (PTm.zero : PTm 1)
  program := PR.proj 0
  post := Syn.var 0 ≐ (Syn.var 1 : PTm 2)
  certified := by
    simpa using (PRA.proj (Γ := [PTm.zero ≐ (PTm.zero : PTm 1)])
      (0 : Fin 1) (Syn.var : Fin 1 → PTm 1))

/-- An actual object-theory existential consequence of the identity program. -/
theorem identity_exists :
    [] ⊢[PRAAx] (identity.pre ⟶ Fm.ex identity.post) :=
  identity.asImplication

/-!
Larger application targets are intentionally absent from this file.  They should
be added only with their complete formulas and must not be replaced by trivial
`Prop` placeholders: defining a target is not proving it.
-/

end LeanProofs.ConciseIPRA.OCiPRA.Examples
