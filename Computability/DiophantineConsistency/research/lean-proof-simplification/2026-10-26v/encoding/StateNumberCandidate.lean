import DiophantineConsistency.WangMachineEncoding
import Mathlib.Logic.Equiv.Fin.Basic

/-!
UNCOMPILED proposal. ProveIt pin 22e020937caa81d0cb72a4f63071d6c0bcc1eba9.
The executable stateNumber and its none=215 sentinel are unchanged.
Only the injectivity proof is replaced, using Mathlib's existing last-slot
finite equivalence. This is not the zero-slot finSuccEquiv.
-/
namespace DiophantineConsistency.Round3StateEncoding
open WangMachineEncoding

theorem stateNumber_injective_candidate : Function.Injective stateNumber := by
  have hcode : stateNumber = fun s : Option (Fin 215) =>
      ((finSuccEquivLast.symm s : Fin 216) : ℕ) := by
    funext s
    cases s <;> simp [stateNumber]
  rw [hcode]
  exact Fin.val_injective.comp finSuccEquivLast.symm.injective

-- Regression statements retain the actual terminal sentinel and all states.
example : stateNumber none = 215 := rfl
example (q : Fin 215) : stateNumber (some q) = q.val := rfl
example (s t : Option (Fin 215)) : stateNumber s = stateNumber t ↔ s = t :=
  stateNumber_injective_candidate.eq_iff

end DiophantineConsistency.Round3StateEncoding
#print axioms DiophantineConsistency.Round3StateEncoding.stateNumber_injective_candidate
