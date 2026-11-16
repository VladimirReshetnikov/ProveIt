import DiophantineConsistency.IPRAPellSlack
import DiophantineConsistency.NativePellPower

/-! Check the positive witness interface at the maintained native Pell
consumer's natural-number premises. -/

set_option autoImplicit false

open DiophantineConsistency IPRAPellSlack

example {X Y r k c a R η ζ : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hr : 1 ≤ r) (hR : R = 2 * r + 1)
    (ha : a = Y * (X + 1)) (hc : c = Pell.yn (by omega : 1 < a + 2) R)
    (hk : k = 2 * Pell.yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1))
    (hck : c = k * Y + η) (slack : natRow η k ζ) : X ^ r < 2 * (Y + 1) :=
  NativePellPower.power_lt_twice_Y hX hY hr hR ha hc hk hck slack.2 slack.1

section ObjectTheory

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

example (terms : Fin 31 → PTm n) :
    Γ ⊢[PRAAx] Fm.iff (LeanProofs.IPRA.lt (terms 12) (terms 12 + terms 13))
      (hasSlack (terms 12) (terms 12 + terms 13)) :=
  Prf.iffI (hasSlack_of_lt _ _) (lt_of_hasSlack _ _)

example (terms : Fin 31 → PTm n) (positive : Γ ⊢[PRAAx] LeanProofs.IPRA.lt zero (terms 13)) :
    Γ ⊢[PRAAx] row (terms 12) (terms 12 + terms 13) (monus (terms 12 + terms 13) (terms 12)) ⋏
      (monus (terms 12 + terms 13) (terms 12) ≐ terms 13) := by
  have slack := nativeSourceSlack terms positive
  exact .andI (row_of_lt (.andE₁ slack)) (.andE₂ slack)

example (terms : Fin 31 → PTm n)
    (interval : Γ ⊢[PRAAx]
      terms 19 ≐ terms 12 + (terms 12 + terms 13) * (terms 16 * terms 9))
    (positive : Γ ⊢[PRAAx] LeanProofs.IPRA.lt zero (terms 13)) :
    Γ ⊢[PRAAx] LeanProofs.IPRA.lt (terms 19)
      ((terms 12 + terms 13) * (terms 16 * terms 9 + succ zero)) :=
  nativeSourceUpperInterval terms interval positive

end ObjectTheory

#print axioms DiophantineConsistency.NativePellPower.power_lt_twice_Y
