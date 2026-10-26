import DiophantineConsistency.CurrentWordConstruction2011
import Mathlib.Logic.Function.Basic

namespace ProofSimplification20261026

/-- A pointwise invariant survives one overwrite if its new value obeys
that invariant at the overwritten position. Distinctness is unnecessary. -/
theorem forall_update_of_forall {ι α : Type*} [DecidableEq ι]
    (P : ι → α → Prop) (f : ι → α) (i : ι) (a : α)
    (hf : ∀ j, P j (f j)) (ha : P i a) :
    ∀ j, P j (Function.update f i a j) :=
  (Function.forall_update_iff f P).mpr ⟨ha, fun j _ => hf j⟩

open DiophantineConsistency
open CurrentMasks2011 CurrentCellConstruction2011 CurrentWordConstruction2011

/-- Proof-side view only; the public executable `word` definition is untouched. -/
def controlledCell (i : Fin 942) (dummy marker : ℕ) : ℕ → ℕ :=
  Function.update (Function.update (localDigit i) 1004 marker) 977 dummy

/-- Bind the update view to the literal nested conditions, including their
priority when a generic version permits repeated update positions. -/
theorem controlledCell_apply (i : Fin 942) (dummy marker e : ℕ) :
    controlledCell i dummy marker e =
      if e = 977 then dummy else if e = 1004 then marker else localDigit i e := by
  simp only [controlledCell, Function.update_apply]

def DigitOK (e v : ℕ) : Prop := v ≤ 1 ∧ (e ∉ lowSupport → v = 0)

/-- The old local-digit proofs provide the base certificate. -/
theorem localDigit_ok (i : Fin 942) (e : ℕ) : DigitOK e (localDigit i e) :=
  ⟨localDigit_boolean i e, localDigit_support i e⟩

/-- Each numeric control is independently Boolean. Neither is identified
with a shifted Start marker and neither is assumed equal to zero. -/
theorem controlledCell_ok (i : Fin 942) (dummy marker : ℕ)
    (hd : dummy ≤ 1) (hm : marker ≤ 1) :
    ∀ e, DigitOK e (controlledCell i dummy marker e) := by
  apply forall_update_of_forall DigitOK _ 977 dummy
  · apply forall_update_of_forall DigitOK _ 1004 marker
    · exact localDigit_ok i
    · exact ⟨hm, fun h => False.elim (h (by decide))⟩
  · exact ⟨hd, fun h => False.elim (h (by decide))⟩

/-- Exact binding to the original source word; this works also for N=0
at the level where the original word definition permits that modulus. -/
theorem word_controlledCell {N : ℕ} (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ) (k : ZMod (N*2011)) :
    word a dummy marker k = controlledCell
      (a ((k.val / 2011 : ℕ) : ZMod N))
      (dummy ((k.val / 2011 : ℕ) : ZMod N))
      (marker ((k.val / 2011 : ℕ) : ZMod N)) (k.val % 2011) := by
  simp only [word, controlledCell_apply]

theorem word_ok {N : ℕ} (a : ZMod N → Fin 942)
    (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1)
    (k : ZMod (N*2011)) : DigitOK (k.val % 2011) (word a dummy marker k) := by
  rw [word_controlledCell]
  exact controlledCell_ok _ _ _ (hd _) (hm _) _

-- Proposed clients of the combined invariant:
example {N : ℕ} (a : ZMod N → Fin 942) (dummy marker : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (hm : ∀ j, marker j ≤ 1) (k : ZMod (N*2011)) :
    word a dummy marker k ≤ 1 :=
  (word_ok a dummy marker hd hm k).1

-- The existing public word_support does NOT assume hd or hm. A production
-- replacement must keep that stronger theorem by instantiating the update
-- invariant only with P(e,v) := (e ∉ lowSupport → v = 0). The conjunctive
-- DigitOK theorem above is a convenience client, not a stronger public premise.

end ProofSimplification20261026
