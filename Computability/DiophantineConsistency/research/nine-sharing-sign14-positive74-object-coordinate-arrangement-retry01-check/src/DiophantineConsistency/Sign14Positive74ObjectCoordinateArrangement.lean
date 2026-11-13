import DiophantineConsistency.Sign14Positive74ObjectLeibnizParamNative

/-! SOURCE-ONLY: arrange any coordinate first, preserving the remaining coordinates. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectCoordinateArrangement

/-- Move the selected original index to the distinguished position zero. -/
def focusIndex {n : ℕ} (i : Fin (n+1)) : Fin (n+1) → Fin (n+1) :=
  i.insertNth 0 (fun j => j.succ)

theorem focus_assignment {n : ℕ} {α : Type} (i : Fin (n+1)) (x : α)
    (v : Fin (n+1) → α) :
    (fun j => (Fin.cons x (i.removeNth v) : Fin (n+1) → α) (focusIndex i j)) = Function.update v i x := by
  rw [← Fin.insertNth_removeNth i x v]
  funext j
  cases j using Fin.succAboveCases i with
  | x => simp [focusIndex]
  | p j => simp [focusIndex, Fin.removeNth]
end DiophantineConsistency.Sign14Positive74ObjectCoordinateArrangement
#print axioms DiophantineConsistency.Sign14Positive74ObjectCoordinateArrangement.focus_assignment
