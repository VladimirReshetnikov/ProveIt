import PA194FoldedCache
import PA194BModelSteps
import ConPAMachineCompressedExecutor

set_option autoImplicit false

namespace PA194TableRows
open ConPA.Machine

private def view (row : Row) : Nat × Nat × Nat × Bool × Nat :=
  (row.q, row.b, row.w, row.right, row.q')

private theorem view_injective : Function.Injective view := by
  intro r s h
  cases r
  cases s
  simpa [view, Row.mk.injEq] using h

def validNative (labels : List Nat) (rows : List PA194BRows.Action)
    (tree : PA194FoldedCache.Tree) (q : Nat) (b : Bool) : Bool :=
  match tree.read q b with
  | none => true
  | some (w, dir, next) =>
    let i := 2 * labels.idxOf q + b.toNat
    decide (i < rows.length) &&
      decide (view (PA194BModelSteps.indexedRow rows i) =
        (labels.idxOf q, b.toNat, w.toNat, dir, labels.idxOf next))

/-- Finite checks of a native cache give the corresponding first-match dense lookup. -/
theorem rowAgreement (labels : List Nat) (rows : List PA194BRows.Action)
    (tree : PA194FoldedCache.Tree)
    (keys : tree.keys.all (fun q => decide (q ∈ labels)) = true)
    (valid : ∀ i : Fin labels.length, ∀ b : Bool,
      validNative labels rows tree (labels.getD i.val 254) b = true) :
    Compressed.RowAgreement (PA194BModelSteps.table rows) tree.read labels.idxOf := by
  intro q b w dir next h
  have key : q ∈ tree.keys := by
    by_contra absent
    rw [PA194FoldedCache.Tree.outside tree q b absent] at h
    contradiction
  have listed : q ∈ labels := of_decide_eq_true (List.all_eq_true.mp keys q key)
  obtain ⟨i, hi, hq⟩ := List.mem_iff_getElem.mp listed
  have proof := valid ⟨i, hi⟩ b
  have atIndex : labels.getD i 254 = q := by
    rw [List.getD_eq_getElem?_getD, getElem?_pos labels i hi]
    exact hq
  rw [show (⟨i, hi⟩ : Fin labels.length).val = i from rfl, atIndex, validNative, h] at proof
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at proof
  have hb : b.toNat < 2 := by cases b <;> decide
  have test : (fun row : Row => decide (labels.idxOf q = row.q ∧ b.toNat = row.b)) =
      fun row => row.q == labels.idxOf q && row.b == b.toNat := by
    funext row
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true_iff, beq_iff_eq]
    exact ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  rw [findRow, test, PA194BModelSteps.find rows _ _ hb proof.1]
  exact congrArg some (view_injective proof.2)

#print axioms rowAgreement
end PA194TableRows
