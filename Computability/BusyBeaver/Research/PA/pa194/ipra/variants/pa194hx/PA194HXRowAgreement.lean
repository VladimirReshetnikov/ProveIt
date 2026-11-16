import PA194HXRowData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194HXRowAgreement
open PA194HXNativeLabels PA194HXContracts PA194HXRowData ConPA.Machine

theorem outside (q : Nat) (b : Bool) (h : q ∉ labels) :
    PA194HXContracts.cachedMachine q b = none := by
  have h21 : q ≠ 21 := by intro e; subst q; exact h (by decide)
  have h45 : q ≠ 45 := by intro e; subst q; exact h (by decide)
  have hk : q ∉ PA194FoldedCache.table.keys := by
    intro hq
    exact h (of_decide_eq_true (List.all_eq_true.mp keys_listed q hq))
  have hn := PA194FoldedCache.Tree.outside PA194FoldedCache.table q b hk
  simpa [PA194HXContracts.cachedMachine,h21,h45,PA194FoldedCache.cachedMachine] using hn

theorem rowAgreement : Compressed.RowAgreement PA194HXDispatch.table PA194HXContracts.cachedMachine denseControl := by
  intro q b w dir q' h
  have listed : q ∈ labels := by
    by_contra hh
    rw [outside q b hh] at h
    contradiction
  obtain ⟨i, hi, hq⟩ := List.mem_iff_getElem.mp listed
  have hi' : i < 195 := by simpa only [size] using hi
  have proof := listed_valid ⟨i, hi'⟩ b
  have hAt : labels.getD i 254 = q := by
    rw [List.getD_eq_getElem?_getD, getElem?_pos labels i hi]
    exact hq
  rw [show (⟨i, hi'⟩ : Fin 195).val = i from rfl, hAt, validNative, h] at proof
  simp only [Bool.and_eq_true_iff, decide_eq_true_eq] at proof
  have hb : b.toNat < 2 := by cases b <;> decide
  have hf : (fun row : Row => decide (denseControl q = row.q ∧ b.toNat = row.b)) =
      fun row => row.q == denseControl q && row.b == b.toNat := by
    funext row
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, Bool.and_eq_true_iff, beq_iff_eq]
    exact ⟨fun h => ⟨h.1.symm,h.2.symm⟩, fun h => ⟨h.1.symm,h.2.symm⟩⟩
  rw [findRow, PA194HXDispatch.table, hf,
    PA194BModelSteps.find PA194HXRows.rows _ _ hb proof.1]
  exact congrArg some (view_injective proof.2)

#print axioms rowAgreement
end PA194HXRowAgreement
