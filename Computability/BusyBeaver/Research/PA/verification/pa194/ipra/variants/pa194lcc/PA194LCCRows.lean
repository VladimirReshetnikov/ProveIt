import PA194LCCData
import PA194TableRows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PA194LCCRows
open PA194LCCData ConPA.Machine

abbrev RowView := Nat × Nat × Nat × Bool × Nat
def view (row : Row) : RowView := (row.q,row.b,row.w,row.right,row.q')
theorem view_injective : Function.Injective view := by
  intro r s h
  cases r
  cases s
  simpa [view,Row.mk.injEq] using h

def validNative (q : Nat) (b : Bool) : Bool :=
  match machine q b with
  | none => true
  | some (w,dir,q') =>
    let i := 2 * denseControl q + b.toNat
    decide (i < rows.length) &&
      decide (view (PA194BModelSteps.indexedRow rows i) =
        (denseControl q,b.toNat,w.toNat,dir,denseControl q'))

theorem listed_valid : ∀ i : Fin 195, ∀ b : Bool,
    validNative (labels.getD i.val 254) b = true := by decide +kernel

theorem labels_length : labels.length = 195 := by decide +kernel

theorem oldKeys_covered : PA194LCData.nativeTree.keys.all
    (fun q => decide (q ∈ labels ∨ q = 41 ∨ q = 190)) = true := by decide +kernel

theorem outside (q : Nat) (b : Bool) (h : q ∉ labels) : machine q b = none := by
  by_cases h41 : q = 41
  · subst q; simp [machine]
  by_cases h190 : q = 190
  · subst q; simp [machine]
  have h28 : q ≠ 28 := by intro e; subst q; exact h (by decide)
  have h70 : q ≠ 70 := by intro e; subst q; exact h (by decide)
  have h139 : q ≠ 139 := by intro e; subst q; exact h (by decide)
  have h330 : q ≠ 330 := by intro e; subst q; exact h (by decide)
  have h331 : q ≠ 331 := by intro e; subst q; exact h (by decide)
  have hk : q ∉ PA194LCData.nativeTree.keys := by
    intro hq
    have hx := of_decide_eq_true (List.all_eq_true.mp oldKeys_covered q hq)
    rcases hx with hm | he | he
    · exact h hm
    · exact h41 he
    · exact h190 he
  have hn := PA194FoldedCache.Tree.outside PA194LCData.nativeTree q b hk
  simpa [machine,h41,h190,h28,h70,h139,h330,h331,PA194LCData.machine] using hn

theorem rowAgreement : Compressed.RowAgreement table machine denseControl := by
  intro q b w dir q' h
  have listed : q ∈ labels := by
    by_contra hh
    rw [outside q b hh] at h
    contradiction
  obtain ⟨i, hi, hq⟩ := List.mem_iff_getElem.mp listed
  have hi' : i < 195 := by simpa only [labels_length] using hi
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
  rw [findRow, table, hf, PA194BModelSteps.find rows _ _ hb proof.1]
  exact congrArg some (view_injective proof.2)

#print axioms listed_valid
#print axioms rowAgreement
end PA194LCCRows
