import CompactPackedCell
import DiophantineConsistency.ArithmeticModularCancellation

/-! Marker predecessor exclusion and low residue of compact cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace CompactOriginPredecessor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord
open CompactRowTransport CompactMarkedTransport CompactWordCellClient
open CompactForwardCellInputs CompactPackedCell
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem marker_north : compactField (fun t => t.2.1) (0:V) = 435 := by
  have h := field_row (V:=V) (fun t => t.2.1) rfl ⟨0, by decide⟩
  change compactField (fun t => t.2.1) (0:V) = (435:V) at h
  exact h

theorem marker_south : compactField (fun t => t.2.2.2) (0:V) = 1 := by
  have h := field_row (V:=V) (fun t => t.2.2.2) rfl ⟨0, by decide⟩
  change compactField (fun t => t.2.2.2) (0:V) = (1:V) at h
  exact h

/-- The cyclic vertical predecessor of the marker cannot itself be the marker:
    the marker tile's north and south colors differ. -/
theorem predecessor_ne_marker {row : V → V} {N s : V} (hword : CompactWord row N s)
    (hs : 0 < s) (hsN : s < N) : row (cyc N 0 s) ≠ 0 := by
  have he : cyc N 0 s = N-s := by simpa using (cyc_of_lt hsN hs)
  have hj : N-s < N := by rw [← he]; exact cyc_lt hword.pos 0 s
  have hwrap : (N-s+s)%N=0 := by rw [tsub_add_cancel_of_le (le_of_lt hsN), mod_self]
  intro hz
  rw [he] at hz
  have h := hword.south 0 hword.pos (N-s) hj hwrap
  rw [hword.marker, hz, marker_south, marker_north] at h
  norm_num at h

/-- The first selector digit is zero away from marker row zero. -/
theorem cell_mod_four (a d : V) (ha : a ≠ 0) (hd : d ≤ 1) : packedCell a d % 4 = 0 := by
  have hs := packedCell_selector a d hd ⟨0, by decide⟩
  have hz : dig 67 (packedCell a d) 0 = 0 := by simpa [selector, ha] using hs
  rw [dig_zero_index] at hz
  have hdiv : (4:V) ∣ Exp.exp 67 := by
    have he : Exp.exp (67:V) = (4:V)*Exp.exp 65 := by
      rw [← exp_add]
      norm_num
    rw [he]
    exact dvd_mul_right _ _
  have hmod := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V) < 4) hdiv (packedCell a d)
  rw [hz] at hmod
  simpa using hmod.symm

#print axioms CompactOriginPredecessor.marker_north
#print axioms CompactOriginPredecessor.marker_south
#print axioms CompactOriginPredecessor.predecessor_ne_marker
#print axioms CompactOriginPredecessor.cell_mod_four
end CompactOriginPredecessor
