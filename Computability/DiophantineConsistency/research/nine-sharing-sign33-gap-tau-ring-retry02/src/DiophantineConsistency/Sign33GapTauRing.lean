import DiophantineConsistency.Sign33Windows
import Sign33OrderedRing

/-! Transport the two scalar window consequences to the difference ring. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Sign33GapTauRing
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem gap_tau_of_windows (q F alpha E N k r : V)
    (hq : 1 ≤ q) (hN : 1 ≤ N)
    (hgap : 0 < q-F-alpha) (hr : r+2 < E) :
    0 ≤ (ι q-1)*(ι q-ι F)+ι alpha ∧ 0 ≤ ι E*ι N+ι k-ι r := by
  have ha : alpha < q-F := tsub_pos_iff_lt.mp hgap
  have hF : F < q := tsub_pos_iff_lt.mp (lt_of_le_of_lt _root_.zero_le ha)
  have hsum : F+alpha ≤ q := by
    have h := add_le_add_left (le_of_lt ha) F
    have he : (q-F)+F=q := tsub_add_cancel_of_le hF.le
    simpa only [add_comm alpha F, he] using h
  have hrr : r ≤ r+2 := by
    simpa only [add_comm (2 : V) r] using (le_add_self : r ≤ 2+r)
  have hrle : r ≤ E := le_trans hrr (le_of_lt hr)
  have hqR : (1 : DiffRing V) ≤ ι q := by
    simpa only [map_one] using (ι_le_ι.mpr hq)
  have hNR : (1 : DiffRing V) ≤ ι N := by
    simpa only [map_one] using (ι_le_ι.mpr hN)
  have hsumR : ι F+ι alpha ≤ ι q := by
    simpa only [map_add] using (ι_le_ι.mpr hsum)
  exact Sign33OrderedRing.gap_tau_signs (ι q) (ι F) (ι alpha) (ι E) (ι N) (ι k) (ι r)
    hqR (ι_nonneg alpha) hsumR (ι_nonneg E) hNR (ι_nonneg k) (ι_le_ι.mpr hrle)
end DiophantineConsistency.Sign33GapTauRing
#print axioms DiophantineConsistency.Sign33GapTauRing.gap_tau_of_windows
