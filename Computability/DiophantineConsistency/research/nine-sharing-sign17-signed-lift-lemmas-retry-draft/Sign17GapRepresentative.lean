import DiophantineConsistency.Sign17OrderedGap

/-! SOURCE-ONLY: nonnegative difference gives a model-natural representative. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17GapRepresentative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem exists_gap (F S W : V) (hF : 1 ≤ F) (hS : 0 < S)
    (hNa : (ι F)*(ι F) - ((ι S)*(ι S))*((ι F)*(ι F)-(ι W)*(ι W))-1=0) :
    ∃ gap : V, ι gap = (ι F)*(ι F)-(ι W)*(ι W) := by
  have hFr : (1 : DiffRing V) ≤ ι F := by
    simpa only [map_one] using (ι_le_ι.mpr hF)
  have hSr : (0 : DiffRing V) < ι S := by
    simpa only [map_zero] using (ι_lt_ι.mpr hS)
  have hn := Sign17OrderedGap.difference_nonnegative (ι F) (ι S) (ι W) hFr hSr hNa
  obtain ⟨gap, hgap⟩ := nonneg_iff.mp hn
  exact ⟨gap, hgap.symm⟩
end DiophantineConsistency.Sign17GapRepresentative
#print axioms DiophantineConsistency.Sign17GapRepresentative.exists_gap
