import DiophantineConsistency.Compact44.HorizontalMarkerGeometry
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace VerticalMarkerGeometry
open CompactConcreteMask FieldWindowGeometry CompactHighPopulation

theorem selectors (j : ℕ) (hj : j<943) :
    absent (phase 1022 (4393-j)) ∧ absent (phase 1022 (5495-j)) := by
  simp only [absent,phase,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem bare (j : Fin 5) (h0 : j≠⟨0,by decide⟩) :
    absent (phase 1022 (![30,62,1100,2201,8849] j)) := by
  fin_cases j <;> simp_all [absent,phase,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]

theorem high_one : highDigits.getD 1022 0=1 := by decide +kernel
#print axioms VerticalMarkerGeometry.selectors
#print axioms VerticalMarkerGeometry.bare
#print axioms VerticalMarkerGeometry.high_one
end VerticalMarkerGeometry
