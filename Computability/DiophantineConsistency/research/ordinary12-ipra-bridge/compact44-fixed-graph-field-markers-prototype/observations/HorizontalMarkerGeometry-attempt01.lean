import DiophantineConsistency.FixedGraphFieldBits
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
noncomputable section
namespace HorizontalMarkerGeometry
open CompactConcreteMask FieldWindowGeometry CompactHighPopulation

theorem selectors (j : ℕ) (hj : j<943) :
    absent (phase 1073 (4393-j)) ∧ absent (phase 1073 (5495-j)) := by
  simp only [absent,phase,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem bare (j : Fin 5) (h1 : j≠⟨1,by decide⟩) (h4 : j≠⟨4,by decide⟩) :
    absent (phase 1073 (![30,62,1100,2201,8849] j)) := by
  fin_cases j <;> simp_all [absent,phase,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton] <;> omega

theorem temporal_absent : absent 1073 := by
  simp only [absent,support,Finset.mem_sdiff,Finset.mem_union,Finset.mem_range,
    Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]
  omega

theorem high_one : highDigits.getD 1073 0=1 := by decide +kernel
#print axioms HorizontalMarkerGeometry.selectors
#print axioms HorizontalMarkerGeometry.bare
#print axioms HorizontalMarkerGeometry.temporal_absent
#print axioms HorizontalMarkerGeometry.high_one
end HorizontalMarkerGeometry
