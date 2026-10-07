import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis

namespace OAI

section

namespace Erdos3

open Module

theorem supportedSubmoduleBasis_comap_span {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (b : Basis ι K V) (P Q : Submodule K V) (S T : Set ι)
    (hP : P = Submodule.span K (b '' S)) (hQ : Q = Submodule.span K (b '' T)) :
    Q.comap P.subtype = Submodule.span K
      (supportedSubmoduleBasis b P S hP '' {i : S | i.val ∈ T}) := by
  ext x
  change x.val ∈ Q ↔ _
  rw [hQ, basis_mem_span_image_iff, basis_mem_span_image_iff]
  constructor
  · intro h i hi
    rw [supportedSubmoduleBasis_repr]
    exact h i.val hi
  · intro h i hi
    by_cases hs : i ∈ S
    · have hh := h ⟨i, hs⟩ hi
      simpa only [supportedSubmoduleBasis_repr] using hh
    · exact (basis_mem_span_image_iff b S x.val).mp (hP.le x.property) i hs

end Erdos3

end

end OAI
