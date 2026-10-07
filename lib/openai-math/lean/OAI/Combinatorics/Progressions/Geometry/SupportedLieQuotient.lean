import OAI.Combinatorics.Progressions.Estimates.ImageRepresentatives
import OAI.Combinatorics.Progressions.Estimates.QuotientInducedMark

namespace OAI

section

namespace Erdos3

open Module

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem supportedQuotientBasis_lieStructure (b : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (S : Set ι) (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i j k : {i // i ∉ S}) :
    lieStructureConstants (L := L ⧸ I) (supportedQuotientBasis b I.toSubmodule S hI) i j k =
      lieStructureConstants b i j k := by
  unfold lieStructureConstants
  rw [supportedQuotientBasis_apply, supportedQuotientBasis_apply]
  change (supportedQuotientBasis b I.toSubmodule S hI).repr
    (I.toSubmodule.mkQ ⁅b i, b j⁆) k = _
  exact supportedQuotientBasis_repr_mk b I.toSubmodule S hI _ k

theorem supportedQuotientBasis_projection_height (b : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (S : Set ι) (hI : I.toSubmodule = Submodule.span ℚ (b '' S))
    (i : ι) (j : {i // i ∉ S}) :
    RationalHeightLE ((supportedQuotientBasis b I.toSubmodule S hI).repr
      (lieQuotientMap I (b i)) j) 1 := by
  change RationalHeightLE ((supportedQuotientBasis b I.toSubmodule S hI).repr
    (I.toSubmodule.mkQ (b i)) j) 1
  rw [supportedQuotientBasis_repr_mk]
  exact basis_repr_height_one b i j

namespace NilpotentLieFiltration

variable {s t : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
  (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule)
  (S : Set ι) (hspan : I.toSubmodule = Submodule.span ℚ (b '' S))

include hlayers in
theorem supportedQuotientBasis_layers (j : ℕ) :
    (F.quotientLie I hI).layer j = Submodule.span ℚ
      (supportedQuotientBasis b I.toSubmodule S hspan '' {i | j ≤ w i}) := by
  change (F.layer j).map I.toSubmodule.mkQ = _
  rw [hlayers j]
  exact supportedQuotientBasis_map_span b I.toSubmodule S hspan {i | j ≤ w i}

end NilpotentLieFiltration
end Erdos3

end

end OAI
