import OAI.Combinatorics.Progressions.Estimates.PetalComparisonTree

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def subalgebraLayerFamily (e : Basis ι ℚ L) (v : κ → L)
    (ω : ι → ℕ) (j : ℕ) : κ ⊕ ι → L :=
  Sum.elim v (fun i => if j ≤ ω i then e i else 0)

omit [Fintype ι] in
theorem subalgebraLayerFamily_height (e : Basis ι ℚ L) (v : κ → L)
    (ω : ι → ℕ) (j : ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H) (z : κ ⊕ ι) (i : ι) :
    RationalHeightLE (e.repr (subalgebraLayerFamily e v ω j z) i) H := by
  classical
  cases z with
  | inl z => exact hv z i
  | inr z =>
    by_cases h : j ≤ ω z
    · by_cases he : z = i
      · subst i
        simpa [subalgebraLayerFamily, h] using rationalHeightLE_one hH
      · simpa [subalgebraLayerFamily, h, he] using rationalHeightLE_zero hH
    · simpa [subalgebraLayerFamily, h] using rationalHeightLE_zero hH

namespace NilpotentLieFiltration

variable {s : ℕ} (F : NilpotentLieFiltration L s)

omit [Fintype ι] in
theorem real_subalgebra_layer_eq_span (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) (j : ℕ) :
    (realificationLieSubalgebra U).toSubmodule ⊔ (F.realLayer j).toSubmodule =
      Submodule.span ℝ (Set.range (fun z => rationalLieInclusion (subalgebraLayerFamily e v ω j z))) := by
  have hlayer : Submodule.span ℚ (Set.range (fun i => if j ≤ ω i then e i else 0)) = F.layer j :=
    (span_conditional_basis e {i | j ≤ ω i}).trans (hlayers j).symm
  rw [subalgebraLayerFamily, real_span_sum_family,
    real_span_rational_family U.toSubmodule v hv,
    real_span_rational_family (F.layer j) _ hlayer]
  rfl

theorem real_subalgebra_layer_mem_iff_coordinates (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hv : Submodule.span ℚ (Set.range v) = U.toSubmodule) (j : ℕ) (x : ℝ ⊗[ℚ] L) :
    x ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j ↔
      (e.baseChange ℝ).equivFun x ∈ Submodule.span ℝ
        (Set.range (fun z i => (e.repr (subalgebraLayerFamily e v ω j z) i : ℝ))) := by
  change x ∈ (realificationLieSubalgebra U).toSubmodule.restrictScalars ℚ ⊔
    (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
  rw [← Submodule.restrictScalars_sup]
  change x ∈ (realificationLieSubalgebra U).toSubmodule ⊔ (F.realLayer j).toSubmodule ↔ _
  rw [F.real_subalgebra_layer_eq_span e ω hlayers U v hv j]
  exact real_span_family_mem_iff_coordinates e _ x

end NilpotentLieFiltration
end Erdos3

end

end OAI
