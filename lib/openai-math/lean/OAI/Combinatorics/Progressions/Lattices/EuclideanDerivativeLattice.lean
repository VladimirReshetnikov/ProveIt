import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Prod
import OAI.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates
import OAI.Combinatorics.Progressions.Linear.ShortVectorProjection
import OAI.Combinatorics.Progressions.Sampling.DerivativeGridPoints

namespace OAI

section

namespace Erdos3

noncomputable def coordinateScaleEquiv {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x i := d i * x i
  invFun x i := x i / d i
  left_inv x := by funext i; exact mul_div_cancel_left₀ (x i) (hd i)
  right_inv x := by funext i; exact mul_div_cancel₀ (x i) (hd i)
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' c x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem coordinateScaleEquiv_apply {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (x : ι → ℝ) (i : ι) : coordinateScaleEquiv d hd x i = d i * x i := rfl

@[simp] theorem coordinateScaleEquiv_symm_apply {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (x : ι → ℝ) (i : ι) : (coordinateScaleEquiv d hd).symm x i = x i / d i := rfl

noncomputable def derivativeShearEquiv {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (Y : E →ₗ[ℝ] F) (A : F ≃ₗ[ℝ] F) :
    (E × F) ≃ₗ[ℝ] (E × F) where
  toFun x := (x.1, Y x.1 - A x.2)
  invFun x := (x.1, A.symm (Y x.1 - x.2))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · rfl
    · change Y (x.1 + y.1) - A (x.2 + y.2) = (Y x.1 - A x.2) + (Y y.1 - A y.2)
      rw [map_add, map_add]
      abel
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · rfl
    · change Y (c • x.1) - A (c • x.2) = c • (Y x.1 - A x.2)
      rw [map_smul, map_smul, smul_sub]

@[simp] theorem derivativeShearEquiv_apply {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (Y : E →ₗ[ℝ] F) (A : F ≃ₗ[ℝ] F) (x : E × F) :
    derivativeShearEquiv Y A x = (x.1, Y x.1 - A x.2) := rfl

noncomputable def derivativeLatticeEquiv {σ κ : Type*}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) :
    ((σ → ℝ) × (κ → ℝ)) ≃ₗ[ℝ] ((σ → ℝ) × (κ → ℝ)) :=
  ((LinearEquiv.refl ℝ (σ → ℝ)).prodCongr
    (coordinateScaleEquiv (fun _ : κ => (l : ℝ)⁻¹) (fun _ => inv_ne_zero (by exact_mod_cast hl.ne')))).trans
    ((derivativeShearEquiv Y A).trans
      ((coordinateScaleEquiv (fun i => (T i)⁻¹) (fun i => inv_ne_zero (hT i))).prodCongr
        (coordinateScaleEquiv scale hscale)))

theorem derivativeLatticeEquiv_apply {σ κ : Type*}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (x : (σ → ℝ) × (κ → ℝ)) :
    derivativeLatticeEquiv T hT scale hscale Y A l hl x =
      (fun i => x.1 i / T i, fun j => scale j * (Y x.1 - A (fun k => x.2 k / l)) j) := by
  simp only [derivativeLatticeEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, derivativeShearEquiv_apply]
  refine Prod.ext ?_ ?_
  · funext i
    simp only [coordinateScaleEquiv_apply, div_eq_mul_inv, mul_comm]
  · funext j
    have he : coordinateScaleEquiv (fun _ : κ => (l : ℝ)⁻¹)
        (fun _ => inv_ne_zero (by exact_mod_cast hl.ne')) x.2 = (fun k => x.2 k / l) := by
      funext k
      simp only [coordinateScaleEquiv_apply, div_eq_mul_inv, mul_comm]
    exact congrArg (fun v : κ → ℝ => scale j * (Y x.1 - A v) j) he

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def standardProductBasis :
    Basis (σ ⊕ κ) ℝ ((σ → ℝ) × (κ → ℝ)) :=
  (Pi.basisFun ℝ σ).prod (Pi.basisFun ℝ κ)

theorem standardProductBasis_mem_iff (x : (σ → ℝ) × (κ → ℝ)) :
    x ∈ Submodule.span ℤ (Set.range (standardProductBasis (σ := σ) (κ := κ))) ↔
      x.1 ∈ realIntegerGrid ∧ x.2 ∈ realIntegerGrid := by
  rw [(standardProductBasis (σ := σ) (κ := κ)).mem_span_iff_repr_mem ℤ x]
  constructor
  · intro h
    have h₁ : ∀ i : σ, ∃ n : ℤ, (n : ℝ) = x.1 i := by
      intro i
      simpa [standardProductBasis] using h (Sum.inl i)
    have h₂ : ∀ i : κ, ∃ n : ℤ, (n : ℝ) = x.2 i := by
      intro i
      simpa [standardProductBasis] using h (Sum.inr i)
    choose a ha using h₁
    choose b hb using h₂
    exact ⟨⟨a, funext ha⟩, ⟨b, funext hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ i
    cases i with
    | inl i => exact ⟨a i, by simpa [standardProductBasis] using congrFun ha i⟩
    | inr i => exact ⟨b i, by simpa [standardProductBasis] using congrFun hb i⟩

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

noncomputable def derivativeLatticeBasis : Basis (σ ⊕ κ) ℝ ((σ → ℝ) × (κ → ℝ)) :=
  standardProductBasis.map (derivativeLatticeEquiv T hT scale hscale Y A l hl)

noncomputable def derivativeLattice : Submodule ℤ ((σ → ℝ) × (κ → ℝ)) :=
  Submodule.span ℤ (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))

instance derivativeLattice_discrete : DiscreteTopology (derivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ
    (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))))

instance derivativeLattice_full : IsZLattice ℝ (derivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ
    (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))))

theorem derivativeLattice_mem_iff (v : (σ → ℝ) × (κ → ℝ)) :
    v ∈ derivativeLattice T hT scale hscale Y A l hl ↔
      ∃ h : σ → ℤ, ∃ z : κ → ℤ,
        v = derivativeLatticeEquiv T hT scale hscale Y A l hl
          (fun i => (h i : ℝ), fun j => (z j : ℝ)) := by
  change v ∈ Submodule.span ℤ (Set.range
    (standardProductBasis.map (derivativeLatticeEquiv T hT scale hscale Y A l hl))) ↔ _
  rw [← ZSpan.map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    obtain ⟨⟨h, hh⟩, ⟨z, hz⟩⟩ := (standardProductBasis_mem_iff x).mp hx
    have he : x = ((fun i => (h i : ℝ)), (fun j => (z j : ℝ))) := Prod.ext hh.symm hz.symm
    exact ⟨h, z, hxv.symm.trans (congrArg (derivativeLatticeEquiv T hT scale hscale Y A l hl) he)⟩
  · rintro ⟨h, z, rfl⟩
    refine ⟨((fun i => (h i : ℝ)), (fun j => (z j : ℝ))), ?_, rfl⟩
    exact (standardProductBasis_mem_iff _).mpr ⟨⟨h, rfl⟩, ⟨z, rfl⟩⟩

theorem derivativeLattice_carrier [DecidableEq κ] :
    (derivativeLattice T hT scale hscale Y A l hl : Set ((σ → ℝ) × (κ → ℝ))) =
      derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l := by
  ext v
  change (v ∈ derivativeLattice T hT scale hscale Y A l hl) ↔ _
  rw [derivativeLattice_mem_iff]
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  constructor
  · rintro ⟨h, z, rfl⟩
    refine ⟨h, (fun j => (z j : ℝ) / l), ⟨z, ?_⟩, ?_⟩
    · funext j
      change (z j : ℝ) = (l : ℝ) * ((z j : ℝ) / l)
      field_simp
    · simp only [derivativeLatticeEquiv_apply, derivativeGridPoint, LinearMap.toMatrix'_mulVec,
        LinearEquiv.coe_coe]
  · rintro ⟨h, r, ⟨z, hz⟩, hv⟩
    have hdiv : (fun j => (z j : ℝ) / l) = r := by
      funext j
      have hj : (z j : ℝ) = (l : ℝ) * r j := congrFun hz j
      rw [hj]
      field_simp
    refine ⟨h, z, hv.trans ?_⟩
    simp only [derivativeLatticeEquiv_apply, derivativeGridPoint, LinearMap.toMatrix'_mulVec, hdiv,
      LinearEquiv.coe_coe]

end Erdos3

end

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]

omit [DecidableEq σ] [DecidableEq κ] in
theorem derivativeGridPoint_shift_bound
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r : κ → ℝ) (R : ℝ)
    (hR : ‖derivativeGridPoint T scale Y M h r‖ ≤ R) :
    ∀ i, |(h i : ℝ)| ≤ R * T i := by
  intro i
  have hi := (norm_le_pi_norm (derivativeGridPoint T scale Y M h r).1 i).trans
    ((norm_fst_le _).trans hR)
  change ‖(h i : ℝ) / T i‖ ≤ R at hi
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hT i)] at hi
  exact (div_le_iff₀ (hT i)).mp hi

theorem derivativeLattice_shortSpan_projection
    (T : σ → ℝ) (hT : ∀ i, 1 ≤ T i)
    (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R δ : ℝ) (hR : 1 ≤ R)
    (H : Finset (σ → ℤ)) (r : (σ → ℤ) → κ → ℝ)
    (hr : ∀ h ∈ H, r h ∈ realDenominatorGrid l)
    (hnorm : ∀ h ∈ H,
      ‖derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h)‖ ≤ R)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card σ - 1) < δ * T i) :
    (shortVectorSpan (derivativeLattice T (fun i => (lt_of_lt_of_le zero_lt_one (hT i)).ne')
      scale hscale Y A l hl) R).map (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ)) = ⊤ := by
  let hT0 : ∀ i, 0 < T i := fun i => lt_of_lt_of_le zero_lt_one (hT i)
  let e := coordinateScaleEquiv T (fun i => (hT0 i).ne')
  let π := e.toLinearMap.comp (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ))
  let Λ := derivativeLattice T (fun i => (hT0 i).ne') scale hscale Y A l hl
  have hmap : (shortVectorSpan Λ R).map π = ⊤ := by
    apply shortVectorSpan_map_eq_top_of_dense_integer_images Λ π H T R δ hT hR
      (fun h hh => derivativeGridPoint_shift_bound T hT0 scale Y _ h (r h) R (hnorm h hh))
      hdense hlarge
    intro h hh
    refine ⟨derivativeGridPoint T scale Y (LinearMap.toMatrix' A.toLinearMap) h (r h),
      ?_, hnorm h hh, ?_⟩
    · change _ ∈ Λ
      rw [← SetLike.mem_coe, derivativeLattice_carrier]
      exact derivativeGridPoint_mem T scale Y _ l h (r h) (hr h hh)
    · funext i
      change T i * ((h i : ℝ) / T i) = (h i : ℝ)
      exact mul_div_cancel₀ (h i : ℝ) (hT0 i).ne'
  have hmap' : ((shortVectorSpan Λ R).map (LinearMap.fst ℝ (σ → ℝ) (κ → ℝ))).map
      e.toLinearMap = ⊤ := by
    simpa only [← Submodule.map_comp] using hmap
  exact (Submodule.map_eq_top_iff (e := e)).mp hmap'

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ κ : Type*} [Fintype σ] [Fintype κ]
  (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

noncomputable def euclideanDerivativeLatticeBasis :
    Basis (σ ⊕ κ) ℝ (EuclideanSpace ℝ (σ ⊕ κ)) :=
  (derivativeLatticeBasis T hT scale hscale Y A l hl).map productEuclideanEquiv

noncomputable def euclideanDerivativeLattice : Submodule ℤ (EuclideanSpace ℝ (σ ⊕ κ)) :=
  Submodule.span ℤ (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))

instance euclideanDerivativeLattice_discrete :
    DiscreteTopology (euclideanDerivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ
    (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))))

instance euclideanDerivativeLattice_full :
    IsZLattice ℝ (euclideanDerivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ
    (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))))

theorem euclideanDerivativeLattice_mem_iff (v : EuclideanSpace ℝ (σ ⊕ κ)) :
    v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ↔
      productEuclideanEquiv.symm v ∈ derivativeLattice T hT scale hscale Y A l hl := by
  change v ∈ Submodule.span ℤ (Set.range
    ((derivativeLatticeBasis T hT scale hscale Y A l hl).map productEuclideanEquiv)) ↔ _
  rw [← ZSpan.map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    change productEuclideanEquiv x = v at hxv
    rw [← hxv, LinearEquiv.symm_apply_apply]
    exact hx
  · intro hv
    exact ⟨productEuclideanEquiv.symm v, hv, productEuclideanEquiv.apply_symm_apply v⟩

theorem productEuclideanEquiv_mem_derivativeLattice (v : (σ → ℝ) × (κ → ℝ)) :
    productEuclideanEquiv v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ↔
      v ∈ derivativeLattice T hT scale hscale Y A l hl := by
  rw [euclideanDerivativeLattice_mem_iff, LinearEquiv.symm_apply_apply]

theorem exists_bounded_euclideanDerivativeLattice_family [DecidableEq κ]
    (R : ℝ) (P : Finset ((σ → ℝ) × (κ → ℝ)))
    (hP : ∀ v ∈ P,
      v ∈ derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l ∧ ‖v‖ ≤ R) :
    ∃ Q : Finset (EuclideanSpace ℝ (σ ⊕ κ)), Q.card = P.card ∧
      ∀ v ∈ Q, v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ∧
        ‖v‖ ≤ ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R := by
  classical
  refine ⟨P.image productEuclideanEquiv, Finset.card_image_of_injective _
    productEuclideanEquiv.injective, ?_⟩
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  constructor
  · apply (productEuclideanEquiv_mem_derivativeLattice T hT scale hscale Y A l hl w).mpr
    rw [← SetLike.mem_coe, derivativeLattice_carrier]
    exact (hP w hw).1
  · exact (productEuclideanEquiv_norm_le w).trans
      (mul_le_mul_of_nonneg_left (hP w hw).2 (Nat.cast_nonneg _))

end Erdos3

end

end OAI
