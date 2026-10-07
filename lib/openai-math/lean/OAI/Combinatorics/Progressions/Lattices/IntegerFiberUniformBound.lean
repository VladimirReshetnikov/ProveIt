import OAI.Combinatorics.Progressions.Estimates.PivotJacobianBound
import OAI.Combinatorics.Progressions.Sampling.PivotGridErrorTransfer

namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def normalizedIntegerColumns (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ) :
    Matrix I J ℝ :=
  Matrix.diagonal (fun i => (P i)⁻¹) * B.map (Int.castRingHom ℝ) * Matrix.diagonal T

theorem normalizedIntegerColumns_mulVec (B : Matrix I J ℤ) (T : J → ℝ) (P : I → ℝ)
    (hT : ∀ j, T j ≠ 0) (y : J → ℤ) :
    normalizedIntegerColumns B T P *ᵥ (fun j => (y j : ℝ) / T j) =
      fun i => ((B *ᵥ y) i : ℝ) / P i := by
  have hc : Matrix.diagonal T *ᵥ (fun j => (y j : ℝ) / T j) = fun j => (y j : ℝ) := by
    funext j
    simp only [Matrix.mulVec_diagonal]
    field_simp [hT j]
  unfold normalizedIntegerColumns
  rw [← Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  funext i
  simp only [Matrix.mulVec_diagonal]
  have hcast : ((B *ᵥ y) i : ℝ) = (B.map (Int.castRingHom ℝ) *ᵥ fun j => (y j : ℝ)) i :=
    (Int.castRingHom ℝ).map_mulVec B y i
  rw [← hcast, div_eq_mul_inv]
  ring

noncomputable def normalizedPivotEquiv (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (I → ℝ) ≃L[ℝ] (I → ℝ) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose

theorem normalizedPivotEquiv_coe (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap =
      matrixSupCLM (normalizedIntegerPivot A S P) :=
  (matrixSupCLM_inverse_spec (normalizedIntegerPivot A S P)
    (normalizedIntegerPivot_det_ne_zero A hA S P hS hP)).1.choose_spec

theorem normalizedPivotEquiv_inverseJacobian (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    inverseJacobian (normalizedPivotEquiv A hA S P hS hP) =
      |(normalizedIntegerPivot A S P).det|⁻¹ := by
  rw [inverseJacobian_eq]
  have he := congrArg ContinuousLinearMap.toLinearMap (normalizedPivotEquiv_coe A hA S P hS hP)
  change (normalizedPivotEquiv A hA S P hS hP).toLinearEquiv.toLinearMap =
    (normalizedIntegerPivot A S P).mulVecLin at he
  rw [he, ← Matrix.toLin'_apply', LinearMap.det_toLin']

theorem scaledIntegerFiber_graph (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 < T j) {x : I → ℤ} {y : J → ℤ} {v : I → ℤ}
    (hxy : A *ᵥ x + B *ᵥ y = v) :
    (fun i => (x i : ℝ) / S i) = (normalizedPivotEquiv A hA S P hS hP).symm
      ((fun i => (v i : ℝ) / P i) -
        matrixSupCLM (normalizedIntegerColumns B T P) (fun j => (y j : ℝ) / T j)) := by
  apply (normalizedPivotEquiv A hA S P hS hP).injective
  rw [ContinuousLinearEquiv.apply_symm_apply]
  change (normalizedPivotEquiv A hA S P hS hP).toContinuousLinearMap _ = _
  rw [normalizedPivotEquiv_coe, matrixSupCLM_apply, matrixSupCLM_apply]
  change normalizedIntegerColumns A S P *ᵥ _ = _
  rw [normalizedIntegerColumns_mulVec A S P (fun i => (hS i).ne') x,
    normalizedIntegerColumns_mulVec B T P (fun j => (hT j).ne') y]
  funext i
  have hi := congrFun hxy i
  have hi' : ((A *ᵥ x) i : ℝ) + ((B *ᵥ y) i : ℝ) = v i := by exact_mod_cast hi
  change ((A *ᵥ x) i : ℝ) / P i = (v i : ℝ) / P i - ((B *ᵥ y) i : ℝ) / P i
  rw [← sub_div, ← hi']
  congr 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def scaledIntegerWeight (f : (J → ℝ) × (I → ℝ) → ℝ)
    (S : I → ℝ) (T : J → ℝ) (p : (I → ℤ) × (J → ℤ)) : ℝ :=
  f ((fun j => (p.2 j : ℝ) / T j), (fun i => (p.1 i : ℝ) / S i))

theorem scaledIntegerWeight_eq_slice (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (hT : ∀ j, 0 < T j) (f : (J → ℝ) × (I → ℝ) → ℝ)
    {p : (I → ℤ) × (J → ℤ)} {v : I → ℤ} (hp : A *ᵥ p.1 + B *ᵥ p.2 = v) :
    scaledIntegerWeight f S T p =
      pivotSliceProfile (normalizedPivotEquiv A hA S P hS hP)
        (matrixSupCLM (normalizedIntegerColumns B T P)) f (fun i => (v i : ℝ) / P i)
        (fun j => (p.2 j : ℝ) / T j) := by
  unfold scaledIntegerWeight pivotSliceProfile
  rw [scaledIntegerFiber_graph A hA B S P T hS hP hT hp]

omit [DecidableEq J] in
theorem integerFiber_free_injective (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) :
    Function.Injective (fun p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} => p.val.2) := by
  intro p q hpq
  change p.val.2 = q.val.2 at hpq
  apply Subtype.ext
  apply Prod.ext
  · apply Matrix.mulVec_injective_of_det_ne_zero hA
    have he := p.property.trans q.property.symm
    rw [hpq] at he
    exact add_right_cancel he
  · exact hpq

theorem scaledIntegerWeight_fiber_summable (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (B : Matrix I J ℤ) (v : I → ℤ) (S P : I → ℝ) (T : J → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {R : ℝ} (hsupport : ∀ p, R < ‖p‖ → f p = 0) :
    Summable (fun p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} =>
      scaledIntegerWeight f S T p.val) := by
  let g := pivotSliceProfile (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P)) f (fun i => (v i : ℝ) / P i)
  have hg : ∀ y, R < ‖y‖ → g y = 0 :=
    pivotSliceProfile_zero_outside _ _ hsupport _
  have hs : Summable (fun y : J → ℤ => g (fun j => (y j : ℝ) / T j)) := by
    simpa only [zero_add, one_mul] using
      scaledRectangularWeight_summable g (fun _ => 0) T (m := 1) zero_lt_one hT hg
  apply (hs.comp_injective (integerFiber_free_injective A hA B v)).congr
  intro p
  exact (scaledIntegerWeight_eq_slice A hA B S P T hS hP hT f p.property).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Matrix BigOperators NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

noncomputable def scaledIntegerFiberOutputMass (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ) : ℝ :=
  ((∏ i, P i) / ((∏ i, S i) * (∏ j, T j))) *
    ∑' p : {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v}, scaledIntegerWeight f S T p.val

noncomputable def normalizedFiberDensity (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) × (I → ℝ) → ℝ) : (I → ℝ) → ℝ :=
  pivotOutputDensity (normalizedPivotEquiv A hA S P hS hP)
    (matrixSupCLM (normalizedIntegerColumns B T P)) f

theorem integerFiber_grid_error (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (y₀ : J → ℤ) (hy₀ : pivotFreeAdmissible A B v y₀)
    {m : ℤ} (hm : 0 < m) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, (m : ℝ) / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (r : integerLatticeResidue (pivotFreeLattice A B) m) :
    let e := normalizedPivotEquiv A hA S P hS hP
    let b := matrixSupCLM (normalizedIntegerColumns B T P)
    |((m.natAbs : ℝ) ^ Fintype.card J / (∏ j, T j)) *
      (∑' z : J → ℤ, scaledIntegerWeight f S T
        ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm.ne' hdiv).symm (r, z)).val) -
      ∫ y, pivotSliceProfile e b f (fun i => (v i : ℝ) / P i) y| ≤
      (2 * R + 2) ^ Fintype.card J * ((K * pivotGraphLipschitz e b : ℝ≥0) : ℝ) * δ := by
  let e := normalizedPivotEquiv A hA S P hS hP
  let b := matrixSupCLM (normalizedIntegerColumns B T P)
  let g := pivotSliceProfile e b f (fun i => (v i : ℝ) / P i)
  let c : J → ℝ := fun j => ((y₀ j + r.out.val j : ℤ) : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq (z : J → ℤ) : scaledIntegerWeight f S T
      ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm.ne' hdiv).symm (r, z)).val =
      g (fun j => (c j + (m : ℝ) * z j) / T j) := by
    rw [scaledIntegerWeight_eq_slice A hA B S P T hS hP hT f
      ((pivotFiberGridEquiv A hA B v y₀ hy₀ hm.ne' hdiv).symm (r, z)).property]
    change g _ = g _
    congr 1
    rw [pivotFiberGridEquiv_free]
    funext j
    simp only [c, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add, Int.cast_mul]
  have hq := scaledRectangular_quadrature g (pivotSliceProfile_lipschitz e b hf _)
    c T hmR hT hR hδ hδ1 hmesh (pivotSliceProfile_zero_outside e b hsupport _)
  have habs : (m.natAbs : ℝ) = m := by
    rw [Nat.cast_natAbs, abs_of_pos hm]
  simp_rw [heq, habs]
  exact hq

theorem integerFiber_quadrature (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    {m : ℤ} (hm : 0 < m) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, (m : ℝ) / T j ≤ δ)
    (hsupport : ∀ p, R < ‖p‖ → f p = 0) :
    let e := normalizedPivotEquiv A hA S P hS hP
    let b := matrixSupCLM (normalizedIntegerColumns B T P)
    |scaledIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      (((pivotFullImage A B).toAddSubgroup.index : ℝ) / |(normalizedIntegerPivot A S P).det|) *
        ((2 * R + 2) ^ Fintype.card J * ((K * pivotGraphLipschitz e b : ℝ≥0) : ℝ) * δ) := by
  obtain ⟨x₀, y₀, hxy⟩ := (pivotFullImage_iff A B v).mp hv
  have hy₀ := (pivotFreeAdmissible_iff A B v y₀).mpr ⟨x₀, hxy⟩
  have ht := pivotFiber_error_of_grid_errors A hA B v y₀ hy₀ hm.ne' hdiv S P T hS hP hT
    (scaledIntegerWeight f S T) (scaledIntegerWeight_fiber_summable A hA B v S P T hS hP hT f hsupport)
    (integerFiber_grid_error A hA B v y₀ hy₀ hm hdiv S P T hS hP hT f hf hR hδ hδ1 hmesh hsupport)
  dsimp only
  unfold scaledIntegerFiberOutputMass normalizedFiberDensity
  rw [pivotOutputDensity_slice_formula, normalizedPivotEquiv_inverseJacobian]
  simpa only [div_eq_mul_inv, mul_assoc] using ht

omit [DecidableEq I] [DecidableEq J] in
theorem scaledIntegerFiberOutputMass_zero_off_image (A : Matrix I I ℤ) (B : Matrix I J ℤ)
    (S P : I → ℝ) (T : J → ℝ) (f : (J → ℝ) × (I → ℝ) → ℝ) (v : I → ℤ)
    (hv : v ∉ pivotFullImage A B) : scaledIntegerFiberOutputMass A B S P T f v = 0 := by
  have hempty : IsEmpty {p : (I → ℤ) × (J → ℤ) // A *ᵥ p.1 + B *ᵥ p.2 = v} :=
    ⟨fun p => hv ((pivotFullImage_iff A B v).mpr ⟨p.val.1, p.val.2, p.property⟩)⟩
  simp only [scaledIntegerFiberOutputMass, tsum_empty, mul_zero]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

noncomputable def integerFiberErrorConstant (j d : ℕ) (G U V R : ℝ) (K : ℝ≥0) : ℝ :=
  G * (j.factorial * U ^ j) * (2 * R + 2) ^ d * K * max 1 (U * V)

theorem integerFiberErrorConstant_nonneg (j d : ℕ) {G U V R : ℝ} (K : ℝ≥0)
    (hG : 0 ≤ G) (hU : 0 ≤ U) (hR : 0 ≤ R) :
    0 ≤ integerFiberErrorConstant j d G U V R K := by
  unfold integerFiberErrorConstant
  positivity

theorem integerFiber_uniform_quadrature {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I I ℤ) (hA : A.det ≠ 0) (B : Matrix I J ℤ)
    (v : I → ℤ) (hv : v ∈ pivotFullImage A B)
    {m : ℤ} (hm : 0 < m) (hdiv : A.det ∣ m)
    (S P : I → ℝ) (T : J → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) (hT : ∀ j, 0 < T j)
    (f : (J → ℝ) × (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R δ G U V : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hmesh : ∀ j, (m : ℝ) / T j ≤ δ) (hsupport : ∀ p, R < ‖p‖ → f p = 0)
    (hindex : ((pivotFullImage A B).toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(normalizedPivotEquiv A hA S P hS hP).symm.toContinuousLinearMap‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns B T P)‖ ≤ V) :
    |scaledIntegerFiberOutputMass A B S P T f v -
        ((pivotFullImage A B).toAddSubgroup.index : ℝ) *
          normalizedFiberDensity A hA B S P T hS hP f (fun i => (v i : ℝ) / P i)| ≤
      integerFiberErrorConstant (Fintype.card I) (Fintype.card J) G U V R K * δ := by
  let e := normalizedPivotEquiv A hA S P hS hP
  let b := matrixSupCLM (normalizedIntegerColumns B T P)
  have hU : 0 ≤ U := (norm_nonneg _).trans hinv
  have hG : 0 ≤ G := (Nat.cast_nonneg _).trans hindex
  have hJ := inverseJacobian_le_norm_bound e hinv
  have hgraph := pivotGraphLipschitz_le_norm_bounds e b hinv hcol
  have hJac : |(normalizedIntegerPivot A S P).det|⁻¹ = inverseJacobian e :=
    (normalizedPivotEquiv_inverseJacobian A hA S P hS hP).symm
  have ht := integerFiber_quadrature A hA B v hv hm hdiv S P T hS hP hT f hf
    hR hδ hδ1 hmesh hsupport
  dsimp only at ht
  rw [div_eq_mul_inv, hJac] at ht
  have houter : ((pivotFullImage A B).toAddSubgroup.index : ℝ) * inverseJacobian e ≤
      G * ((Fintype.card I).factorial * U ^ Fintype.card I) :=
    mul_le_mul hindex hJ (inverseJacobian_pos e).le hG
  have hinner : (2 * R + 2) ^ Fintype.card J * ((K * pivotGraphLipschitz e b : ℝ≥0) : ℝ) * δ ≤
      (2 * R + 2) ^ Fintype.card J * ((K : ℝ) * max 1 (U * V)) * δ := by
    apply mul_le_mul_of_nonneg_right _ hδ
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left hgraph K.coe_nonneg
  calc
    _ ≤ _ := ht
    _ ≤ (G * ((Fintype.card I).factorial * U ^ Fintype.card I)) *
        ((2 * R + 2) ^ Fintype.card J * ((K : ℝ) * max 1 (U * V)) * δ) :=
      mul_le_mul houter hinner (by positivity) (by positivity)
    _ = _ := by unfold integerFiberErrorConstant; ring

end Erdos3

end

end OAI
