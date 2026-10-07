import OAI.Combinatorics.Progressions.Probability.ShiftedProductCoordinateLaw

namespace OAI


namespace Erdos3

theorem enormousCoefficient_mesh_conditions {j h : ℕ} {D Z L H : ℝ}
    (hD : 0 ≤ D) (hZ : 0 ≤ Z) (hL : 0 < L) (hH : 0 < H)
    (hlarge : 2 * (1 + Z) * D * L ^ (h * (j + 1)) ≤ H) :
    D * L ^ (h * j) ≤ H / L ^ h ∧
      Z * (D * L ^ (h * j) / (H / L ^ h)) ≤ 1 / 2 := by
  have hp : L ^ (h * (j + 1)) = L ^ (h * j) * L ^ h := by
    rw [Nat.mul_add, Nat.mul_one, pow_add]
  have hprod : D * L ^ (h * j) * L ^ h ≤ H := by
    rw [hp] at hlarge
    have hnon : 0 ≤ D * L ^ (h * j) * L ^ h := by positivity
    nlinarith
  refine ⟨(le_div_iff₀ (pow_pos hL h)).mpr hprod, ?_⟩
  have he : Z * (D * L ^ (h * j) / (H / L ^ h)) =
      Z * D * L ^ (h * (j + 1)) / H := by rw [hp]; field_simp
  rw [he]
  apply (div_le_iff₀ hH).mpr
  have hnon : 0 ≤ D * L ^ (h * (j + 1)) := by positivity
  nlinarith

theorem enormousCoefficient_error_rate {j h : ℕ} (C L H : ℝ) :
    C * L ^ (h * j) / (H / L ^ h) = C * L ^ (h * (j + 1)) / H := by
  rw [Nat.mul_add, Nat.mul_one, pow_add, div_div_eq_mul_div]
  ring


open MeasureTheory
open scoped BigOperators NNReal

noncomputable def coefficientImageMask {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ) (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ A.mulVecLin.range then
    (A.mulVecLin.range.toAddSubgroup.index : ℝ) * f (fun i => (v i : ℝ) / P i) else 0

noncomputable def selectedCoefficientDensity {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) : (I → ℝ) → ℝ :=
  normalizedFiberDensity (A.submatrix id s) hA (remainingMatrixColumns A s)
    (fun i => S (s i)) P (fun j => S j.val) (fun i => hS (s i)) hP (selectedCoefficientProfile s f)

theorem selectedCoefficient_mask {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (s : I ↪ J) (P : I → ℝ) (f : (I → ℝ) → ℝ) :
    maskedIntegerImageDensity (A.submatrix id s) (remainingMatrixColumns A s) P f =
      coefficientImageMask A P f := by
  classical
  funext v
  simp only [maskedIntegerImageDensity, coefficientImageMask, selectedMatrix_full_image]

theorem coefficientImage_polynomial_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U V C L ρ H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hρ : 0 < ρ) (hH : 0 ≤ H)
    (hscale : ∀ j, ρ ≤ S j) (hsmall : ((A.submatrix id s).det.natAbs : ℝ) ≤ ρ)
    (hcoeff : ∀ i j, |(A i (s j) : ℝ)| ≤ C * L ^ h)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K *
      (((A.submatrix id s).det.natAbs : ℝ) / ρ) ≤ 1 / 2)
    (hbound : ∀ x, ‖f x‖ ≤ H) (hindex : (A.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
      (fun i => S (s i)) P)).inverse‖ ≤ U)
    (hcol : ‖matrixSupCLM (normalizedIntegerColumns (remainingMatrixColumns A s)
      (fun j => S j.val) P)‖ ≤ V) :
    ∃ hZ : 0 < coefficientWeightSum f S, ∀ v,
      |(∏ i, P i) * (coefficientImagePMF A f hf0 S hS hsupport hZ v).toReal -
        coefficientImageMask A P (selectedCoefficientDensity A s hA S P hS hP f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U V R H K * ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * Fintype.card I) / ρ := by
  classical
  have hmass' : (∫ p, selectedCoefficientProfile s f p) = 1 :=
    (selectedCoefficientProfile_integral s f).trans hmass
  have hindex' := hindex
  rw [← selectedMatrix_full_image A s] at hindex'
  obtain ⟨hM, herror⟩ := normalizedIntegerImage_polynomial_error (U := U)
    (A.submatrix id s) hA (remainingMatrixColumns A s)
    (fun i => S (s i)) P (fun j => S j.val) (fun i => hS (s i)) hP (fun j => hS j.val)
    (selectedCoefficientProfile s f) (selectedCoefficientProfile_nonneg s hf0)
    (selectedCoefficientProfile_lipschitz s hf) h hR hρ hH
    (fun i => hscale (s i)) (fun j => hscale j.val) hsmall hcoeff
    (selectedCoefficientProfile_zero_outside s hsupport) hmass' hsmallMass
    (selectedCoefficientProfile_norm_le s hbound) hindex'
    (by rwa [normalizedPivotEquiv_inverse_eq]) hcol
  refine ⟨selectedCoefficient_weight_sum_pos s f S hS hM, fun v => ?_⟩
  have he := herror v
  rw [selectedCoefficient_image_law A s f hf0 S hS hsupport hM, selectedCoefficient_mask] at he
  exact he

end Erdos3


namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem coefficientImage_enormous_error {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (S : J → ℝ) (hS : ∀ j, 0 < S j)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R G U C L Hcap H : ℝ} (h : ℕ) (hR : 0 ≤ R) (hL : 0 < L)
    (hH : 0 < H) (hcap : 0 ≤ Hcap) (hC : 0 ≤ C)
    (hscale : ∀ j, H / L ^ h ≤ S j)
    (hcoeff : ∀ i j, |(A i (s j) : ℝ)| ≤ C * L ^ h)
    (hentry : ∀ i j, |normalizedIntegerColumns A S (fun _ => H) i j| ≤ C)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hbound : ∀ x, ‖f x‖ ≤ Hcap) (hindex : (A.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G)
    (hinv : ‖(matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
      (fun i => S (s i)) (fun _ => H))).inverse‖ ≤ U)
    (hlarge : 2 * (1 + (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K) *
      ((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * (Fintype.card I + 1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum f S, ∀ v,
      |H ^ Fintype.card I * (coefficientImagePMF A f hf0 S hS hsupport hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s hA S (fun _ => H) hS (fun _ => hH) f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U (Fintype.card (UnselectedColumn s) * C) R Hcap K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * (Fintype.card I + 1)) / H := by
  classical
  have hρ : 0 < H / L ^ h := div_pos hH (pow_pos hL h)
  have hm := enormousCoefficient_mesh_conditions (j := Fintype.card I) (h := h)
    (D := (Fintype.card I).factorial * C ^ Fintype.card I)
    (Z := (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K)
    (by positivity) (by positivity) hL hH hlarge
  have hd := integerPivot_polynomial_period_bound (A.submatrix id s) h hcoeff
  have hsmall := hd.trans hm.1
  have hsmallMass : (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K *
      (((A.submatrix id s).det.natAbs : ℝ) / (H / L ^ h)) ≤ 1 / 2 := by
    apply le_trans _ hm.2
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hd hρ.le) (by positivity)
  obtain ⟨hZ, he⟩ := coefficientImage_polynomial_error A s hA S (fun _ => H) hS (fun _ => hH)
    f hf0 hf h hR hρ hcap hscale hsmall hcoeff hsupport hmass hsmallMass hbound hindex hinv
    (normalized_remainingMatrixColumns_norm A s S (fun _ => H) hC hentry)
  refine ⟨hZ, fun v => ?_⟩
  simpa only [Finset.prod_const, Finset.card_univ, enormousCoefficient_error_rate] using he v

end Erdos3


namespace Erdos3

noncomputable def coefficientImageMultiplier {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) : ℝ := by
  classical
  exact if v ∈ A.mulVecLin.range then (A.mulVecLin.range.toAddSubgroup.index : ℝ) else 0

theorem coefficientImageMask_eq_multiplier {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (P : I → ℝ) (f : (I → ℝ) → ℝ) (v : I → ℤ) :
    coefficientImageMask A P f v = coefficientImageMultiplier A v * f (fun i => (v i : ℝ)/P i) := by
  classical
  by_cases hv : v ∈ A.mulVecLin.range <;> simp [coefficientImageMask, coefficientImageMultiplier, hv]

theorem coefficientImageMultiplier_nonneg {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) : 0 ≤ coefficientImageMultiplier A v := by
  classical
  unfold coefficientImageMultiplier
  split <;> positivity

theorem coefficientImageMultiplier_le_index {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) :
    coefficientImageMultiplier A v ≤ (A.mulVecLin.range.toAddSubgroup.index : ℝ) := by
  classical
  unfold coefficientImageMultiplier
  split <;> simp

theorem integerFromCols_image_eq_of_kernel_residues {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) (C D : Matrix I N ℤ) (m : ℕ)
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hCD : integerResidueMatrix C m = integerResidueMatrix D m) :
    (Matrix.fromCols A C).mulVecLin.range = (Matrix.fromCols A D).mulVecLin.range := by
  apply integerMatrixImage_eq_of_residueMatrix _ _ m
  · rw [integerMatrix_fromCols_range]
    exact hperiod.trans le_sup_left
  · rw [integerMatrix_fromCols_range]
    exact hperiod.trans le_sup_left
  · simp only [integerResidueMatrix_fromCols, hCD]

noncomputable def coefficientResidueMultiplier {I J N : Type*} [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) {m : ℕ} (r : Matrix I N (ZMod m)) (v : I → ℤ) : ℝ :=
  coefficientImageMultiplier (Matrix.fromCols A (liftResidueMatrix r)) v

theorem coefficientImageMultiplier_eq_residue {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hr : integerResidueMatrix C m = r) (v : I → ℤ) :
    coefficientImageMultiplier (Matrix.fromCols A C) v = coefficientResidueMultiplier A r v := by
  classical
  have he := integerFromCols_image_eq_of_kernel_residues A C (liftResidueMatrix r) m hperiod
    (by rw [liftResidueMatrix_residue, hr])
  unfold coefficientImageMultiplier coefficientResidueMultiplier
  simp only [coefficientImageMultiplier, he]

theorem coefficientResidueMultiplier_bounds {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (m : ℕ) (r : Matrix I N (ZMod m))
    (hperiod : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hr : integerResidueMatrix C m = r) {G : ℝ}
    (hG : ((Matrix.fromCols A C).mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G) (v : I → ℤ) :
    0 ≤ coefficientResidueMultiplier A r v ∧ coefficientResidueMultiplier A r v ≤ G := by
  rw [← coefficientImageMultiplier_eq_residue A C m r hperiod hr v]
  exact ⟨coefficientImageMultiplier_nonneg _ _, (coefficientImageMultiplier_le_index _ _).trans hG⟩

theorem monomialCoefficientMatrix_residue_eq {α K I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (vertices vertices' : Finset α → K → ℤ) (rows : I → Finset α) (m : ℕ)
    (hv : ∀ t, integerResidueMap K m (vertices t) = integerResidueMap K m (vertices' t)) :
    integerResidueMatrix (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices rows) m =
      integerResidueMatrix (integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) vertices' rows) m :=
  integerJetMatrix_residue_eq _ _ _ _ _ (fun _ t _ => hv t)


open MeasureTheory
open scoped BigOperators NNReal

structure CoefficientFiberControl {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (H L : ℝ) (h : ℕ) (C U G : ℝ) : Prop where
  det_ne_zero : (A.submatrix id s).det ≠ 0
  scale_lower : ∀ j, H / L ^ h ≤ S j
  integer_entry_bound : ∀ i j, |(A i (s j) : ℝ)| ≤ C * L ^ h
  normalized_entry_bound : ∀ i j, |normalizedIntegerColumns A S (fun _ => H) i j| ≤ C
  inverse_bound : ‖(matrixSupCLM (normalizedIntegerPivot (A.submatrix id s)
    (fun i => S (s i)) (fun _ => H))).inverse‖ ≤ U
  index_bound : (A.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ G

theorem coefficientImage_enormous_of_control {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (A : Matrix I J ℤ) (s : I ↪ J) (S : J → ℝ) (hS : ∀ j, 0 < S j)
    {H L C U G : ℝ} (h : ℕ) (ctrl : CoefficientFiberControl A s S H L h C U G)
    (hL : 0 < L) (hH : 0 < H) (hC : 0 ≤ C)
    (f : (J → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {K : ℝ≥0} (hf : LipschitzWith K f)
    {R Hcap : ℝ} (hR : 0 ≤ R) (hcap : 0 ≤ Hcap)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hbound : ∀ x, ‖f x‖ ≤ Hcap)
    (hlarge : 2 * (1 + (2 * R + 2) ^ (Fintype.card I + Fintype.card (UnselectedColumn s)) * K) *
      ((Fintype.card I).factorial * C ^ Fintype.card I) * L ^ (h * (Fintype.card I + 1)) ≤ H) :
    ∃ hZ : 0 < coefficientWeightSum f S, ∀ v,
      |H ^ Fintype.card I * (coefficientImagePMF A f hf0 S hS hsupport hZ v).toReal -
        coefficientImageMask A (fun _ => H)
          (selectedCoefficientDensity A s ctrl.det_ne_zero S (fun _ => H) hS (fun _ => hH) f) v| ≤
      (normalizedFiberErrorConstant (Fintype.card I) (Fintype.card (UnselectedColumn s))
        G U (Fintype.card (UnselectedColumn s) * C) R Hcap K *
        ((Fintype.card I).factorial * C ^ Fintype.card I)) *
          L ^ (h * (Fintype.card I + 1)) / H :=
  coefficientImage_enormous_error A s ctrl.det_ne_zero S hS f hf0 hf h hR hL hH hcap hC
    ctrl.scale_lower ctrl.integer_entry_bound ctrl.normalized_entry_bound hsupport hmass
    hbound ctrl.index_bound ctrl.inverse_bound hlarge

end Erdos3


namespace Erdos3

theorem coefficientImageMultiplier_eq_of_output_residue
    {I J : Type*} [Fintype I] [Fintype J]
    (A : Matrix I J ℤ) (period : ℕ)
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range)
    (v w : I → ℤ) (hvw : integerResidueMap I period v = integerResidueMap I period w) :
    coefficientImageMultiplier A v = coefficientImageMultiplier A w := by
  classical
  have hmem : v ∈ A.mulVecLin.range ↔ w ∈ A.mulVecLin.range := by
    simp only [integerMatrixImage_residue_iff A period hperiod, hvw]
  simp only [coefficientImageMultiplier, hmem]

theorem coefficientResidueMultiplier_eq_of_output_residue
    {I J N : Type*} [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) {modulus : ℕ} (r : Matrix I N (ZMod modulus)) (period : ℕ)
    (hperiod : integerScalarLattice I (period : ℤ) ≤ A.mulVecLin.range)
    (v w : I → ℤ) (hvw : integerResidueMap I period v = integerResidueMap I period w) :
    coefficientResidueMultiplier A r v = coefficientResidueMultiplier A r w := by
  apply coefficientImageMultiplier_eq_of_output_residue _ period _ v w hvw
  rw [integerMatrix_fromCols_range]
  exact hperiod.trans le_sup_left


theorem integerScalarLattice_le_of_dvd (I : Type*) [Fintype I]
    {a b : ℤ} (h : a ∣ b) : integerScalarLattice I b ≤ integerScalarLattice I a := by
  obtain ⟨t, rfl⟩ := h
  rintro v ⟨z, rfl⟩
  refine ⟨t • z, ?_⟩
  change a • (t • z) = (a*t) • z
  rw [mul_smul]

theorem integerScalarLattice_nat_refinement (I : Type*) [Fintype I]
    {m n : ℕ} (h : m ∣ n) : integerScalarLattice I (n : ℤ) ≤ integerScalarLattice I (m : ℤ) :=
  integerScalarLattice_le_of_dvd I (by exact_mod_cast h)

theorem coefficientResidueMultiplier_eq_of_periods {I J N : Type*}
    [Fintype I] [Fintype J] [Fintype N]
    (A : Matrix I J ℤ) (C : Matrix I N ℤ) (m n : ℕ)
    (r : Matrix I N (ZMod m)) (s : Matrix I N (ZMod n))
    (hm : integerScalarLattice I (m : ℤ) ≤ A.mulVecLin.range)
    (hn : integerScalarLattice I (n : ℤ) ≤ A.mulVecLin.range)
    (hr : integerResidueMatrix C m = r) (hs : integerResidueMatrix C n = s) (v : I → ℤ) :
    coefficientResidueMultiplier A r v = coefficientResidueMultiplier A s v :=
  (coefficientImageMultiplier_eq_residue A C m r hm hr v).symm.trans
    (coefficientImageMultiplier_eq_residue A C n s hn hs v)


open scoped Matrix

variable {I I' J : Type*} [Fintype J]

theorem coefficientImageMultiplier_reindex_rows
    (e : I' ≃ I) (A : Matrix I J ℤ) (v : I → ℤ) :
    coefficientImageMultiplier (A.submatrix e id) (fun i => v (e i)) =
      coefficientImageMultiplier A v := by
  classical
  let E := (LinearEquiv.funCongrLeft ℤ ℤ e).toAddEquiv
  have hr : (A.submatrix e id).mulVecLin.range.toAddSubgroup =
      A.mulVecLin.range.toAddSubgroup.map E.toAddMonoidHom := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨A *ᵥ z, ⟨z, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
  have hi : (A.submatrix e id).mulVecLin.range.toAddSubgroup.index =
      A.mulVecLin.range.toAddSubgroup.index := by
    rw [hr]
    exact AddSubgroup.index_map_equiv _ E
  have hm : (fun i => v (e i)) ∈ (A.submatrix e id).mulVecLin.range ↔
      v ∈ A.mulVecLin.range := by
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨z, ?_⟩
      funext i
      obtain ⟨i, rfl⟩ := e.surjective i
      exact congrFun hz i
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  simp only [coefficientImageMultiplier, hm, hi]

theorem coefficientResidueMultiplier_reindex_rows {N : Type*} [Fintype N]
    (e : I' ≃ I) (A : Matrix I J ℤ) {m : ℕ} (r : Matrix I N (ZMod m)) (v : I → ℤ) :
    coefficientResidueMultiplier (A.submatrix e id) (r.submatrix e id) (fun i => v (e i)) =
      coefficientResidueMultiplier A r v := by
  exact coefficientImageMultiplier_reindex_rows e (Matrix.fromCols A (liftResidueMatrix r)) v

end Erdos3

end OAI
