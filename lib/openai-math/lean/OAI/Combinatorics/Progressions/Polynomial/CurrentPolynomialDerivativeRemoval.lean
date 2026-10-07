import OAI.Combinatorics.Progressions.Polynomial.FormalPolynomialCorrectionStep

namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def PolynomialLiftSystem (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ k, S k = dualAdjoint P (R k)

theorem PolynomialLiftSystem.remove (P A B : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) (hSR : PolynomialLiftSystem P S R) :
    PolynomialLiftSystem (A⁻¹ * P * B⁻¹)
      (fun k => dualAdjoint A⁻¹ (S k)) (fun k => dualAdjoint B (R k)) := by
  intro k
  change dualAdjoint A⁻¹ (S k) = dualAdjoint (A⁻¹ * P * B⁻¹) (dualAdjoint B (R k))
  rw [dualAdjoint_mul, dualAdjoint_mul, dualAdjoint_inv_cancel, hSR k]

theorem PolynomialLiftSystem.real_evaluation [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (P : PolynomialGroup σ hnil) (S R : κ → VectorPolynomial σ ℚ L)
    (hSR : PolynomialLiftSystem P S R) (k : κ) (t : σ → ℝ) :
    eval₂ t (S k) = dualAdjoint (realPolynomialValueHom t P) (eval₂ t (R k)) := by
  rw [hSR k, eval₂_dualAdjoint]

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial NilpotentLieBCHGroup

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem formal_current_layer_correction_preserves_lifts (hs : 2 ≤ s)
    (V : Submodule ℚ L) (j : ℕ) (P A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.layer j)
    (S R : κ → VectorPolynomial σ ℚ L) (k : κ → L)
    (hSR : PolynomialLiftSystem P S R)
    (hS : ∀ t α, coefficients (S t - monomial 0 (k t)) α ∈ V ⊔ F.layer (j + 1))
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ F.layer (j + 1)) :
    PolynomialLiftSystem (A⁻¹ * P * B⁻¹)
        (fun t => dualAdjoint A⁻¹ (S t)) (fun t => dualAdjoint B (R t)) ∧
      ∀ t α,
        coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈ V ⊔ F.layer (j + 1) ∧
        coefficients (dualAdjoint B (R t) - monomial 0 (k t)) α ∈ V ⊔ F.layer (j + 1) := by
  have h := F.polynomialFiltration.current_layer_correction_preserves_lifts hs
    (coefficientSubmodule V) j A P B hA hB S R (fun t => monomial 0 (k t)) hSR
    (fun t => (mem_coefficient_sup_polynomialLayer F V (j + 1) _).mpr (hS t))
    (fun t => (mem_coefficient_sup_polynomialLayer F V (j + 1) _).mpr (hR t))
  refine ⟨PolynomialLiftSystem.remove P A B S R hSR, ?_⟩
  intro t α
  exact ⟨(mem_coefficient_sup_polynomialLayer F V (j + 1) _).mp (h t).2.1 α,
    (mem_coefficient_sup_polynomialLayer F V (j + 1) _).mp (h t).2.2 α⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def PolynomialLiftSystemMod (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ k, S k - dualAdjoint P (R k) ∈ coefficientSubmodule V

def PolynomialDerivativeSystemMod (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i) ∈ coefficientSubmodule V

theorem PolynomialLiftSystem.to_mod (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) (h : PolynomialLiftSystem P S R) :
    PolynomialLiftSystemMod V P S R := by
  intro k
  rw [h k, sub_self]
  exact Submodule.zero_mem _

theorem PolynomialDerivativeSystem.to_mod (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (h : PolynomialDerivativeSystem P small rational extra) :
    PolynomialDerivativeSystemMod V P small rational extra := by
  intro i
  rw [h i, sub_self]
  exact Submodule.zero_mem _

theorem PolynomialLiftSystemMod.exact_left (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (S R : κ → VectorPolynomial σ ℚ L) (h : PolynomialLiftSystemMod V P S R) :
    ∃ S₀ : κ → VectorPolynomial σ ℚ L,
      PolynomialLiftSystem P S₀ R ∧ ∀ k, S k - S₀ k ∈ coefficientSubmodule V :=
  ⟨fun k => dualAdjoint P (R k), fun _ => rfl, h⟩

theorem PolynomialDerivativeSystemMod.exact_system (V : Submodule ℚ L) (P : PolynomialGroup σ hnil)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (h : PolynomialDerivativeSystemMod V P small rational extra) :
    ∃ error : σ → VectorPolynomial σ ℚ L,
      (∀ i, error i ∈ coefficientSubmodule V) ∧
      PolynomialDerivativeSystem P small rational (fun i => extra i + error i) := by
  refine ⟨fun i => formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i), h, ?_⟩
  intro i
  change formalLogDerivative i P = small i + dualAdjoint P (rational i) +
    (extra i + (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)))
  abel

theorem PolynomialLiftSystemMod.remove (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (S R : κ → VectorPolynomial σ ℚ L) (h : PolynomialLiftSystemMod V P S R) :
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹)
      (fun k => dualAdjoint A⁻¹ (S k)) (fun k => dualAdjoint B (R k)) := by
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hA
  intro k
  change dualAdjoint A⁻¹ (S k) - dualAdjoint (A⁻¹ * P * B⁻¹) (dualAdjoint B (R k)) ∈ _
  rw [dualAdjoint_mul, dualAdjoint_mul, dualAdjoint_inv_cancel, ← dualAdjoint_sub]
  exact dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹ _ hAi (h k)

theorem PolynomialDerivativeSystemMod.remove (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (P A B : PolynomialGroup σ hnil) (hA : ∀ α, coefficients A.coord α ∈ U)
    (small rational extra : σ → VectorPolynomial σ ℚ L)
    (h : PolynomialDerivativeSystemMod V P small rational extra) :
    PolynomialDerivativeSystemMod V (A⁻¹ * P * B⁻¹)
      (fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A))
      (fun i => dualAdjoint B (rational i) - formalLogDerivative i B)
      (fun i => dualAdjoint A⁻¹ (extra i)) := by
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ U := (coefficientLieSubalgebra U).neg_mem hA
  intro i
  have herr := dualAdjoint_mem_coefficientSubmodule U V hUV A⁻¹
    (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)) hAi (h i)
  have hmem : dualAdjoint A⁻¹
      (formalLogDerivative i P - (small i + dualAdjoint P (rational i) + extra i)) ∈
      coefficientSubmodule V := herr
  change formalLogDerivative i (A⁻¹ * P * B⁻¹) -
    (dualAdjoint A⁻¹ (small i - formalLogDerivative i A) +
      dualAdjoint (A⁻¹ * P * B⁻¹) (dualAdjoint B (rational i) - formalLogDerivative i B) +
      dualAdjoint A⁻¹ (extra i)) ∈ coefficientSubmodule V
  convert hmem using 1
  rw [formalLogDerivative_remove]
  simp only [dualAdjoint_mul, dualAdjoint_add, dualAdjoint_sub, dualAdjoint_inv_cancel]
  abel

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem polynomial_grade_eq_of_sub_mem_next (j : ℕ)
    (X Y : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hXY : ∀ α, coefficients (X - Y) α ∈ F.realification.layer (j + 1)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) Y := by
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  rw [coefficients_map, coefficients_map]
  have h := F.realGradeProjection_eq_zero_of_mem_next_layer b w hlayers j _ (hXY α)
  simp only [map_sub, Finsupp.sub_apply] at h
  exact sub_eq_zero.mp h

include hlayers in
theorem polynomial_grade_adjoint_eq (hs : 2 ≤ s) (j : ℕ)
    (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (dualAdjoint A X) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) X := by
  apply F.polynomial_grade_eq_of_sub_mem_next b w hlayers j
  exact F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A hA X

include hlayers in
theorem polynomial_grade_logDerivative_eq (hs : 1 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (formalLogDerivative i A) =
      (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord := by
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hDlayer := pderiv_mem_submodule (F.realification.layer j) A.coord hAlayer i
  have hrem := F.realification.polynomialFiltration.dualLogDerivative_sub_tangent_mem_layer hs
    (i := j) (j := j) (formalPolynomialJetHom i A)
    (by rw [formalPolynomialJet_base]; exact hAlayer)
    (by rw [formalPolynomialJet_tangent]; exact hDlayer)
  rw [formalPolynomialJet_tangent] at hrem
  have hnext : ∀ α, coefficients (formalLogDerivative i A -
      (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord) α ∈ F.realification.layer (j + 1) := by
    intro α
    exact F.realification.antitone (by omega : j + 1 ≤ j + j) (hrem α)
  have hgrade := F.polynomial_grade_eq_of_sub_mem_next b w hlayers j _ _ hnext
  have hfix : VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) A.coord = A.coord := by
    apply coefficients.injective
    apply Finsupp.ext
    intro α
    rw [coefficients_map]
    exact hA α
  rw [← pderiv_map, hfix] at hgrade
  exact hgrade

include hlayers in
theorem current_derivative_removal_projection (hs : 2 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) small -
        (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord ∧
    VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint B rational - formalLogDerivative i B) =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) rational -
        (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) B.coord := by
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hA α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hBlayer : ∀ α, coefficients B.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hB α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hAlayer
  constructor
  · rw [F.polynomial_grade_adjoint_eq b w hlayers hs j A⁻¹ hAi, map_sub,
      F.polynomial_grade_logDerivative_eq b w hlayers (by omega) hj i A hA]
  · rw [map_sub, F.polynomial_grade_adjoint_eq b w hlayers hs j B hBlayer,
      F.polynomial_grade_logDerivative_eq b w hlayers (by omega) hj i B hB]

include hlayers in
theorem current_derivative_defect_preserved (hs : 2 ≤ s) {j : ℕ} (hj : 0 < j)
    (i : σ) (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (small rational : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    let π := VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
    let D := (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
    D (π (A⁻¹ * P * B⁻¹).coord) - π (dualAdjoint A⁻¹ (small - formalLogDerivative i A)) -
        π (dualAdjoint B rational - formalLogDerivative i B) =
      D (π P.coord) - π small - π rational := by
  dsimp only
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w j - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w j x = x := by
    intro x hx
    exact sub_eq_zero.mp hx
  have hgrades := F.polynomial_bchRemove_grades b w hlayers E j hE A.coord P.coord B.coord
    (fun α => sub_eq_zero.mpr (hA α)) (fun α => sub_eq_zero.mpr (hB α))
  have hP : VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
      (A⁻¹ * P * B⁻¹).coord =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord - A.coord - B.coord :=
    hgrades.1
  have hparts := F.current_derivative_removal_projection b w hlayers hs hj i A B hA hB small rational
  rw [hP, hparts.1, hparts.2, map_sub, map_sub]
  abel

end Erdos3.NilpotentLieFiltration

end

end OAI
