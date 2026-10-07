import OAI.Combinatorics.Progressions.Dynamics.CurrentLayerBudget
import OAI.Combinatorics.Progressions.Estimates.FormalCurrentDerivativeAdvance
import OAI.Combinatorics.Progressions.Geometry.CoordinateDerivativeBounds
import OAI.Combinatorics.Progressions.Polynomial.ControlledCurrentLayerPolynomialStep

namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem controlled_zero_sum_separation {ι : Type*} [Fintype ι]
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (a b : ι → ℝ) (ha : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p))
    (hb : b ∈ realDenominatorGrid l) (hsum : a + b = 0) : a = 0 ∧ b = 0 := by
  have h := controlled_small_vector_separation (0 : Matrix ι Empty ℚ)
    (H := 1) (by omega) hl (by intro i j; exact j.elim) hp hι
    (by simpa using hp) (by simpa using Real.one_le_exp hp) hlp a b ha hb
    (by rw [hsum]; exact Submodule.zero_mem _)
  simpa only [Set.range_eq_empty, Submodule.span_empty, Submodule.mem_bot] using h

theorem current_derivative_polynomials_separate
    {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l)
    (hsum : ∀ i α, coefficients (S i + R i) α ∈ V.baseChange ℝ) :
    ∀ i α, coefficients (S i) α ∈ V.baseChange ℝ ∧
      coefficients (R i) α ∈ V.baseChange ℝ := by
  have hTone (i : σ) : 1 ≤ T i :=
    (Real.one_le_exp (separationBudget_nonneg hp)).trans (hT i)
  intro i α
  have hscale : Real.exp (separationBudget p) ≤ T i * monomialScale T α :=
    (hT i).trans (le_mul_of_one_le_right (zero_le_one.trans (hTone i))
      (one_le_monomialScale T hTone α))
  have hnorm : ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / Real.exp (separationBudget p) :=
    (hsmall i α).trans (div_le_div_of_nonneg_left (Real.exp_nonneg _) (Real.exp_pos _) hscale)
  have hzero : realQuotientCoordinateMap f (coefficients (S i) α) +
      realQuotientCoordinateMap f (coefficients (R i) α) = 0 := by
    have h := (realQuotientCoordinateMap_eq_zero_iff f _).mpr (hsum i α)
    simpa only [map_add, Finsupp.add_apply] using h
  obtain ⟨hS, hR⟩ := controlled_zero_sum_separation hl hp hι hlp _ _ hnorm (hrational i α) hzero
  exact ⟨(realQuotientCoordinateMap_eq_zero_iff f _).mp hS,
    (realQuotientCoordinateMap_eq_zero_iff f _).mp hR⟩

theorem current_derivative_terms_vanish_of_invariant_polynomial
    {L ι σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι]
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V))
    {l : ℕ} (hl : 0 < l) {p : ℝ} (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hP : ∀ α, coefficients P α ∈ V.baseChange ℝ)
    (S R : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (S i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients (R i) α) ∈
      realDenominatorGrid l)
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P - S i - R i) α ∈ V.baseChange ℝ) :
    ∀ i α, coefficients (S i) α ∈ V.baseChange ℝ ∧
      coefficients (R i) α ∈ V.baseChange ℝ := by
  apply current_derivative_polynomials_separate V f hl hp hι hlp T hT S R hsmall hrational
  intro i α
  have hD : coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P) α ∈
      V.baseChange ℝ := by
    rw [coefficients_pderiv]
    exact ((V.baseChange ℝ).restrictScalars ℚ).smul_mem _ (hP _)
  have h := (V.baseChange ℝ).sub_mem hD (hsplit i α)
  simp only [map_sub, Finsupp.sub_apply] at h
  simp only [map_add, Finsupp.add_apply]
  convert h using 1
  abel

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem eval₂_lie_mem_of_coefficients {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
    (V : Submodule ℝ L) (P : VectorPolynomial σ ℚ L) (x : L)
    (hP : ∀ α, ⁅coefficients P α, x⁆ ∈ V) (t : σ → ℝ) : ⁅eval₂ t P, x⁆ ∈ V := by
  classical
  rw [← sum_monomial_coefficients P]
  simp only [Finsupp.sum, map_sum, eval₂_monomial, sum_lie, smul_lie]
  exact V.sum_mem (fun α _ => V.smul_mem _ (hP α))

namespace NilpotentLieFiltration

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem formal_current_layer_derivative_equation (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hU : ∀ α, coefficients P.coord α ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystem P small rational extra) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hUvalue (t : σ → ℝ) : eval₂ t P.coord ∈ Uq :=
    (eval₂_mem_iff_coefficients U.toSubmodule P.coord).mpr hU t
  apply F.real_current_layer_polynomial_derivative_equation b w hlayers hs Uq V K hUV hV hj
    P.coord hUvalue hK hlower
    (fun t k hk => eval₂_lie_mem_of_coefficients _ P.coord k (fun α => hbracket α k hk) t)
    small rational hrational (fun i t => eval₂ t (extra i))
    (fun i t => realPolynomialJet i t P)
    (fun i t => realPolynomialJet_base i t P) (fun i t => realPolynomialJet_tangent i t P)
  · intro i t
    have h := (eval₂_mem_iff_coefficients _ _).mpr (hextra i) t
    simpa only [map_sub, eval₂_map] using h
  · intro i t
    simpa only [realPolynomialJet_baseHom] using
      PolynomialDerivativeSystem.real_evaluation P small rational extra hsystem i t

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem formal_current_layer_derivative_equation_mod (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w V) {j : ℕ} (hj : 2 ≤ j)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hU : ∀ α, coefficients P.coord α ∈ U)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational extra) :
    ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V := by
  obtain ⟨error, herror, hexact⟩ := PolynomialDerivativeSystemMod.exact_system
    (V.restrictScalars ℚ) P small rational extra hsystem
  apply F.formal_current_layer_derivative_equation b w hlayers hs U V K hUV hV hj
    P hU hK hlower hbracket small rational (fun i => extra i + error i) hrational _ hexact
  intro i α
  have heq : extra i + error i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord) =
      (extra i - VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) + error i := by abel
  rw [heq, map_add, Finsupp.add_apply]
  exact Submodule.add_mem _ (hextra i α) (Submodule.mem_sup_left (herror i α))

theorem formal_current_layer_correction_preserves_lifts_mod {κ : Type*} (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℚ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : κ → ℝ ⊗[ℚ] L)
    (hSR : PolynomialLiftSystemMod V P S R)
    (hS : ∀ t α, coefficients (S t - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1))
    (hR : ∀ t α, coefficients (R t - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1)) :
    PolynomialLiftSystemMod V (A⁻¹ * P * B⁻¹)
        (fun t => dualAdjoint A⁻¹ (S t)) (fun t => dualAdjoint B (R t)) ∧
      ∀ t α,
        coefficients (dualAdjoint A⁻¹ (S t) - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1) ∧
        coefficients (dualAdjoint B (R t) - monomial 0 (k t)) α ∈ V ⊔ F.realification.layer (j + 1) := by
  refine ⟨PolynomialLiftSystemMod.remove U V hUV P A B hAU S R hSR, ?_⟩
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hA
  intro t α
  have hleft := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A⁻¹ hAi (S t)
  have hright := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j B hB (R t)
  constructor
  · have h := (V ⊔ F.realification.layer (j + 1)).add_mem (Submodule.mem_sup_right (hleft α)) (hS t α)
    convert h using 1
    simp only [map_sub, Finsupp.sub_apply]
    abel
  · have h := (V ⊔ F.realification.layer (j + 1)).add_mem (Submodule.mem_sup_right (hright α)) (hR t α)
    convert h using 1
    simp only [map_sub, Finsupp.sub_apply]
    abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem homogeneous_pderiv_coordinate_bound [Fintype σ] [Fintype ι]
    (q : L →ₗ[ℚ] (ι → ℝ)) (P : VectorPolynomial σ ℚ L) (j : ℕ)
    (hP : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients P α = 0)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ α, ‖q (coefficients P α)‖ ≤ M / monomialScale T α)
    (i : σ) (α : σ →₀ ℕ) :
    ‖q (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α)‖ ≤
      j * M / (T i * monomialScale T α) := by
  classical
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (mul_nonneg (Nat.cast_nonneg j) hM)
    (mul_pos (hT i) (monomialScale_pos T hT α)).le)).mpr
  intro n
  let f := (LinearMap.proj n).comp q
  have hdegree : ∀ (β : σ →₀ ℕ) k, j < β k → f (coefficients P β) = 0 := by
    intro β k hk
    have hw := Finsupp.le_weight (fun _ : σ => (1 : ℕ)) (s := k) (by decide) β
    have hne : Finsupp.weight (fun _ : σ => (1 : ℕ)) β ≠ j := by omega
    rw [hP β hne, map_zero]
  have hcoord (β : σ →₀ ℕ) : |f (coefficients P β)| ≤ M / monomialScale T β := by
    exact (norm_le_pi_norm (q (coefficients P β)) n).trans (hbound β)
  have h := directionalDerivative_single_scaled_bound f P j hdegree T hT M hM hcoord i α
  rw [directionalDerivative_single] at h
  change |f (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α)| ≤ _
  convert h using 1
  ring

theorem pderiv_coordinate_grid (q : L →ₗ[ℚ] (ι → ℝ)) (P : VectorPolynomial σ ℚ L) (l : ℕ)
    (hP : ∀ α, q (coefficients P α) ∈ realDenominatorGrid l) (i : σ) (α : σ →₀ ℕ) :
    q (coefficients ((MvPolynomial.pderiv i).toLinearMap.rTensor L P) α) ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hP (α + Finsupp.single i 1)
  rw [coefficients_pderiv, map_smul]
  refine ⟨fun n => (α i + 1 : ℤ) * z n, ?_⟩
  funext n
  have hzn : (z n : ℝ) = (l : ℝ) * q (coefficients P (α + Finsupp.single i 1)) n := congrFun hz n
  change (((α i + 1 : ℤ) * z n : ℤ) : ℝ) =
    (l : ℝ) * (((α i + 1 : ℚ) : ℝ) * q (coefficients P (α + Finsupp.single i 1)) n)
  simp only [Int.cast_mul, Int.cast_add, Int.cast_natCast, Int.cast_one,
    Rat.cast_add, Rat.cast_natCast, Rat.cast_one, hzn]
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem formal_correction_sub_mem_layer (j : ℕ)
    (P A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.layer j) :
    ∀ α, coefficients ((A⁻¹ * P * B⁻¹).coord - P.coord) α ∈ F.layer j := by
  have h := F.polynomialFiltration.correction_removal_preserves_lower_layers (j := j + 1)
    A P B (by rw [Nat.add_sub_cancel]; exact hA)
    (by rw [Nat.add_sub_cancel]; exact hB) (by omega)
  rw [Nat.add_sub_cancel] at h
  exact h

theorem formal_correction_preserves_bracket_remainder (V : Submodule ℚ L) (j : ℕ)
    (P A B : PolynomialGroup σ F.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.layer j)
    (x : L) (hbracket : ∀ α, ⁅coefficients P.coord α, x⁆ ∈ V ⊔ F.layer (j + 1)) :
    ∀ α, ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, x⁆ ∈ V ⊔ F.layer (j + 1) := by
  intro α
  have hx : x ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  have hdiff := F.formal_correction_sub_mem_layer j P A B hA hB α
  have hlie := F.lie_mem hdiff hx
  have h := (V ⊔ F.layer (j + 1)).add_mem (Submodule.mem_sup_right hlie) (hbracket α)
  simp only [map_sub, Finsupp.sub_apply, sub_lie, sub_add_cancel] at h
  exact h

variable {μ : Type*} (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem formal_correction_preserves_projected_log {j : ℕ}
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j) :
    ∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ)
        (A⁻¹ * P * B⁻¹).coord =
      VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord := by
  intro d hd
  apply F.polynomial_grade_eq_of_sub_mem_next b w hlayers d
  intro α
  exact F.realification.antitone (Nat.succ_le_of_lt hd)
    (F.realification.formal_correction_sub_mem_layer j P A B hA hB α)

include hlayers in
theorem formal_correction_advances_log_conditions {j : ℕ} (hj : 2 ≤ j)
    (V K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (hcurrent : ∀ α, coefficients (VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (A⁻¹ * P * B⁻¹).coord) α ∈ V) :
    (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ K) ∧
      ∀ α d, 2 ≤ d → d < j + 1 →
        basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ V := by
  have hbelow := F.formal_correction_preserves_projected_log b w hlayers P A B hA hB
  have hcoef (d : ℕ) (hd : d < j) (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := by
    have h := congrArg (fun X : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients X α) (hbelow d hd)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
    exact h
  constructor
  · intro α
    rw [hcoef 1 (by omega)]
    exact hK α
  · intro α d hd hdj
    rcases lt_or_eq_of_le (show d ≤ j by omega) with hlt | rfl
    · rw [hcoef d hlt]
      exact hlower α d hd hlt
    · have h := hcurrent α
      simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
      exact h

include hlayers in
theorem formal_correction_preserves_horizontal_extra (hs : 2 ≤ s) {j : ℕ} (hj : 2 ≤ j)
    (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, coefficients A.coord α ∈ F.realification.layer j)
    (hB : ∀ α, coefficients B.coord α ∈ F.realification.layer j)
    (extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    ∀ i α, coefficients (dualAdjoint A⁻¹ (extra i) - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (A⁻¹ * P * B⁻¹).coord)) α ∈
        V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  have hlow := F.formal_correction_preserves_projected_log b w hlayers P A B hA hB 1 (by omega)
  have hAi : ∀ α, coefficients (A⁻¹).coord α ∈ F.realification.layer j :=
    (coefficientSubmodule (F.realification.layer j)).neg_mem hA
  intro i α
  rw [← pderiv_map, hlow, pderiv_map]
  have hdiff := F.realification.polynomialFiltration.adjoint_correction_sub_mem_layer hs j A⁻¹ hAi (extra i)
  have h := (V ⊔ (F.realLayer (j + 1)).toSubmodule).add_mem
    (Submodule.mem_sup_right (hdiff α)) (hextra i α)
  convert h using 1
  simp only [map_sub, Finsupp.sub_apply]
  abel

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ ι σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype σ] [Fintype ι] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hlayers in
theorem current_correction_derivative_terms_vanish (hs : 2 ≤ s)
    (V : Submodule ℚ L) (f : Basis ι ℚ (L ⧸ V)) {j l m : ℕ} (hj : 0 < j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsplit : ∀ i α, coefficients
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
        (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P.coord) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i) -
        VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α ∈ V.baseChange ℝ)
    (hnew : ∀ α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (A⁻¹ * P * B⁻¹).coord) α ∈ V.baseChange ℝ)
    {p M C : ℝ} (hp : 0 ≤ p) (hC : 0 ≤ C)
    (hdim : (Fintype.card ι : ℝ) ≤ p) (hl : 0 < l) (hm : 0 < m)
    (hden : ((l * m : ℕ) : ℝ) ≤ Real.exp p) (hsize : M + j * C ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (hsmall : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (hrational : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l)
    (hAnorm : ∀ α, ‖realQuotientCoordinateMap f (coefficients A.coord α)‖ ≤ C / monomialScale T α)
    (hBgrid : ∀ α, realQuotientCoordinateMap f (coefficients B.coord α) ∈ realDenominatorGrid m) :
    ∀ i α, coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))) α ∈ V.baseChange ℝ ∧
      coefficients (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
        (dualAdjoint B (rational i) - formalLogDerivative i B)) α ∈ V.baseChange ℝ := by
  let π := VectorPolynomial.map (σ := σ) ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
  let q := (realQuotientCoordinateMap f).restrictScalars ℚ
  let small' := fun i => π (dualAdjoint A⁻¹ (small i - formalLogDerivative i A))
  let rational' := fun i => π (dualAdjoint B (rational i) - formalLogDerivative i B)
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hparts (i : σ) := F.current_derivative_removal_projection b w hlayers hs hj i A B hA hB (small i) (rational i)
  have hsmall' : ∀ i α, ‖realQuotientCoordinateMap f (coefficients (small' i) α)‖ ≤
      Real.exp p / (T i * monomialScale T α) := by
    intro i α
    have hD := homogeneous_pderiv_coordinate_bound q A.coord j hAhom T hTpos hC hAnorm i α
    have he : small' i = π (small i) - (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord :=
      (hparts i).1
    rw [he, map_sub, Finsupp.sub_apply, map_sub]
    calc
      _ ≤ ‖realQuotientCoordinateMap f (coefficients (π (small i)) α)‖ +
          ‖realQuotientCoordinateMap f (coefficients
            ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) A.coord) α)‖ := norm_sub_le _ _
      _ ≤ M / (T i * monomialScale T α) + j * C / (T i * monomialScale T α) := add_le_add (hsmall i α) hD
      _ = (M + j * C) / (T i * monomialScale T α) := by ring
      _ ≤ Real.exp p / (T i * monomialScale T α) :=
        div_le_div_of_nonneg_right hsize (mul_pos (hTpos i) (monomialScale_pos T hTpos α)).le
  have hrational' : ∀ i α, realQuotientCoordinateMap f (coefficients (rational' i) α) ∈
      realDenominatorGrid (l * m) := by
    intro i α
    have he : rational' i = π (rational i) - (MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) B.coord :=
      (hparts i).2
    rw [he, map_sub, Finsupp.sub_apply, map_sub]
    exact realDenominatorGrid_sub_product l m _ _ (hrational i α)
      (pderiv_coordinate_grid q B.coord m hBgrid i α)
  apply current_derivative_terms_vanish_of_invariant_polynomial V f (Nat.mul_pos hl hm) hp hdim hden T hT
    (π (A⁻¹ * P * B⁻¹).coord) hnew small' rational' hsmall' hrational'
  intro i α
  have he := F.current_derivative_defect_preserved b w hlayers hs hj i P A B hA hB (small i) (rational i)
  change coefficients
    ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) (π (A⁻¹ * P * B⁻¹).coord) - small' i - rational' i) α ∈ _
  rw [he]
  exact hsplit i α

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {E V : Submodule ℚ L}

include hlayers in
theorem exists_controlled_formal_current_layer_step
    (hgraded : BasisHomogeneousBrackets b w) (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (hj : 2 ≤ j)
    (hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p q M : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hrows : (Fintype.card ι : ℝ) ≤ p) (hcols : (Fintype.card ν : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : ((l * j : ℕ) : ℝ) ≤ Real.exp p)
    (hbudget : (Fintype.card σ : ℝ) / j * M ≤ Real.exp p)
    (hrowsq : (Fintype.card ι : ℝ) ≤ q)
    (hden : ((l * matrixDenominator (quotientCoordinateMatrix b f) *
        matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * Real.exp ((p + 2) ^ 36) ≤ Real.exp q)
    (hsize : M + j * ((((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p)) ≤ Real.exp q)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (hTq : ∀ i, Real.exp (separationBudget q) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l) :
    ∃ (m : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid (matrixDenominator (bracketLiftMatrix b e) * m)) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        ∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  let π := VectorPolynomial.map (σ := σ) ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ)
  have hjpos : 0 < j := by omega
  have hsplit := F.formal_current_layer_derivative_equation_mod b w hlayers hs U (V.baseChange ℝ) K
    hUV hV hj P hPU hK hlower hbracket small rational extra hrational hextra hsystem
  have h := F.exists_controlled_current_layer_polynomial_step b w hlayers Uq e f (hgraded.baseChange b w)
    hjpos hE hEU hH hl hA he hp hrows hcols hHp hlp T hT P.coord (π P.coord) hPU hPgraded rfl
    (fun α => by rw [coefficients_map]; exact hPE α) (fun i => π (small i)) (fun i => π (rational i))
    (fun i => shifted_one_projection_homogeneous (b.baseChange ℝ) w _ (hSgraded i) hjpos)
    (fun i => shifted_one_projection_homogeneous (b.baseChange ℝ) w _ (hRgraded i) hjpos)
    hsplit hM hbudget
    (fun i α n => (norm_le_pi_norm (realQuotientCoordinateMap f (coefficients (π (small i)) α)) n).trans (hslow i α)) hgrid
  obtain ⟨m, a, c, Pnew, hm, hmp, hac, hahom, hchom, hanorm, hcgrid,
    hremove, _, hconstant, hnewgraded, hnewU, hnewV, hbelow⟩ := h
  let A : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot := ⟨a⟩
  let B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot := ⟨c⟩
  let P' := A⁻¹ * P * B⁻¹
  have hcoord : P'.coord = Pnew := hremove.symm
  have hApure : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients A.coord α) = coefficients A.coord α :=
    fun α => hE _ (hac α).1
  have hBpure : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients B.coord α) = coefficients B.coord α :=
    fun α => hE _ (hac α).2
  have hAU : ∀ α, coefficients A.coord α ∈ Uq := fun α => hEU _ (hac α).1
  have hBU : ∀ α, coefficients B.coord α ∈ Uq := fun α => hEU _ (hac α).2
  have hAlayer : ∀ α, coefficients A.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hApure α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  have hBlayer : ∀ α, coefficients B.coord α ∈ F.realification.layer j := by
    intro α
    rw [← hBpure α]
    exact F.realGradeProjection_mem_layer b w hlayers j _
  let C : ℝ := (((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
    (((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hAnorm : ∀ α, ‖realQuotientCoordinateMap f (coefficients A.coord α)‖ ≤ C / monomialScale T α := by
    intro α
    calc
      _ ≤ (((Fintype.card μ : ℝ) + 1) * (Q + 1)) * ‖(b.baseChange ℝ).equivFun (coefficients a α)‖ :=
        realQuotientCoordinateMap_norm_bound b f hf _
      _ ≤ (((Fintype.card μ : ℝ) + 1) * (Q + 1)) *
          ((((Fintype.card ν : ℝ) + 1) * (J + 1)) * Real.exp ((p + 2) ^ 18 + p) / monomialScale T α) :=
        mul_le_mul_of_nonneg_left (hanorm α) (by positivity)
      _ = C / monomialScale T α := by dsimp [C]; ring
  let n := matrixDenominator (quotientCoordinateMatrix b f) * (matrixDenominator (bracketLiftMatrix b e) * m)
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) (Nat.mul_pos (matrixDenominator_pos _) hm)
  have hBgrid : ∀ α, realQuotientCoordinateMap f (coefficients B.coord α) ∈ realDenominatorGrid n :=
    fun α => realQuotientCoordinateMap_grid b f _ _ (hcgrid α)
  have hden' : ((l * n : ℕ) : ℝ) ≤ Real.exp q := by
    calc
      _ = ((l * matrixDenominator (quotientCoordinateMatrix b f) *
          matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * (m : ℝ) := by
        dsimp [n]
        push_cast
        ring
      _ ≤ ((l * matrixDenominator (quotientCoordinateMatrix b f) *
          matrixDenominator (bracketLiftMatrix b e) : ℕ) : ℝ) * Real.exp ((p + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmp (by positivity)
      _ ≤ Real.exp q := hden
  have hnew : ∀ α, coefficients (π P'.coord) α ∈ V.baseChange ℝ := by
    intro α
    rw [hcoord]
    exact Submodule.baseChange_mono ℝ inf_le_right (hnewV α)
  have hvanish := F.current_correction_derivative_terms_vanish b w hlayers hs V f hjpos P A B
    hApure hBpure hahom small rational hsplit hnew hq hC hrowsq hl hn hden' hsize T hTq hslow hgrid hAnorm hBgrid
  have hadvance := F.formal_current_derivative_advance b w hlayers Uq (V.baseChange ℝ) hUV hV j A B
    hAU hBU hAlayer hBlayer small rational hsmall hrational hvanish
  have hAgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j a hahom hApure
  have hBgraded := homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
    j c hchom hBpure
  have hlog := F.formal_correction_advances_log_conditions b w hlayers hj (V.baseChange ℝ) K
    P A B hAlayer hBlayer hK hlower hnew
  have hWiff (x : ℝ ⊗[ℚ] L) :
      x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔ F.realification.layer (j + 1) ↔
        x ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    change x ∈ (V.baseChange ℝ).restrictScalars ℚ ⊔
      (F.realLayer (j + 1)).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  have hbracket' : ∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
      V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
    intro α k hk
    exact (hWiff _).mp (F.realification.formal_correction_preserves_bracket_remainder
      ((V.baseChange ℝ).restrictScalars ℚ) j P A B hAlayer hBlayer k
      (fun β => (hWiff _).mpr (hbracket β k hk)) α)
  refine ⟨m, A, B, hm, hmp, hac, hahom, hchom, hanorm, hcgrid, ?_, ?_, ?_, ?_, ?_, ?_,
    PolynomialDerivativeSystemMod.remove Uq ((V.baseChange ℝ).restrictScalars ℚ) hUV P A B hAU
      small rational extra hsystem, ?_, hadvance, hlog.1, hlog.2, hbracket',
    F.formal_correction_preserves_horizontal_extra b w hlayers hs hj (V.baseChange ℝ)
      P A B hAlayer hBlayer extra hextra⟩
  · group
  · change coefficients P'.coord 0 = _
    rw [hcoord]
    exact hconstant
  · change P'.coord ∈ _
    rw [hcoord]
    exact hnewgraded
  · intro α
    change coefficients P'.coord α ∈ _
    rw [hcoord]
    exact hnewU α
  · intro α
    change coefficients (π P'.coord) α ∈ _
    rw [hcoord]
    exact hnewV α
  · intro d hd
    change VectorPolynomial.map _ P'.coord = _
    rw [hcoord]
    exact hbelow d hd
  · intro i
    exact polynomial_derivative_removal_preserves_shifted_grading (b.baseChange ℝ) w (hgraded.baseChange b w)
      i A B (small i) (rational i) hAgraded hBgraded (hSgraded i) (hRgraded i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_current_layer_step :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι ν σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype ν] [Fintype σ] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hlayers : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    {E V : Submodule ℚ L}
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (K : Submodule ℝ (ℝ ⊗[ℚ] L))
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (e : Basis ν ℚ E) (f : Basis ι ℚ (L ⧸ V))
    {j H J Q l : ℕ} (_hj : 2 ≤ j)
    (_hE : ∀ x ∈ E.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hEU : ∀ x ∈ E.baseChange ℝ, x ∈ U)
    (_hH : 1 ≤ H) (_hl : 0 < l)
    (_hA : ∀ i n, RationalHeightLE (subspaceQuotientMatrix e f i n) H)
    (_he : ∀ i n, RationalHeightLE (b.repr (e n : L) i) J)
    (_hf : ∀ i n, RationalHeightLE (f.repr (V.mkQ (b n)) i) Q)
    {p M : ℝ} (_hp : 0 ≤ p) (_hM : 0 ≤ M)
    (_hambient : (Fintype.card μ : ℝ) ≤ p) (_hrows : (Fintype.card ι : ℝ) ≤ p)
    (_hcols : (Fintype.card ν : ℝ) ≤ p) (_hvariables : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hJp : (J : ℝ) ≤ Real.exp p) (_hQp : (Q : ℝ) ≤ Real.exp p)
    (_hlp : (l : ℝ) ≤ Real.exp p) (_hMp : M ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (P : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (_hPU : ∀ α, coefficients P.coord α ∈ U)
    (_hPgraded : P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1))
    (_hPE : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P.coord α) ∈ E.baseChange ℝ)
    (_hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (_hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V.baseChange ℝ)
    (_hbracket : ∀ α k, k ∈ K →
      ⁅coefficients P.coord α, k⁆ ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (small rational extra : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (_hsmall : ∀ i α, coefficients (small i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hrational : ∀ i α, coefficients (rational i) α ∈ V.baseChange ℝ ⊔ (F.realLayer j).toSubmodule)
    (_hextra : ∀ i α, coefficients (extra i - VectorPolynomial.map
      ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
      ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P.coord)) α ∈
        V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule)
    (_hsystem : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P small rational extra)
    (_hSgraded : ∀ i, small i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hRgraded : ∀ i, rational i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (_hslow : ∀ i α, ‖realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small i)) α)‖ ≤
        M / (T i * monomialScale T α))
    (_hgrid : ∀ i α, realQuotientCoordinateMap f (coefficients
      (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational i)) α) ∈
        realDenominatorGrid l),
    ∃ (n : ℕ) (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      (∀ α, coefficients A.coord α ∈ E.baseChange ℝ ∧ coefficients B.coord α ∈ E.baseChange ℝ) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients A.coord α = 0) ∧
      (∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j → coefficients B.coord α = 0) ∧
      (∀ α, ‖(b.baseChange ℝ).equivFun (coefficients A.coord α)‖ ≤
        Real.exp ((p + C) ^ C) / monomialScale T α) ∧
      (∀ α, (b.baseChange ℝ).equivFun (coefficients B.coord α) ∈
        realDenominatorGrid n) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
      let extra' := fun i => dualAdjoint A⁻¹ (extra i)
      A * P' * B = P ∧ coefficients P'.coord 0 = coefficients P.coord 0 ∧
        P'.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, coefficients (VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) α ∈ (E ⊓ V).baseChange ℝ) ∧
        (∀ d < j, VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P'.coord =
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w d).restrictScalars ℚ) P.coord) ∧
        PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i, small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        (∀ i α, coefficients (small' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule ∧
          coefficients (rational' i) α ∈ V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K) ∧
        (∀ α d, 2 ≤ d → d < j + 1 →
          basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V.baseChange ℝ) ∧
        (∀ α k, k ∈ K → ⁅coefficients P'.coord α, k⁆ ∈
          V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        ∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V.baseChange ℝ ⊔ (F.realLayer (j + 1)).toSubmodule := by
  obtain ⟨C, hC, hCbound⟩ := exists_current_layer_uniform_budget
  refine ⟨C, hC, ?_⟩
  intro L μ ι ν σ _ _ _ _ _ _ s F b w hlayers E V
    hgraded hs U K hUV hV e f j H J Q l hj hE hEU hH hl hA he hf
    p M hp hM hambient hrows hcols hvariables hjp hHp hJp hQp hlp hMp T hT
    P hPU hPgraded hPE hK hlower hbracket small rational extra hsmall hrational hextra
    hsystem hSgraded hRgraded hslow hgrid
  let t := currentLayerConstructionBudget p
  let q := currentLayerRemovalBudget p
  have ht : 0 ≤ t := currentLayerConstructionBudget_nonneg hp
  have hq : 0 ≤ q := currentLayerRemovalBudget_nonneg hp
  have hpt : p ≤ t := le_currentLayerConstructionBudget hp
  have hEt : Real.exp p ≤ Real.exp t := Real.exp_le_exp.mpr hpt
  have hconstruction := current_layer_construction_budget_bounds hM (Fintype.card σ) j l
    hvariables (by omega) hjp hlp hMp
  have hpplus : Real.exp p ≤ Real.exp ((p + 2) ^ 1) := by
    apply Real.exp_le_exp.mpr
    simp only [pow_one]
    linarith
  have hD := matrixDenominator_le_exp_power (quotientCoordinateMatrix b f) hp 1 hrows hambient (fun i n => by
    have hden : (((quotientCoordinateMatrix b f i n).den) : ℝ) ≤ Q := Nat.cast_le.mpr (hf i n).2
    exact (hden.trans hQp).trans hpplus)
  have hEden := matrixDenominator_le_exp_power (bracketLiftMatrix b e) hp 1 hambient hcols (fun i n => by
    have hden : (((bracketLiftMatrix b e i n).den) : ℝ) ≤ J := Nat.cast_le.mpr (he i n).2
    exact (hden.trans hJp).trans hpplus)
  obtain ⟨hpq, hden, hsize, _, haCap, hbCap⟩ := current_layer_removal_budget_bounds hp
    (Fintype.card μ) (Fintype.card ν) j J Q l
    (matrixDenominator (quotientCoordinateMatrix b f)) (matrixDenominator (bracketLiftMatrix b e))
    hambient hcols hjp hJp hQp hlp hMp hD hEden
  have hCval : separationBudget t + separationBudget q + q ≤ (p + C) ^ C := hCbound p hp
  have hst := separationBudget_nonneg ht
  have hsq := separationBudget_nonneg hq
  have htCut : separationBudget t ≤ (p + C) ^ C := by linarith
  have hqCut : separationBudget q ≤ (p + C) ^ C := by linarith
  have hqBound : q ≤ (p + C) ^ C := by linarith
  have hTt : ∀ i, Real.exp (separationBudget t) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr htCut).trans (hT i)
  have hTq : ∀ i, Real.exp (separationBudget q) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hqCut).trans (hT i)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hstep := F.exists_controlled_formal_current_layer_step b w hlayers (p := t) (q := q)
    hgraded hs U K hUV hV e f hj hE hEU hH hl hA he hf ht hq hM
    (hrows.trans hpt) (hcols.trans hpt) (hHp.trans hEt) hconstruction.1 hconstruction.2
    (hrows.trans hpq) hden hsize T hTt hTq P hPU hPgraded hPE hK hlower hbracket
    small rational extra hsmall hrational hextra hsystem hSgraded hRgraded hslow hgrid
  obtain ⟨m, A, B, hm, hmp, hAB, hAhom, hBhom, hAnorm, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩ := hstep
  let n := matrixDenominator (bracketLiftMatrix b e) * m
  have hn : 0 < n := Nat.mul_pos (matrixDenominator_pos _) hm
  have hnbound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (matrixDenominator (bracketLiftMatrix b e) : ℝ) * (m : ℝ) := by dsimp [n]; rw [Nat.cast_mul]
      _ ≤ (matrixDenominator (bracketLiftMatrix b e) : ℝ) * Real.exp ((t + 2) ^ 36) :=
        mul_le_mul_of_nonneg_left hmp (Nat.cast_nonneg _)
      _ ≤ Real.exp q := hbCap
      _ ≤ _ := Real.exp_le_exp.mpr hqBound
  refine ⟨n, A, B, hn, hnbound, hAB, hAhom, hBhom, ?_, hBgrid,
    hprod, hconstant, hnewgraded, hnewU, hnewV, hbelow, hnewsystem, hnewshift,
    hnewderivative, hnewK, hnewlower, hnewbracket, hnewextra⟩
  intro α
  exact (hAnorm α).trans (div_le_div_of_nonneg_right
    (haCap.trans (Real.exp_le_exp.mpr hqBound)) (monomialScale_pos T hTpos α).le)

end Erdos3.NilpotentLieFiltration

end

end OAI
