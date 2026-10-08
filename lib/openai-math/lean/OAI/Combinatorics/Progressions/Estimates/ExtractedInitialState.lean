/-
Modified for ProveIt: give exists_fastCoefficient_rational_removal_grid a
local 400000-heartbeat budget for dependent quotient reduction on Lean 4.32.
The upstream theorem statements and proof text are unchanged.
-/
import OAI.Combinatorics.Progressions.Dynamics.FastRemovalBudget
import OAI.Combinatorics.Progressions.Dynamics.InitialRemovalBudget
import OAI.Combinatorics.Progressions.Estimates.FullFastHorizontalNormalization
import OAI.Combinatorics.Progressions.Geometry.NativeCoordinateDerivativeSystem
import OAI.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse
import OAI.Combinatorics.Progressions.Polynomial.NativeFormalPolynomialSystems

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

set_option maxHeartbeats 400000 in
theorem exists_fastCoefficient_rational_removal_grid (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
      (b : Basis κ ℝ (F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U))
      (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1)),
      (∀ y, (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ (R y) = b.equivFun.symm y) →
      ∀ l L₀ dproj : ℕ, 0 < L₀ → (L₀ : ℝ) ≤ Real.exp p →
      0 < dproj → (dproj : ℝ) ≤ Real.exp p →
      (∀ y, y ∈ realDenominatorGrid l → F.FirstCoefficientGrid e ω hF (fun _ => 1) L₀ (R y)) →
      (∀ m x, F.FirstCoefficientGrid e ω hF (fun _ => 1) m x →
        b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) ∈
            realDenominatorGrid (dproj * m)) →
      ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U,
          F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) L₀ g.val.coord →
          (∀ x, b.equivFun x ∈ realDenominatorGrid l →
            b.equivFun (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g x) ∈
              realDenominatorGrid q) ∧
          (∀ h : σ → ℤ, b.equivFun (F.realFastCoefficientDirectionMap U g.val (fun i => (h i : ℝ))) ∈
            realDenominatorGrid q) ∧
          ∀ x, b.equivFun x ∈ realDenominatorGrid l → ∀ h : σ → ℤ,
            b.equivFun (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g x -
              F.realFastCoefficientDirectionMap U g.val (fun i => (h i : ℝ))) ∈ realDenominatorGrid q := by
  have hex := exists_firstCoefficient_operation_grid (s + 1)
  obtain ⟨D, _, hfirst⟩ := hex
  let B : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C D) ^ D
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF H p hH hp hι hσ hHp hc U b R hR
    l L₀ dproj hL hLp hd hdP hlift hproj
  have hdata := hfirst F e ω hF H p hH hp hι hσ hHp hc L₀ hL hLp
  obtain ⟨m, hm, hmp, _, had, hlog⟩ := hdata
  have hfinal : p + (p + D) ^ D ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  have hq : ((dproj * m : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp ((p + D) ^ D) :=
        mul_le_mul hdP hmp (Nat.cast_nonneg m) (Real.exp_nonneg p)
      _ = Real.exp (p + (p + D) ^ D) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hfinal
  refine ⟨dproj * m, Nat.mul_pos hd hm, hq, ?_⟩
  intro g hg
  have haction : ∀ x, b.equivFun x ∈ realDenominatorGrid l →
      b.equivFun (F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g x) ∈
        realDenominatorGrid (dproj * m) := by
    intro x hx
    exact F.fastCoefficientAdjoint_grid e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      U b R hR g l L₀ m (dproj * m) hlift (fun y hy => had g.val y hg hy) (hproj m) x hx
  have hderivative : ∀ h : σ → ℤ,
      b.equivFun (F.realFastCoefficientDirectionMap U g.val (fun i => (h i : ℝ))) ∈
        realDenominatorGrid (dproj * m) := by
    intro h
    exact hproj m _ (hlog g.val.coord hg h)
  refine ⟨haction, hderivative, ?_⟩
  intro x hx h
  rw [map_sub]
  exact realDenominatorGrid_sub (dproj * m) _ _ (haction x hx) (hderivative h)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw

theorem realFirstCoefficientGradedPolynomial_initial_remainder
    (x : F.RealFirstCoefficientModule w) (α : σ →₀ ℕ) :
    coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w x -
      monomial 0 ((F.layerOneGradedMap e ω hF).baseChange ℝ
        (F.realFirstCoefficientHorizontal w x))) α ∈
      (F.associatedGradedFiltration.realLayer 2).toSubmodule := by
  classical
  rw [← F.realFirstCoefficientGradedPolynomial_horizontal]
  by_cases hα : α = 0
  · subst α
    simp only [map_sub, Finsupp.sub_apply, coefficients_monomial,
      Finsupp.single_eq_same, sub_self]
    exact Submodule.zero_mem _
  · rw [map_sub, Finsupp.sub_apply, coefficients_monomial,
      Finsupp.single_eq_of_ne hα, sub_zero]
    apply (F.associatedGradedFiltration.real_mem_layer_iff_basis_coordinates
      (F.associatedGradedBasis e ω hF) ω (F.associatedGradedFiltration_layer e ω hF) 2 _).mpr
    intro i hi
    have hpos := positive_weight_of_ne_zero w hw hα
    exact F.realFirstCoefficientGradedPolynomial_coordinate_of_ne e ω hF w x α i (by omega)

theorem realFirstCoefficientGradedPolynomial_mem_second
    (x : F.RealFirstCoefficientModule w) (hx : F.realFirstCoefficientHorizontal w x = 0)
    (α : σ →₀ ℕ) :
    coefficients (F.realFirstCoefficientGradedPolynomial e ω hF w x) α ∈
      (F.associatedGradedFiltration.realLayer 2).toSubmodule := by
  have h := F.realFirstCoefficientGradedPolynomial_initial_remainder e ω hF w hw x α
  simpa only [hx, map_zero, monomial, TensorProduct.tmul_zero, sub_zero] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_fastCoefficient_slow_removal_bound (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      ∀ (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
      (b : Basis κ ℝ (F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U))
      (R : (κ → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule (fun _ : σ => 1)),
      (∀ y, (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ (R y) = b.equivFun.symm y) →
      ∀ (rows : κ → FirstCoefficientIndex (fun _ : σ => 1) ω) (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ K : ℝ, 0 ≤ K → K ≤ Real.exp p →
      (∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
        ∀ i, |b.equivFun ((F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ x) i| ≤
            K * M / monomialScale T (rows i).val.1) →
      (∀ M, 0 ≤ M → ∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ => 1) T (K * M) (R y)) →
      let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
      let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
      let Y := fun (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) i =>
        F.realFastCoefficientDirectionMap U g.val (Pi.single i 1)
      ∀ g : F.realFastDiagonalSubgroup (fun _ : σ => 1) U,
        F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T (Real.exp ((p + 2) ^ a)) g.val.coord →
        (∀ x, ‖N ((ρ g).symm x)‖ ≤ Real.exp ((p + C) ^ C) * ‖N x‖) ∧
        (∀ i, ‖N (Y g i)‖ ≤ Real.exp ((p + C) ^ C) / T i) ∧
        ∀ (M : ℝ) (small : σ → F.RealFastCoefficientModule (fun _ => 1) (fun _ => Nat.zero_lt_one) U),
          (∀ i, ‖N (small i)‖ ≤ M / T i) →
          ∀ i, ‖N ((ρ g).symm (small i - Y g i))‖ ≤
            Real.exp ((p + C) ^ C) * (M + Real.exp ((p + C) ^ C)) / T i := by
  have hexA := exists_firstCoefficient_adjoint_bound (s + 1) a
  obtain ⟨cA, _, hA⟩ := hexA
  have hexD := exists_firstCoefficient_coordinate_derivative_bound (s + 1) a
  obtain ⟨cD, _, hD⟩ := hexD
  have hfactorBudget := exists_fast_removal_factor_budget s a cA cD
  obtain ⟨C, hC, hbudget⟩ := hfactorBudget
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ _ F e ω hF H p hH hp hι hσ hHp hc U b R hR rows T hT K hK hKp
    hproj hlift N ρ Y g hg
  obtain ⟨hAfactor, hDfactor⟩ := hbudget p hp K hK hKp
  have hginv := F.realAdaptedCoefficientBound_inv e ω hF (fun _ => 1) T
    (Real.exp ((p + 2) ^ a)) g.val hg
  have had := hA F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H p hH hp hι hσ hHp hc T hT (g⁻¹).val hginv
  have haction : ∀ x, ‖N ((ρ g).symm x)‖ ≤ Real.exp ((p + C) ^ C) * ‖N x‖ := by
    intro x
    have he := F.realFastCoefficientAction_symm (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U g x
    have hb := F.fastCoefficientAdjoint_norm_bound e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      U b R hR rows T hT K K (Real.exp ((p + cA) ^ cA)) hK hK (Real.exp_nonneg _) hproj hlift
      g⁻¹ had x
    exact (congrArg (fun y => ‖N y‖) he).le.trans
      (hb.trans (mul_le_mul_of_nonneg_right hAfactor (norm_nonneg _)))
  have hfirst := hD F e ω hF H p hH hp hι hσ hHp hc T hT g.val.coord hg
  have hderivative : ∀ i, ‖N (Y g i)‖ ≤ Real.exp ((p + C) ^ C) / T i := by
    intro i
    have hb := F.fastCoefficientDirection_norm_bound e ω hF U b rows T hT K
      (Real.exp ((p + cD) ^ cD) * ((s + 1 : ℕ) * Real.exp ((p + 2) ^ a))) hK (by positivity)
      hproj g.val (fun j => by simpa only [mul_div_assoc] using hfirst j) i
    exact hb.trans (div_le_div_of_nonneg_right hDfactor (hT i).le)
  refine ⟨haction, hderivative, ?_⟩
  intro M small hsmall i
  exact norm_removed_derivative_bound N (ρ g).symm.toLinearMap (small i) (Y g i)
    (Real.exp ((p + C) ^ C)) M (Real.exp ((p + C) ^ C)) (T i)
    (Real.exp_nonneg _) (hT i) haction (hsmall i) (hderivative i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι ν τ K L V : Type*} [Fintype σ] [DecidableEq σ]
  [AddCommGroup K] [Module ℝ K] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))
  (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) U
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) U
local notation "P" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap U (Subtype.val g) (Pi.single i 1))

include e ω hF

theorem realFast_derivative_removal_controlled
    (a b c : 𝓖) (S R : K →ₗ[ℝ] 𝓔)
    (hSR : S = (ρ (a * b * c)).toLinearMap.comp R)
    (I : K →ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2))) (hS : (P).comp S = I) (hR : (P).comp R = I)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y (a * b * c) i = small i + ρ (a * b * c) (rational i) + S (k i))
    (N : 𝓔 →ₗ[ℝ] V) (coord : 𝓔 →ₗ[ℝ] (τ → ℝ))
    (C M D : ℝ) (hC : 0 ≤ C) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (haction : ∀ x, ‖N ((ρ a).symm x)‖ ≤ C * ‖N x‖)
    (hsmall : ∀ i, ‖N (small i)‖ ≤ M / T i) (hYa : ∀ i, ‖N (Y a i)‖ ≤ D / T i)
    (B : K → ℝ) (hSbound : ∀ x, ‖N (S x)‖ ≤ B x)
    (v : ν → K) (l q : ℕ) (hRgrid : ∀ j, coord (R (v j)) ∈ realDenominatorGrid l)
    (hrational : ∀ i, coord (rational i) ∈ realDenominatorGrid l)
    (hc : ∀ x, coord x ∈ realDenominatorGrid l → coord (ρ c x) ∈ realDenominatorGrid q)
    (hYc : ∀ i, coord (Y c i) ∈ realDenominatorGrid q) :
    let S' := (ρ a).symm.toLinearMap.comp S
    let R' := (ρ c).toLinearMap.comp R
    let small' := fun i => (ρ a).symm (small i - Y a i)
    let rational' := fun i => ρ c (rational i) - Y c i
    S' = (ρ b).toLinearMap.comp R' ∧ (P).comp S' = I ∧ (P).comp R' = I ∧
      (∀ x, ‖N (S' x)‖ ≤ C * B x) ∧
      (∀ j, coord (R' (v j)) ∈ realDenominatorGrid q) ∧
      ∀ i, Y b i = small' i + ρ b (rational' i) + S' (k i) ∧
        ‖N (small' i)‖ ≤ C * (M + D) / T i ∧
        coord (rational' i) ∈ realDenominatorGrid q := by
  have hfactor := F.realFastCoefficient_remove_lifts U a b c S R hSR
  have hhorizontal := F.realFastCoefficient_remove_horizontal_lifts U e ω hF a c S R I hS hR
  refine ⟨hfactor, hhorizontal.1, hhorizontal.2, ?_, ?_, ?_⟩
  · intro x
    exact (haction (S x)).trans (mul_le_mul_of_nonneg_left (hSbound x) hC)
  · intro j
    exact hc _ (hRgrid j)
  · intro i
    refine ⟨F.realFastCoefficient_remove_derivative U e ω hF a b c (Pi.single i 1)
      (small i) (rational i) (S (k i)) (hsystem i), ?_, ?_⟩
    · exact norm_removed_derivative_bound N (ρ a).symm.toLinearMap (small i) (Y a i)
        C M D (T i) hC (hT i) haction (hsmall i) (hYa i)
    · rw [map_sub]
      exact realDenominatorGrid_sub q _ _ (hc _ (hrational i)) (hYc i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "bG" => F.associatedGradedBasis e ω hF
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Kf" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "φ" => F.realFirstCoefficientGradedPolynomial e ω hF (fun _ : σ => 1)
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "H₁" => F.realFirstCoefficientHorizontal (fun _ : σ => 1)

noncomputable def nativeInitialFormalState
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (S R : (κ → ℝ) →ₗ[ℝ] E)
    (small rational : σ → E) (k : σ → κ → ℝ)
    (hSR : ∀ z, (Kf).mkQ (S (Pi.basisFun ℝ κ z)) =
      ρ g ((Kf).mkQ (R (Pi.basisFun ℝ κ z))))
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      (Kf).mkQ (small i) + ρ g ((Kf).mkQ (rational i)) + (Kf).mkQ (S (k i)))
    (hS : ∀ z, H₁ (S (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2))
    (hR : ∀ z, H₁ (R (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2))
    (hsmall : ∀ i, H₁ (small i) = 0) (hrational : ∀ i, H₁ (rational i) = 0)
    (hhorizontal : ∀ i, (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) ∈
        K.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (p : ℝ) (l : ℕ) (hl : 0 < l)
    (hlp : (l : ℝ) ≤ Real.exp p)
    (hSbound : ∀ z, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T
      (Real.exp p) (S (Pi.basisFun ℝ κ z)))
    (hRgrid : ∀ z, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R (Pi.basisFun ℝ κ z)))
    (hsmallBound : ∀ i, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T
      (Real.exp p / T i) (small i))
    (hrationalGrid : ∀ i, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (rational i)) :
    F.associatedGradedFiltration.FormalInductionState bG ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
      (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 p where
  P := F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val
  S := fun z => φ (S (Pi.basisFun ℝ κ z))
  R := fun z => φ (R (Pi.basisFun ℝ κ z))
  small := fun i => φ (small i)
  rational := fun i => φ (rational i)
  k := k
  denominator := l
  denominator_pos := hl
  denominator_bound := hlp
  constant_zero := F.realAdaptedGradedPolynomialLie_constant e ω hF (fun _ : σ => 1) g.val.coord
  mem_U := F.realAdaptedGradedPolynomialLie_fullFast_mem e ω hF W hW g
  graded := F.realAdaptedGradedPolynomialLie_graded e ω hF (fun _ : σ => 1) g.val.coord
  horizontal := F.realAdaptedGradedPolynomialLie_horizontal_mem e ω hF g.val.coord
    ((F.gradedHorizontalKernel e ω hF K).baseChange ℝ)
    (fun i => F.gradedHorizontalKernel_real_mem e ω hF K _ (hhorizontal i))
  lower_log := by intro α d hd hlt; omega
  lower_bracket := by
    intro d hd z α
    have hd0 : d = 0 := by omega
    subst d
    have hz := F.associatedGradedFiltration.realGradeProjection_eq_zero_of_mem_next_layer
      bG ω (F.associatedGradedFiltration_layer e ω hF) 0
      (coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) g.val.coord) α)
      (by rw [Nat.zero_add, F.associatedGradedFiltration.realification.one_eq_top]; trivial)
    change ⁅basisGradeProjection ((bG).baseChange ℝ) ω 0
      (coefficients (F.realAdaptedGradedPolynomialLie e ω hF (fun _ : σ => 1) g.val.coord) α),
      (1 : ℝ) ⊗ₜ[ℚ] (F.gradedHorizontalKernelBasis e ω hF K bK z : F.AssociatedGraded)⁆ ∈ _
    rw [hz, zero_lie]
    exact Submodule.zero_mem _
  lift_system := F.nativeFast_liftSystem_to_formal e ω hF W hW g
    (fun z => S (Pi.basisFun ℝ κ z)) (fun z => R (Pi.basisFun ℝ κ z)) hSR
  derivative_system := by
    have he : (fun i : σ => basisPolynomialLift (Pi.basisFun ℝ κ)
        (fun z => φ (S (Pi.basisFun ℝ κ z))) (k i)) = (fun i : σ => φ (S (k i))) := by
      funext i
      exact (F.realFirstCoefficientGradedPolynomial_basisLift e ω hF (Pi.basisFun ℝ κ) S (k i)).symm
    rw [he]
    exact F.nativeFast_derivativeSystem_to_formal e ω hF W hW g small rational (fun i => S (k i)) hsystem
  S_shift := fun z => F.realFirstCoefficientGradedPolynomial_homogeneous e ω hF (fun _ : σ => 1) _
  R_shift := fun z => F.realFirstCoefficientGradedPolynomial_homogeneous e ω hF (fun _ : σ => 1) _
  small_shift := fun i => F.realFirstCoefficientGradedPolynomial_homogeneous e ω hF (fun _ : σ => 1) _
  rational_shift := fun i => F.realFirstCoefficientGradedPolynomial_homogeneous e ω hF (fun _ : σ => 1) _
  S_remainder := by
    intro z α
    apply Submodule.mem_sup_right
    have h := F.realFirstCoefficientGradedPolynomial_initial_remainder e ω hF (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) (S (Pi.basisFun ℝ κ z)) α
    rw [hS z, LinearMap.baseChange_tmul] at h
    rw [F.gradedHorizontalKernelBasis_coe]
    exact h
  R_remainder := by
    intro z α
    apply Submodule.mem_sup_right
    have h := F.realFirstCoefficientGradedPolynomial_initial_remainder e ω hF (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) (R (Pi.basisFun ℝ κ z)) α
    rw [hR z, LinearMap.baseChange_tmul] at h
    rw [F.gradedHorizontalKernelBasis_coe]
    exact h
  small_remainder := fun i α => Submodule.mem_sup_right
    (F.realFirstCoefficientGradedPolynomial_mem_second e ω hF (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) (small i) (hsmall i) α)
  rational_remainder := fun i α => Submodule.mem_sup_right
    (F.realFirstCoefficientGradedPolynomial_mem_second e ω hF (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) (rational i) (hrational i) α)
  S_bound := fun z => F.realFirstCoefficientGradedPolynomial_bound e ω hF (fun _ : σ => 1) T hT
    (Real.exp_pos p).le _ (hSbound z)
  R_grid := fun z => F.realFirstCoefficientGradedPolynomial_grid e ω hF (fun _ : σ => 1) l _ (hRgrid z)
  small_bound := fun i => F.realFirstCoefficientGradedPolynomial_bound e ω hF (fun _ : σ => 1) T hT
    (div_nonneg (Real.exp_pos p).le (hT i).le) _ (hsmallBound i)
  rational_grid := fun i => F.realFirstCoefficientGradedPolynomial_grid e ω hF (fun _ : σ => 1) l _ (hrationalGrid i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ ν L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf

theorem exists_initialFormalState_of_quotient_section
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (S R : (κ → ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → κ → ℝ)
    (hSR : ∀ z, S (Pi.basisFun ℝ κ z) = ρ g (R (Pi.basisFun ℝ κ z)))
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      small i + ρ g (rational i) + S (k i))
    (hS : ∀ z, Hq (S (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2))
    (hR : ∀ z, Hq (R (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2))
    (hsmall : ∀ i, Hq (small i) = 0) (hrational : ∀ i, Hq (rational i) = 0)
    (hhorizontal : ∀ i, (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) ∈
        K.baseChange ℝ)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C p q : ℝ)
    (hbudget : C * Real.exp p ≤ Real.exp q)
    (hsectionBound : ∀ M : ℝ, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (C * M) (sectionMap y))
    (l m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp q)
    (hsectionGrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid l →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (hSbound : ∀ z i, |b.equivFun (S (Pi.basisFun ℝ κ z)) i| ≤
      Real.exp p / monomialScale T (rows i).val.1)
    (hRgrid : ∀ z, b.equivFun (R (Pi.basisFun ℝ κ z)) ∈ realDenominatorGrid l)
    (hsmallBound : ∀ j i, |b.equivFun (small j) i| ≤
      (Real.exp p / T j) / monomialScale T (rows i).val.1)
    (hrationalGrid : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) :
    ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
      (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 q,
      X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val := by
  let rep := F.realFastCoefficientRepresentative (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf b sectionMap
  have hrep (x : Q) : (J).mkQ (rep x) = x :=
    F.realFastCoefficientRepresentative_mk (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection x
  have hrepH (x : Q) : F.realFirstCoefficientHorizontal (fun _ : σ => 1) (rep x) = Hq x :=
    F.realFastCoefficientRepresentative_horizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
      Uf b sectionMap hsection x
  have hrepBound {M : ℝ} (hM : 0 ≤ M) (x : Q)
      (hx : ∀ i, |b.equivFun x i| ≤ M / monomialScale T (rows i).val.1) :
      F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (C * M) (rep x) :=
    hsectionBound M hM (b.equivFun x) hx
  have hrepGrid (x : Q) (hx : b.equivFun x ∈ realDenominatorGrid l) :
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (rep x) :=
    hsectionGrid (b.equivFun x) hx
  have hnSR (z : κ) : (J).mkQ ((rep.comp S) (Pi.basisFun ℝ κ z)) =
      ρ g ((J).mkQ ((rep.comp R) (Pi.basisFun ℝ κ z))) := by
    simp only [LinearMap.comp_apply, hrep]
    exact hSR z
  have hnSystem (i : σ) : F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      (J).mkQ (rep (small i)) + ρ g ((J).mkQ (rep (rational i))) + (J).mkQ ((rep.comp S) (k i)) := by
    simp only [LinearMap.comp_apply, hrep]
    exact hsystem i
  have hnSBound (z : κ) : F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T
      (Real.exp q) ((rep.comp S) (Pi.basisFun ℝ κ z)) :=
    FirstCoefficientSlowBound.mono F e ω hF (fun _ : σ => 1) T hT hbudget _
      (hrepBound (Real.exp_pos p).le _ (hSbound z))
  have hnSmallBound (i : σ) : F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T
      (Real.exp q / T i) (rep (small i)) := by
    have hb : C * (Real.exp p / T i) ≤ Real.exp q / T i := by
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right hbudget (hT i).le
    exact FirstCoefficientSlowBound.mono F e ω hF (fun _ : σ => 1) T hT hb _
      (hrepBound (div_nonneg (Real.exp_pos p).le (hT i).le) _ (hsmallBound i))
  let X := F.nativeInitialFormalState e ω hF W hW g K bK (rep.comp S) (rep.comp R)
    (fun i => rep (small i)) (fun i => rep (rational i)) k hnSR hnSystem
    (fun z => (hrepH _).trans (hS z)) (fun z => (hrepH _).trans (hR z))
    (fun i => (hrepH _).trans (hsmall i)) (fun i => (hrepH _).trans (hrational i))
    hhorizontal T hT q m hm hmp hnSBound (fun z => hrepGrid _ (hRgrid z))
    hnSmallBound (fun i => hrepGrid _ (hrationalGrid i))
  exact ⟨X, rfl⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem fastCoefficientSection_budget {p : ℝ} (hp : 0 ≤ p) (a : ℕ) (ha : 1 ≤ a)
    (m : ℕ) (hm : (m : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    Real.exp ((p + 2) ^ a) * Real.exp p ≤ Real.exp ((p + 2) ^ (a + 1)) ∧
      (m : ℝ) ≤ Real.exp ((p + 2) ^ (a + 1)) := by
  constructor
  · rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    calc
      (p + 2) ^ a + p ≤ 2 * (p + 2) ^ a := by linarith [le_power_budget hp ha]
      _ ≤ (p + 2) * (p + 2) ^ a :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (p + 2) ^ (a + 1) := by rw [pow_succ]; ring
  · exact hm.trans (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith) (by omega)))

variable {σ ι κ ν L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf

theorem exists_initialFormalState_of_normalized_quotient
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ)
    (hSR : S = (ρ g).toLinearMap.comp R)
    (hsystem : ∀ i, F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      small i + ρ g (rational i) + S (k i))
    (hS : (Hq).comp S = (K.baseChange ℝ).subtype)
    (hR : (Hq).comp R = (K.baseChange ℝ).subtype)
    (hsmall : ∀ i, Hq (small i) = 0) (hrational : ∀ i, Hq (rational i) = 0)
    (hlinear : ∀ i, (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) =
        (k i).val)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (C p q : ℝ)
    (hbudget : C * Real.exp p ≤ Real.exp q)
    (hsectionBound : ∀ M : ℝ, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (C * M) (sectionMap y))
    (l m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp q)
    (hsectionGrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid l →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (hSbound : ∀ z i, |b.equivFun (S (realSubmoduleBasis K bK z)) i| ≤
      Real.exp p / monomialScale T (rows i).val.1)
    (hRgrid : ∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l)
    (hsmallBound : ∀ j i, |b.equivFun (small j) i| ≤
      (Real.exp p / T j) / monomialScale T (rows i).val.1)
    (hrationalGrid : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) :
    ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
      (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 q,
      X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val := by
  let I := realSubmoduleParameterization K bK
  let Sc := S.comp I.toLinearMap
  let Rc := R.comp I.toLinearMap
  let kc := fun i => I.symm (k i)
  have hSc (z : κ) : Sc (Pi.basisFun ℝ κ z) = S (realSubmoduleBasis K bK z) := by
    change S (realSubmoduleParameterization K bK (Pi.basisFun ℝ κ z)) = _
    rw [realSubmoduleParameterization_basis]
  have hRc (z : κ) : Rc (Pi.basisFun ℝ κ z) = R (realSubmoduleBasis K bK z) := by
    change R (realSubmoduleParameterization K bK (Pi.basisFun ℝ κ z)) = _
    rw [realSubmoduleParameterization_basis]
  have hSRc (z : κ) : Sc (Pi.basisFun ℝ κ z) = ρ g (Rc (Pi.basisFun ℝ κ z)) := by
    exact LinearMap.congr_fun hSR (I (Pi.basisFun ℝ κ z))
  have hScH (z : κ) : Hq (Sc (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2) := by
    have h := LinearMap.congr_fun hS (I (Pi.basisFun ℝ κ z))
    change Hq (Sc (Pi.basisFun ℝ κ z)) = (I (Pi.basisFun ℝ κ z)).val at h
    exact h.trans ((congrArg Subtype.val (realSubmoduleParameterization_basis K bK z)).trans
      (realSubmoduleBasis_coe K bK z))
  have hRcH (z : κ) : Hq (Rc (Pi.basisFun ℝ κ z)) = (1 : ℝ) ⊗ₜ[ℚ] (bK z : L ⧸ F.layer 2) := by
    have h := LinearMap.congr_fun hR (I (Pi.basisFun ℝ κ z))
    change Hq (Rc (Pi.basisFun ℝ κ z)) = (I (Pi.basisFun ℝ κ z)).val at h
    exact h.trans ((congrArg Subtype.val (realSubmoduleParameterization_basis K bK z)).trans
      (realSubmoduleBasis_coe K bK z))
  have hsys (i : σ) : F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1) =
      small i + ρ g (rational i) + Sc (kc i) := by
    change _ = small i + ρ g (rational i) + S (I (I.symm (k i)))
    rw [LinearEquiv.apply_symm_apply]
    exact hsystem i
  apply F.exists_initialFormalState_of_quotient_section e ω hF W hW g K bK b rows sectionMap hsection
    Sc Rc small rational kc hSRc hsys hScH hRcH hsmall hrational
    (fun i => (hlinear i).symm ▸ (k i).property) T hT C p q hbudget hsectionBound l m hm hmp hsectionGrid
  · intro z i
    exact (congrArg (fun x : Q => |b.equivFun x i|) (hSc z)).le.trans (hSbound z i)
  · intro z
    exact (congrArg (fun x : Q => b.equivFun x ∈ realDenominatorGrid l) (hRc z)).mpr (hRgrid z)
  · exact hsmallBound
  · exact hrationalGrid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ ι κ ν L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "Y" => (fun (g : G) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

theorem exists_initialFormalState_after_removal
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) (a g c : G)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ)
    (hSR : S = (ρ (a * g * c)).toLinearMap.comp R)
    (hsystem : ∀ i, Y (a * g * c) i = small i + ρ (a * g * c) (rational i) + S (k i))
    (hS : (Hq).comp S = (K.baseChange ℝ).subtype)
    (hR : (Hq).comp R = (K.baseChange ℝ).subtype)
    (haH : ∀ i, Hq (Y a i) = Hq (small i)) (hcH : ∀ i, Hq (Y c i) = Hq (rational i))
    (hlinear : ∀ i, (F.layer 2).mkQ.baseChange ℝ
      (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) =
        (k i).val)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (D M B A C p q : ℝ) (hD : 0 ≤ D)
    (haction : ∀ x, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) ((ρ a).symm x)‖ ≤
      D * ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) x‖)
    (hsmall : ∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤ M / T i)
    (hYa : ∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (Y a i)‖ ≤ A / T i)
    (hSbound : ∀ z, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
      (S (realSubmoduleBasis K bK z))‖ ≤ B)
    (hSBudget : D * B ≤ Real.exp p) (hsmallBudget : D * (M + A) ≤ Real.exp p)
    (hsectionBudget : C * Real.exp p ≤ Real.exp q)
    (hsectionBound : ∀ N : ℝ, 0 ≤ N → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ N / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (C * N) (sectionMap y))
    (l r m : ℕ) (hm : 0 < m) (hmp : (m : ℝ) ≤ Real.exp q)
    (hsectionGrid : ∀ y : ν → ℝ, y ∈ realDenominatorGrid r →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m (sectionMap y))
    (hRgrid : ∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l)
    (hrational : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l)
    (hc : ∀ x, b.equivFun x ∈ realDenominatorGrid l → b.equivFun (ρ c x) ∈ realDenominatorGrid r)
    (hYc : ∀ i, b.equivFun (Y c i) ∈ realDenominatorGrid r) :
    ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
      (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 q,
      X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val := by
  let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
  let Sn := (ρ a).symm.toLinearMap.comp S
  let Rn := (ρ c).toLinearMap.comp R
  let smalln := fun i => (ρ a).symm (small i - Y a i)
  let rationaln := fun i => ρ c (rational i) - Y c i
  have hnSR : Sn = (ρ g).toLinearMap.comp Rn :=
    F.realFastCoefficient_remove_lifts (K := K.baseChange ℝ) Wf a g c S R hSR
  have hnH : (Hq).comp Sn = (K.baseChange ℝ).subtype ∧
      (Hq).comp Rn = (K.baseChange ℝ).subtype :=
    F.realFastCoefficient_remove_horizontal_lifts (K := K.baseChange ℝ) Wf e ω hF a c S R
      (K.baseChange ℝ).subtype hS hR
  have hnSystem (i : σ) := F.realFastCoefficient_remove_derivative Wf e ω hF a g c
    (Pi.single i 1) (small i) (rational i) (S (k i)) (hsystem i)
  have hnHorizontal (i : σ) : Hq (smalln i) = 0 ∧ Hq (rationaln i) = 0 :=
    horizontal_remove_zero Hq (ρ a) (ρ c)
      (F.realFastCoefficientAction_horizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf e ω hF a)
      (F.realFastCoefficientAction_horizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf e ω hF c)
      (small i) (rational i) (Y a i) (Y c i) (haH i) (hcH i)
  apply F.exists_initialFormalState_of_normalized_quotient e ω hF W hW g K bK b rows sectionMap hsection
    Sn Rn smalln rationaln k hnSR hnSystem hnH.1 hnH.2
    (fun i => (hnHorizontal i).1) (fun i => (hnHorizontal i).2) hlinear T hT C p q
    hsectionBudget hsectionBound r m hm hmp hsectionGrid
  · intro z i
    have hz : ‖N (Sn (realSubmoduleBasis K bK z))‖ ≤ Real.exp p :=
      (haction _).trans ((mul_le_mul_of_nonneg_left (hSbound z) hD).trans hSBudget)
    exact (basisWeightedCoordinates_norm_le_iff b _ (fun j => monomialScale_pos T hT _)
      (Real.exp_pos p).le _).mp hz i
  · exact fun z => hc _ (hRgrid z)
  · intro j i
    have hj : ‖N (smalln j)‖ ≤ Real.exp p / T j :=
      (norm_removed_derivative_bound N (ρ a).symm.toLinearMap (small j) (Y a j)
        D M A (T j) hD (hT j) haction (hsmall j) (hYa j)).trans
          (div_le_div_of_nonneg_right hsmallBudget (hT j).le)
    exact (basisWeightedCoordinates_norm_le_iff b _ (fun i => monomialScale_pos T hT _)
      (div_nonneg (Real.exp_pos p).le (hT j).le) _).mp hj i
  · intro i
    change b.equivFun (ρ c (rational i) - Y c i) ∈ realDenominatorGrid r
    rw [map_sub]
    exact realDenominatorGrid_sub r _ _ (hc _ (hrational i)) (hYc i)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

def ControlledInitialRemovalSpec (s aExp C : ℕ) : Prop :=
    ∀ {σ ι κ ν L : Type*} [Fintype σ] [DecidableEq σ] [Fintype ι]
      [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (H : ℕ) (p : ℝ), 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H) →
      ∀ W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded,
      let Wf := F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
      let E := F.RealFirstCoefficientModule (fun _ : σ => 1)
      let J := F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
      let Q := E ⧸ J
      let G := F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
      let ρ := F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
      let Hq := F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
        (F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf)
      let Y := fun (g : G) i => F.realFastCoefficientDirectionMap Wf g.val (Pi.single i 1)
      BasisGradedSubmodule
        (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
          (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val)
          (F.reducedSquareBasis_layers e ω hF))
        (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val) W.toSubmodule →
      ∀ (a g c : G) (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
        (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
        (sectionMap : (ν → ℝ) →ₗ[ℝ] E),
      (∀ y, J.mkQ (sectionMap y) = b.equivFun.symm y) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ Kscale : ℝ, 0 ≤ Kscale → Kscale ≤ Real.exp p →
      (∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
        ∀ i, |b.equivFun (J.mkQ x) i| ≤ Kscale * M / monomialScale T (rows i).val.1) →
      (∀ M, 0 ≤ M → ∀ y : ν → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Kscale * M) (sectionMap y)) →
      ∀ l δ : ℕ, 0 < l → 0 < δ → ((δ * l : ℕ) : ℝ) ≤ Real.exp p →
      (∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
        b.equivFun (J.mkQ x) ∈ realDenominatorGrid (δ * m)) →
      (∀ m (y : ν → ℝ), y ∈ realDenominatorGrid m →
        F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y)) →
      F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T
        (Real.exp ((p + 2) ^ aExp)) a.val.coord →
      F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) (δ * l) c.val.coord →
      ∀ (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ),
      S = (ρ (a * g * c)).toLinearMap.comp R →
      (∀ i, Y (a * g * c) i = small i + ρ (a * g * c) (rational i) + S (k i)) →
      Hq.comp S = (K.baseChange ℝ).subtype → Hq.comp R = (K.baseChange ℝ).subtype →
      (∀ i, Hq (Y a i) = Hq (small i)) → (∀ i, Hq (Y c i) = Hq (rational i)) →
      (∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) =
          (k i).val) →
      (∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
        Real.exp p / T i) →
      (∀ z, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
        (S (realSubmoduleBasis K bK z))‖ ≤ Real.exp p) →
      (∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l) →
      (∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l) →
      ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
        (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
        (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
        (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((p + C) ^ C),
        X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

theorem exists_controlled_initialFormalState_after_removal (s aExp : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledInitialRemovalSpec s aExp C := by
  have hslowExists := exists_fastCoefficient_slow_removal_bound s aExp
  obtain ⟨cS, _, hslow⟩ := hslowExists
  have hgridExists := exists_fastCoefficient_rational_removal_grid s
  obtain ⟨cR, _, hgrid⟩ := hgridExists
  obtain ⟨C, hC, hbudget⟩ := exists_initial_removal_budget cS cR
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ν L _ _ _ _ _ _ _ F e ω hF H p hH hp hι hσ hHp hstructure
    W Wf E J Q G ρ Hq Y hW a g c K bK b rows sectionMap hsection T hT Kscale hKscale hKscalep
    hprojection hsectionBound l δ hl hδ hδlp hprojectionGrid hsectionGrid ha hc
    S R small rational k hSR hsystem hS hR haH hcH hlinear hsmall hSbound hRgrid hrational
  have hδp : (δ : ℝ) ≤ Real.exp p := by
    have hlone : (1 : ℝ) ≤ l := by exact_mod_cast hl
    calc
      (δ : ℝ) ≤ (δ : ℝ) * l := le_mul_of_one_le_right (Nat.cast_nonneg _) hlone
      _ = ((δ * l : ℕ) : ℝ) := (Nat.cast_mul _ _).symm
      _ ≤ Real.exp p := hδlp
  have hslowData := hslow F e ω hF H p hH hp hι hσ hHp hstructure
    Wf b sectionMap hsection rows T hT Kscale hKscale hKscalep hprojection hsectionBound a ha
  have hgridData := hgrid F e ω hF H p hH hp hι hσ hHp hstructure
    Wf b sectionMap hsection l (δ * l) δ (Nat.mul_pos hδ hl) hδlp hδ hδp
    (hsectionGrid l) hprojectionGrid
  obtain ⟨r, hr, hrp, hactionGrid⟩ := hgridData
  have hcData := hactionGrid c hc
  have hYc : ∀ i, b.equivFun (Y c i) ∈ realDenominatorGrid r := by
    intro i
    have hcast : (fun j => (((Pi.single i 1 : σ → ℤ) j) : ℝ)) =
        (Pi.single i 1 : σ → ℝ) := by
      funext j
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    have hi := hcData.2.1 (Pi.single i 1)
    rw [hcast] at hi
    exact hi
  obtain ⟨hSBudget, hsmallBudget, hsectionBudget, hgridBudget⟩ := hbudget p hp
  have hsectionFinal : Kscale * Real.exp (p + 1 + 2 * (p + cS) ^ cS) ≤
      Real.exp ((p + C) ^ C) :=
    (mul_le_mul_of_nonneg_right hKscalep (Real.exp_nonneg _)).trans hsectionBudget
  have hdenomFinal : ((δ * r : ℕ) : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hδp hrp (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans hgridBudget
  exact F.exists_initialFormalState_after_removal e ω hF W hW a g c K bK b rows sectionMap hsection
    S R small rational k hSR hsystem hS hR haH hcH hlinear T hT
    (Real.exp ((p + cS) ^ cS)) (Real.exp p) (Real.exp p) (Real.exp ((p + cS) ^ cS))
    Kscale (p + 1 + 2 * (p + cS) ^ cS) ((p + C) ^ C) (Real.exp_nonneg _)
    hslowData.1 hsmall hslowData.2.1 hSbound hSBudget hsmallBudget
    hsectionFinal hsectionBound l r (δ * r) (Nat.mul_pos hδ hr) hdenomFinal
    (hsectionGrid r) hRgrid hrational hcData.1 hYc

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

universe uσ uι uκ uν uL

variable {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι]
  [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "Y" => (fun (g : G) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))
local notation "UH" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

def HorizontalInitialStateSpec (aExp C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (Kscale : ℝ) (_hKscale : 0 ≤ Kscale) (_hKscalep : Kscale ≤ Real.exp p)
    (_hprojection : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
      ∀ i, |b.equivFun ((J).mkQ x) i| ≤ Kscale * M / monomialScale T (rows i).val.1)
    (_hsectionBound : ∀ M, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Kscale * M) (sectionMap y))
    (l δ : ℕ) (_hl : 0 < l) (_hδ : 0 < δ) (_hδlp : ((δ * l : ℕ) : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : ν → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ)
    (_hSR : S = (ρ g₀).toLinearMap.comp R)
    (_hsystem : ∀ i, Y g₀ i = small i + ρ g₀ (rational i) + S (k i))
    (_hS : (Hq).comp S = (K.baseChange ℝ).subtype)
    (_hR : (Hq).comp R = (K.baseChange ℝ).subtype)
    (_hsmallH : ∀ i, Hq (small i) ∈ UH) (_hrationalH : ∀ i, Hq (rational i) ∈ UH)
    (_hkH : ∀ i, (k i).val ∈ UH)
    (_hsmall : ∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
      Real.exp p / T i)
    (_hSbound : ∀ z, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
      (S (realSubmoduleBasis K bK z))‖ ≤ Real.exp p)
    (_hRgrid : ∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l)
    (_hrational : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l),
    ∃ a g c : G, a * g * c = g₀ ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp ((p + 2) ^ aExp)) a.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) (δ * l) c.val.coord ∧
      ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
        (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
        (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
        (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((p + C) ^ C),
        X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

theorem exists_initialFormalState_of_horizontal_data
    (aExp C : ℕ) (haExp : 2 ≤ aExp)
    (hcontrol : ControlledInitialRemovalSpec.{uσ, uι, uκ, uν, uL} s aExp C) :
    F.HorizontalInitialStateSpec (σ := σ) (κ := κ) (ν := ν) e ω hF W aExp C := by
  intro H p hH hp hι hσ hHp hstructure hW g₀ hzero K bK b rows sectionMap hsection
    T hT Kscale hKscale hKscalep hprojection hsectionBound l δ hl hδ hδlp
    hprojectionGrid hsectionGrid S R small rational k hSR hsystem hS hR
    hsmallH hrationalH hkH hsmall hSbound hRgrid hrational
  have hraw := hcontrol (σ := σ) (ι := ι) (κ := κ) (ν := ν) (L := L)
    F e ω hF H p hH hp hι hσ hHp hstructure W
  have hraw' := hraw hW
  have hfinish (a g c : G) (hfactor : a * g * c = g₀)
      (habound : F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T
        (Real.exp ((p + 2) ^ aExp)) a.val.coord)
      (hcgrid : F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) (δ * l) c.val.coord)
      (hlinear : ∀ i, (F.layer 2).mkQ.baseChange ℝ
        (coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g.val.coord) (Finsupp.single i 1)) =
          (k i).val)
      (haH : ∀ i, Hq (Y a i) = Hq (small i))
      (hcH : ∀ i, Hq (Y c i) = Hq (rational i)) :
      ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
        (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
        (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
        (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((p + C) ^ C),
        X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val := by
    as_aux_lemma =>
      have hSR' : S = (ρ (a * g * c)).toLinearMap.comp R := by
        simpa only [hfactor] using hSR
      have hsystem' (i : σ) : Y (a * g * c) i = small i + ρ (a * g * c) (rational i) + S (k i) := by
        simpa only [hfactor] using hsystem i
      have hresult := hraw' a g c K bK b rows sectionMap hsection T hT Kscale hKscale hKscalep
        hprojection hsectionBound l δ hl hδ hδlp hprojectionGrid hsectionGrid habound hcgrid
        S R small rational k hSR' hsystem' hS hR haH hcH hlinear hsmall hSbound hRgrid hrational
      exact hresult
  have hsize : Kscale * Real.exp p ≤ Real.exp ((p + 2) ^ aExp) := by
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul_of_nonneg_right hKscalep (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp ((p + 2) ^ aExp) := by
        apply Real.exp_le_exp.mpr
        exact (show 2 * p ≤ (p + 2) ^ 2 by nlinarith [sq_nonneg p]).trans
          (pow_le_pow_right₀ (by linarith) haExp)
  have hsmallHorizontalBound (i : σ) :
      ‖cH (Hq (small i))‖ ≤ Real.exp ((p + 2) ^ aExp) / T i := by
    calc
      _ ≤ Kscale * ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ :=
        F.realFastCoefficientHorizontal_section_norm_bound e ω hF (fun _ => 1)
          (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection rows T hT
          Kscale hKscale hsectionBound (small i)
      _ ≤ Kscale * (Real.exp p / T i) := mul_le_mul_of_nonneg_left (hsmall i) hKscale
      _ = (Kscale * Real.exp p) / T i := (mul_div_assoc _ _ _).symm
      _ ≤ _ := div_le_div_of_nonneg_right hsize (hT i).le
  have hrationalHorizontalGrid (i : σ) : cH (Hq (rational i)) ∈ realDenominatorGrid (δ * l) :=
    F.realFastCoefficientHorizontal_section_grid e ω hF (fun _ => 1)
      (fun _ => Nat.zero_lt_one) Uf b sectionMap hsection l (δ * l)
      (hsectionGrid l) (rational i) (hrational i)
  have hnorm := F.realFast_controlled_horizontal_factorization e ω hF
    (F.fullFastGradedDiagonal W) Wf
    (F.fullFastPointwise_image_le e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW)
    g₀ hzero (K.baseChange ℝ) S R hSR hS hR small rational k hsystem hsmallH hrationalH hkH
    T hT (Real.exp ((p + 2) ^ aExp)) (Real.exp_nonneg _) hsmallHorizontalBound
    (δ * l) hrationalHorizontalGrid
  obtain ⟨a, g, c, hfactor, habound, hcgrid, hlinear, haH, hcH⟩ := hnorm
  exact ⟨a, g, c, hfactor, habound, hcgrid, hfinish a g c hfactor habound hcgrid hlinear haH hcH⟩

theorem exists_horizontal_initialState_bound (s aExp : ℕ) (haExp : 2 ≤ aExp) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι]
        [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.HorizontalInitialStateSpec (σ := σ) (κ := κ) (ν := ν) e ω hF W aExp C := by
  have h := exists_controlled_initialFormalState_after_removal.{uσ, uι, uκ, uν, uL} s aExp
  obtain ⟨C, hC, hcontrol⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ν L _ _ _ _ _ _ _ F e ω hF W
  exact F.exists_initialFormalState_of_horizontal_data e ω hF W aExp C haExp hcontrol

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uκ uν uτ uL

variable {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "Y" => (fun (g : G) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

def AbsorbedInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (_hsize : ((Fintype.card τ + Fintype.card ι + Fintype.card κ : ℕ) : ℝ) ≤ p)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis κ ℚ K)
    (_hKb : ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) H)
    (b : Basis ν ℝ Q) (rows : ν → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (ν → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (Kscale : ℝ) (_hKscale : 0 ≤ Kscale) (_hKscalep : Kscale ≤ Real.exp p)
    (_hprojection : ∀ M, 0 ≤ M → ∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x →
      ∀ i, |b.equivFun ((J).mkQ x) i| ≤ Kscale * M / monomialScale T (rows i).val.1)
    (_hsectionBound : ∀ M, 0 ≤ M → ∀ y : ν → ℝ,
      (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Kscale * M) (sectionMap y))
    (l δ : ℕ) (_hl : 0 < l) (_hδ : 0 < δ) (_hδlp : ((δ * l : ℕ) : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : ν → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (S R : (K.baseChange ℝ) →ₗ[ℝ] Q) (small rational : σ → Q) (k : σ → K.baseChange ℝ)
    (_hSR : S = (ρ g₀).toLinearMap.comp R)
    (_hsystem : ∀ i, Y g₀ i = small i + ρ g₀ (rational i) + S (k i))
    (_hS : (Hq).comp S = (K.baseChange ℝ).subtype)
    (_hR : (Hq).comp R = (K.baseChange ℝ).subtype)
    (_hsmallH : ∀ i, ‖cH (Hq (small i))‖ ≤ Real.exp p / T i)
    (_hsmall : ∀ i, ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
      Real.exp p / T i)
    (_hSbound : ∀ x, ‖basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1) (S x)‖ ≤
      Real.exp p * ‖cH x.val‖)
    (_hRgrid : ∀ z, b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l)
    (_hrational : ∀ i, b.equivFun (rational i) ∈ realDenominatorGrid l),
    ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ Real.exp (absorbedInitialParameter p) ∧
      ∃ a g c : G, a * g * c = g₀ ∧
        F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T
          (Real.exp ((absorbedInitialParameter p + 2) ^ 2)) a.val.coord ∧
        F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) d c.val.coord ∧
        ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
          (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
          (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
          (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((absorbedInitialParameter p + C) ^ C),
          X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

theorem exists_initialFormalState_after_absorption (C : ℕ)
    (hinit : F.HorizontalInitialStateSpec (σ := σ) (κ := κ) (ν := ν) e ω hF W 2 C) :
    F.AbsorbedInitialStateSpec (σ := σ) (κ := κ) (ν := ν) (τ := τ) e ω hF W C := by
  intro H p hH hp hι hσ hHp hstructure hW v hv hheight hsize g₀ hzero K bK hKb
    b rows sectionMap hsection T hT Kscale hKscale hKscalep hprojection hsectionBound
    l δ hl hδ hδlp hprojectionGrid hsectionGrid S R small rational k hSR hsystem hS hR
    hsmallH hsmall hSbound hRgrid hrational
  let N := basisWeightedCoordinates b (fun i => monomialScale T (rows i).val.1)
  let A := submoduleBasisMatrix (F.layerOneBasis e ω hF) K bK
  have hAspan := realSubmoduleBasis_matrix_span (F.layerOneBasis e ω hF) K bK
  have hAcol := realSubmoduleBasis_matrix_coordinates (F.layerOneBasis e ω hF) K bK
  have hA : ∀ i j, RationalHeightLE (A i j) H := hKb
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hrH (i : σ) : cH (Hq (rational i)) ∈ realDenominatorGrid (δ * l) :=
    F.realFastCoefficientHorizontal_section_grid e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Uf b sectionMap hsection l (δ * l) (hsectionGrid l) (rational i) (hrational i)
  have habs := F.exists_fullFast_derivative_absorption e ω hF W hW v hv g₀ hzero
    (K.baseChange ℝ) A hAspan (realSubmoduleBasis K bK) hAcol S R hSR hS hR
    b.equivFun.toLinearMap N l l hRgrid hH (Nat.mul_pos hδ hl) hheight hA hp hsize hHp hδlp
    T hT (Real.exp p) (Real.exp p) (Real.exp_nonneg _) hSbound small rational k hsystem
    hsmallH hsmall hrH hrational
  obtain ⟨m, hm, hmp, ks, kr, habs⟩ := habs
  let small₀ := fun i => small i - S (ks i)
  let rational₀ := fun i => rational i - R (kr i)
  let k₀ := fun i => k i + ks i + kr i
  let l₀ := l * (l * m)
  have hbudget := absorbedInitialParameter_bounds hp
  have hep : Real.exp p ≤ Real.exp (absorbedInitialParameter p) := Real.exp_le_exp.mpr hbudget.1
  have hlp : (l : ℝ) ≤ Real.exp p := by
    have hd : (1 : ℝ) ≤ δ := by exact_mod_cast hδ
    have h := le_mul_of_one_le_left (Nat.cast_nonneg l) hd
    exact h.trans (by simpa only [Nat.cast_mul] using hδlp)
  have hδp : (δ : ℝ) ≤ Real.exp p := by
    have hlone : (1 : ℝ) ≤ l := by exact_mod_cast hl
    have h := le_mul_of_one_le_right (Nat.cast_nonneg δ) hlone
    exact h.trans (by simpa only [Nat.cast_mul] using hδlp)
  have hl₀ : 0 < l₀ := Nat.mul_pos hl (Nat.mul_pos hl hm)
  have hdenom : ((δ * l₀ : ℕ) : ℝ) ≤ Real.exp (absorbedInitialParameter p) := by
    simp only [l₀, Nat.cast_mul]
    apply le_trans _ hbudget.2.2
    gcongr
  have hRgrid₀ (z : κ) : b.equivFun (R (realSubmoduleBasis K bK z)) ∈ realDenominatorGrid l₀ :=
    realDenominatorGrid_subset_of_dvd hl (dvd_mul_right l (l * m)) (hRgrid z)
  have hsmall₀ (i : σ) : ‖N (small₀ i)‖ ≤ Real.exp (absorbedInitialParameter p) / T i := by
    have hi := (habs i).2.2.2.2.2.1
    exact hi.trans (div_le_div_of_nonneg_right hbudget.2.1 (hTpos i).le)
  have hSbasis (z : κ) : ‖N (S (realSubmoduleBasis K bK z))‖ ≤
      Real.exp (absorbedInitialParameter p) := by
    have hnorm : ‖cH (realSubmoduleBasis K bK z).val‖ ≤ (H : ℝ) := by
      rw [hAcol z]
      apply (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg H)).mpr
      intro i
      exact (hA i z).abs_real_le
    have htwo : 2 * p ≤ absorbedInitialParameter p := by
      unfold absorbedInitialParameter
      have h19 : 0 ≤ (p + 2) ^ 19 := by positivity
      have h36 : 0 ≤ (p + 2) ^ 36 := by positivity
      linarith
    calc
      _ ≤ Real.exp p * (H : ℝ) := (hSbound _).trans (mul_le_mul_of_nonneg_left hnorm (Real.exp_nonneg _))
      _ ≤ Real.exp p * Real.exp p := mul_le_mul_of_nonneg_left hHp (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr htwo
  have hout := hinit H (absorbedInitialParameter p) hH (absorbedInitialParameter_nonneg hp)
    (hι.trans hbudget.1) (hσ.trans hbudget.1) (hHp.trans hep) hstructure hW g₀ hzero K bK
    b rows sectionMap hsection T hTpos Kscale hKscale (hKscalep.trans hep) hprojection hsectionBound
    l₀ δ hl₀ hδ hdenom hprojectionGrid hsectionGrid S R small₀ rational₀ k₀ hSR
    (fun i => (habs i).2.2.2.1) hS hR (fun i => (habs i).1)
    (fun i => (habs i).2.1) (fun i => (habs i).2.2.1)
    hsmall₀ hSbasis hRgrid₀ (fun i => (habs i).2.2.2.2.2.2.2)
  exact ⟨δ * l₀, Nat.mul_pos hδ hl₀, hdenom, hout⟩

theorem exists_absorbed_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {κ : Type uκ} {ν : Type uν} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype τ]
        [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.AbsorbedInitialStateSpec (σ := σ) (κ := κ) (ν := ν) (τ := τ) e ω hF W C := by
  have h := exists_horizontal_initialState_bound.{uσ, uι, uκ, uν, uL} s 2 (by decide)
  obtain ⟨C, hC, hinit⟩ := h
  refine ⟨C, hC, ?_⟩
  intro σ ι κ ν τ L _ _ _ _ _ _ _ _ F e ω hF W
  exact F.exists_initialFormalState_after_absorption e ω hF W C (hinit F e ω hF W)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s a d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Hq" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))

def ExtractedInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hap : (a : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (b : Basis (Fin d) ℝ Q) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (ha : a ≤ d) (η : (Fin a → ℝ) ≃ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2)))
    (_hη : ∀ x, η (fun i => b.equivFun x (Fin.castLE ha i)) = Hq x)
    (sectionMap : (Fin d → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (Cscale : ℝ) (_hC : 0 ≤ Cscale) (_hCp : Cscale ≤ Real.exp p)
    (_hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x → ∀ i,
        |b.equivFun ((J).mkQ x) i| ≤ Cscale * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Cscale * M) (sectionMap y)))
    (δ : ℕ) (_hδ : 0 < δ) (_hδp : (δ : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : Fin d → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (B : ℝ) (_hB : 0 ≤ B) (_hBp : B ≤ Real.exp p)
    (D : CoordinateDerivativeSystem ha T
      (b.equivFun.toLinearMap.comp (F.realFastCoefficientDirectionMap Wf g₀.val))
      (b.equivFun.symm.trans ((ρ g₀).trans b.equivFun))
      (fun i => monomialScale T (rows i).val.1) B),
    D.k ≤ a ∧ ∃ (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin D.k) ℚ K),
      ∃ Hk : ℕ, 1 ≤ Hk ∧ (Hk : ℝ) ≤ Real.exp ((p + 2) ^ 3) ∧
        (∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) Hk) ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ x g z : G, x * g * z = g₀ ∧
            F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T
              (Real.exp ((p + C) ^ C)) x.val.coord ∧
            F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) m z.val.coord ∧
            ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
              (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
              (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
              (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 ((p + C) ^ C),
              X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

theorem exists_initialFormalState_from_extraction (C D : ℕ)
    (hbudget : ∀ p : ℝ, 0 ≤ p →
      separationBudget (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      absorbedInitialParameter (extractedInitialParameter p) ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + 2) ^ 2 ≤ (p + D) ^ D ∧
      (absorbedInitialParameter (extractedInitialParameter p) + C) ^ C ≤ (p + D) ^ D)
    (habs : ∀ r : ℕ, F.AbsorbedInitialStateSpec (σ := σ) (κ := Fin r) (ν := Fin d)
      (τ := τ) e ω hF W C) :
    F.ExtractedInitialStateSpec (σ := σ) (τ := τ) (a := a) (d := d) e ω hF W D := by
  intro H p hH hp hι hσ hτ hap hHp hstructure hW v hv hheight g₀ hzero
    b rows ha η hη sectionMap hsection Cscale hC hCp hweighted δ hδ hδp
    hprojectionGrid hsectionGrid T hT B hB hBp sys
  let q := extractedInitialParameter p
  have hq := extractedInitialParameter_controls hp
  have hqpos : 0 ≤ q := hp.trans hq.1
  have hep : Real.exp p ≤ Real.exp q := Real.exp_le_exp.mpr hq.1
  have hb := hbudget p hp
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTq (i : σ) : Real.exp (separationBudget q) ≤ T i :=
    (Real.exp_le_exp.mpr hb.1).trans (hT i)
  have hgrid (y : Fin d → ℝ) (hy : y ∈ realDenominatorGrid 1) :
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) δ (sectionMap y) :=
    (congrArg (fun n => F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) n (sectionMap y))
      (Nat.mul_one δ)).mp (hsectionGrid 1 y hy)
  have hnative := F.exists_native_coordinate_derivative_system e ω hF Wf
    b rows ha η hη sectionMap hsection Cscale hC hweighted δ hδ hgrid T hTpos
    g₀ B hB sys p hp hap hδp hCp (sys.height_le.trans hBp)
  obtain ⟨hk, K, bK, Hk, hHk, hHkp, hKheight, l, hl, hlB, S, R, hSR, hS, hR,
    hSnorm, hRgrid, small, rational, k, hsystem, hrgrid, hsmall, hsmallH⟩ := hnative
  have hcommon : ((max H Hk : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hHp.trans hep) (hHkp.trans (Real.exp_le_exp.mpr hq.2.2))
  have hkcard : (Fintype.card (Fin sys.k) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr hk).trans hap
  have hsize : ((Fintype.card τ + Fintype.card ι + Fintype.card (Fin sys.k) : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_add, Nat.cast_add]
    calc
      _ ≤ p + p + p := add_le_add (add_le_add hτ hι) hkcard
      _ ≤ q := by linarith [hq.2.1]
  have hproducts := extractedInitialParameter_products hp hB hBp hC hCp δ l hδp hlB
  have hsmallq (i : σ) :
      ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (small i)‖ ≤
        Real.exp q / T i :=
    (hsmall i).trans (div_le_div_of_nonneg_right (hBp.trans hep) (hTpos i).le)
  have hsmallHq (i : σ) : ‖cH (Hq (small i))‖ ≤ Real.exp q / T i := by
    have hCB : Cscale * B ≤ Real.exp q := (mul_comm Cscale B).trans_le hproducts.1
    exact (hsmallH i).trans (div_le_div_of_nonneg_right hCB (hTpos i).le)
  have hSq (x : K.baseChange ℝ) :
      ‖basisWeightedCoordinates b (fun j => monomialScale T (rows j).val.1) (S x)‖ ≤
        Real.exp q * ‖cH x.val‖ :=
    (hSnorm x).trans (mul_le_mul_of_nonneg_right hproducts.1 (norm_nonneg _))
  have hout := habs sys.k (max H Hk) q (hH.trans (le_max_left _ _)) hqpos
    (hι.trans hq.1) (hσ.trans hq.1) hcommon
    (fun i j k => (hstructure i j k).mono (le_max_left _ _)) hW v hv
    (fun j i => (hheight j i).mono (le_max_left _ _)) hsize g₀ hzero K bK
    (fun i j => (hKheight i j).mono (le_max_right _ _)) b rows sectionMap hsection T hTq
    Cscale hC (hCp.trans hep) (fun M hM => (hweighted T hTpos M hM).1)
    (fun M hM => (hweighted T hTpos M hM).2) l δ hl hδ hproducts.2
    hprojectionGrid hsectionGrid S R small rational k hSR hsystem hS hR
    hsmallHq hsmallq hSq hRgrid hrgrid
  obtain ⟨m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := hout
  refine ⟨hk, K, bK, Hk, hHk, hHkp, hKheight, m, hm,
    hmp.trans (Real.exp_le_exp.mpr hb.2.1), x, g, z, hfactor, ?_, hz,
    X.enlarge hb.2.2.2 hTpos, hX⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hTpos
    (Real.exp_le_exp.mpr hb.2.2.1) x.val.coord hx

theorem exists_extracted_initialState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) (a d : ℕ),
        F.ExtractedInitialStateSpec (σ := σ) (τ := τ) (a := a) (d := d) e ω hF W C := by
  have h := exists_absorbed_initialState_bound.{uσ, uι, 0, 0, uτ, uL} s
  obtain ⟨C, _, habs⟩ := h
  obtain ⟨D, hD, hbudget⟩ := exists_extractedInitialParameter_budget C
  refine ⟨D, hD, ?_⟩
  intro σ ι τ L _ _ _ _ _ _ F e ω hF W a d
  exact F.exists_initialFormalState_from_extraction e ω hF W C D hbudget
    (fun r => habs (κ := Fin r) (ν := Fin d) F e ω hF W)

end Erdos3.NilpotentLieFiltration

end

end OAI
