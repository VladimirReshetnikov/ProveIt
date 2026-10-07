/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.UniformFormalCurrentLayerStep
import OAI.Combinatorics.Progressions.Polynomial.PolynomialKernelDirectionBudget

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

theorem formal_invariant_correction_preserves_derivative_remainder
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (j : ℕ)
    (A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule) :
    ∀ i α, coefficients (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)) α ∈
        V ⊔ (F.realLayer j).toSubmodule ∧
      coefficients (dualAdjoint B (rational i) - formalLogDerivative i B) α ∈
        V ⊔ (F.realLayer j).toSubmodule := by
  let W := V.restrictScalars ℚ ⊔ F.realification.layer j
  have hWiff (x : ℝ ⊗[ℚ] L) : x ∈ W ↔ x ∈ V ⊔ (F.realLayer j).toSubmodule := by
    change x ∈ V.restrictScalars ℚ ⊔ (F.realLayer j).toSubmodule.restrictScalars ℚ ↔ _
    rw [← Submodule.restrictScalars_sup]
    rfl
  intro i α
  have h := polynomial_derivative_removal_preserves_coefficients U W
    (F.realification.invariant_sup_layer U (V.restrictScalars ℚ) hUV j)
    i A B (small i) (rational i) hAU hBU
    (fun β => Submodule.mem_sup_left (hAV β)) (fun β => Submodule.mem_sup_left (hBV β))
    (fun β => (hWiff _).mpr (hsmall i β)) (fun β => (hWiff _).mpr (hrational i β))
  exact ⟨(hWiff _).mp (h.1 α), (hWiff _).mp (h.2 α)⟩

include hF in
theorem formal_invariant_bracket_derivative_step (hs : 2 ≤ s)
    (U : LieSubalgebra ℚ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hAV : ∀ α, coefficients A.coord α ∈ V) (hBV : ∀ α, coefficients B.coord α ∈ V)
    (S : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : σ → κ) (I : κ → ℝ ⊗[ℚ] L)
    (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A)
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B
    let extra' := fun i => dualAdjoint A⁻¹ (S (k i))
    PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule := by
  intro P' small' rational' extra'
  have hnew := PolynomialDerivativeSystemMod.remove U (V.restrictScalars ℚ) hUV P A B hAU
    small rational (fun i => S (k i)) hsystem
  have hrem := F.formal_invariant_correction_preserves_derivative_remainder U V hUV j A B
    hAU hBU hAV hBV small rational hsmall hrational
  have hmono : V ⊔ (F.realLayer j).toSubmodule ≤ V ⊔ (F.realLayer 2).toSubmodule := by
    apply sup_le_sup_left _ V
    intro x hx
    exact F.realification.antitone hj hx
  refine ⟨hnew, hrem, ?_⟩
  apply F.formal_extra_horizontal_equation b w hF hs V hV j P' small' rational' extra'
    hnew (fun i α => hmono (hrem i α).1) (fun i α => hmono (hrem i α).2)
  intro i
  exact F.formal_lift_nonhorizontal_remainder b w hF V hV (by omega : 1 ≤ j)
    (extra' i) (I (k i)) (hI _) (hS _)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_bracket_correction_preserves_log_conditions
    (V K : Submodule ℝ (ℝ ⊗[ℚ] L)) {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAK : j = 2 → ∀ α, coefficients A.coord α ∈ K)
    (hBK : j = 2 → ∀ α, coefficients B.coord α ∈ K)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V) :
    (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ K) ∧
      ∀ α d, 2 ≤ d → d < j →
        basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) ∈ V := by
  let E := LinearMap.ker (basisGradeProjection (b.baseChange ℝ) w (j - 1) - LinearMap.id)
  have hE : ∀ x ∈ E, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x :=
    fun _ hx => sub_eq_zero.mp hx
  have hgrades := F.polynomial_bchRemove_grades b w hF E (j - 1) hE A.coord P.coord B.coord
    (fun α => sub_eq_zero.mpr (hA α)) (fun α => sub_eq_zero.mpr (hB α))
  have hcurrent (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients P.coord α) -
          coefficients A.coord α - coefficients B.coord α := by
    have h := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) hgrades.1
    simp only [coefficients_map, map_sub, Finsupp.sub_apply, LinearMap.restrictScalars_apply] at h
    exact h
  have hbelow (d : ℕ) (hd : d < j - 1) (α : σ →₀ ℕ) :
      basisGradeProjection (b.baseChange ℝ) w d (coefficients (A⁻¹ * P * B⁻¹).coord α) =
        basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) := by
    have h := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) (hgrades.2 d hd)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at h
    exact h
  constructor
  · intro α
    by_cases hj2 : j = 2
    · have h := hcurrent α
      rw [hj2] at h
      change basisGradeProjection (b.baseChange ℝ) w 1 (coefficients (A⁻¹ * P * B⁻¹).coord α) = _ at h
      rw [h]
      exact K.sub_mem (K.sub_mem (hK α) (hAK hj2 α)) (hBK hj2 α)
    · rw [hbelow 1 (by omega)]
      exact hK α
  · intro α d hd hdj
    rcases lt_or_eq_of_le (show d ≤ j - 1 by omega) with hlt | rfl
    · rw [hbelow d hlt]
      exact hlower α d hd hdj
    · rw [hcurrent]
      exact V.sub_mem (V.sub_mem (hlower α (j - 1) hd hdj) (hAV (by omega) α)) (hBV (by omega) α)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {μ σ K L : Type*} [AddCommGroup K] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))

include hF in
theorem formal_bracket_to_current_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V H : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (I : K →+ ℝ ⊗[ℚ] L) (hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x)
    {j : ℕ} (hj : 2 ≤ j)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0)
    (hAH : j = 2 → ∀ α, coefficients A.coord α ∈ H)
    (hBH : j = 2 → ∀ α, coefficients B.coord α ∈ H)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hH : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ H)
    (hlower : ∀ α d, 2 ≤ d → d < j →
      basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (S R : K →+ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k a c : σ → K)
    (ha : j = 2 → ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1))
    (hc : j = 2 → ∀ i, I (c i) = coefficients B.coord (Finsupp.single i 1))
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational (fun i => S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ x α, coefficients (dualAdjoint A⁻¹ (S x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hR : ∀ x α, coefficients (dualAdjoint B (R x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hbracket : ∀ α x, x ∈ H → ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, x⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule) :
    let P' := A⁻¹ * P * B⁻¹
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R
    let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + if j = 2 then S' (a i) else 0
    let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + if j = 2 then R' (c i) else 0
    let k' := fun i => if j = 2 then k i - a i - c i else k i
    let extra' := fun i => S' (k' i)
    (∀ α, coefficients P'.coord α ∈ U) ∧
      (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ H) ∧
      (∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V) ∧
      PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      (∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
      ∀ i α, coefficients
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
          (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) -
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small' i) -
          VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational' i)) α ∈ V := by
  intro P' S' R' small' rational' k' extra'
  let Uq : LieSubalgebra ℚ (ℝ ⊗[ℚ] L) :=
    { U.toSubmodule.restrictScalars ℚ with lie_mem' := fun hx hy => U.lie_mem hx hy }
  have hnewU : ∀ α, coefficients P'.coord α ∈ U :=
    bchRemove_coefficients_mem Uq s A.coord P.coord B.coord hAU hPU hBU
  have hlogs := F.formal_bracket_correction_preserves_log_conditions b w hF V H hj P A B
    hA hB hAH hBH hAV hBV hH hlower
  have hlifts : PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' :=
    PolynomialLiftSystemMod.remove Uq (V.restrictScalars ℚ) hUV P A B hAU S R hSR
  have hderivatives :
      PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
      (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
        coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
      ∀ i α, coefficients (extra' i - VectorPolynomial.map
        ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
        ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    by_cases hj2 : j = 2
    · subst j
      have h := F.formal_degree_two_reabsorption b w hF hs Uq V hUV hV I hI P A B hAU
        hAhom hBhom S R small rational k a c (ha rfl) (hc rfl) hSR hsystem hsmall hrational hS hR
      simp only [P', S', R', small', rational', k', extra', ite_true]
      exact h.2
    · have h := F.formal_invariant_bracket_derivative_step b w hF hs Uq V hUV hV hj P A B
        hAU hBU (hAV (by omega)) (hBV (by omega)) S k I hI small rational hsystem hsmall hrational hS
      simp only [P', S', small', rational', k', extra', ite_eq_right hj2, add_zero]
      exact h
  refine ⟨hnewU, hlogs.1, hlogs.2, hlifts, hderivatives.1, hderivatives.2.1, hderivatives.2.2, ?_⟩
  exact F.formal_current_layer_derivative_equation_mod b w hF hs U V H hUV hV hj P'
    hnewU hlogs.1 hlogs.2 hbracket small' rational' extra'
    (fun i α => (hderivatives.2.1 i α).2) hderivatives.2.2 hderivatives.1

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

def bracketTransitionBudget (p : ℝ) : ℝ :=
  4 * p + (p + 2) ^ 8 + (p + 2) ^ 9 + 1

theorem bracket_transition_budget_bounds {p : ℝ} (hp : 0 ≤ p)
    (k m d : ℕ) (hk : (k : ℝ) ≤ p) (hm : (m : ℝ) ≤ Real.exp p)
    (hd : (d : ℝ) ≤ Real.exp ((p + 2) ^ 9)) :
    Real.exp p ≤ Real.exp (bracketTransitionBudget p) ∧
      Real.exp p + (k : ℝ) * Real.exp p * Real.exp ((p + 2) ^ 8) ≤
        Real.exp (bracketTransitionBudget p) ∧
      ((m * (m * d) : ℕ) : ℝ) ≤ Real.exp (bracketTransitionBudget p) := by
  have h8 : 0 ≤ (p + 2) ^ 8 := by positivity
  have h9 : 0 ≤ (p + 2) ^ 9 := by positivity
  have hpE : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  have hterm : (k : ℝ) * Real.exp p * Real.exp ((p + 2) ^ 8) ≤
      Real.exp (2 * p + (p + 2) ^ 8) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp ((p + 2) ^ 8) := by
        gcongr
        exact hk.trans hpE
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  refine ⟨Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith), ?_, ?_⟩
  · calc
      _ ≤ Real.exp (2 * p + (p + 2) ^ 8) + Real.exp (2 * p + (p + 2) ^ 8) :=
        add_le_add (Real.exp_le_exp.mpr (by linarith)) hterm
      _ = Real.exp (2 * p + (p + 2) ^ 8) * 2 := by ring
      _ ≤ Real.exp (2 * p + (p + 2) ^ 8) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (1 : ℝ)]) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + (p + 2) ^ 8 + 1) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith)
  · calc
      _ = (m : ℝ) * ((m : ℝ) * (d : ℝ)) := by simp only [Nat.cast_mul]
      _ ≤ Real.exp p * (Real.exp p * Real.exp ((p + 2) ^ 9)) :=
        mul_le_mul hm (mul_le_mul hm hd (Nat.cast_nonneg _) (Real.exp_nonneg _))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Real.exp_nonneg _)
      _ = Real.exp (2 * p + (p + 2) ^ 9) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by unfold bracketTransitionBudget; linarith)

theorem exists_bracket_transition_uniform_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → bracketTransitionBudget p ≤ (p + C) ^ C := by
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget
    (4 * Polynomial.X + (Polynomial.X + 2) ^ 8 + (Polynomial.X + 2) ^ 9 + 1)
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [bracketTransitionBudget, Polynomial.eval₂_pow] using hbound p hp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L μ κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [Fintype μ] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
  (hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
  {K : Submodule ℚ L}

include hF in
theorem exists_controlled_bracket_to_current_layer (hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V : Submodule ℝ (ℝ ⊗[ℚ] L))
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (hV : BasisGradedSubmodule (b.baseChange ℝ) w V)
    (e : Basis κ ℚ K)
    (hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {j H m : ℕ} (hj : 2 ≤ j) (hH : 1 ≤ H) (hm : 0 < m)
    (he : ∀ i z, RationalHeightLE (b.repr (e z : L) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hambient : (Fintype.card μ : ℝ) ≤ p)
    (hkernel : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hmp : (m : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (P A B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot)
    (hPU : ∀ α, coefficients P.coord α ∈ U)
    (hAU : ∀ α, coefficients A.coord α ∈ U) (hBU : ∀ α, coefficients B.coord α ∈ U)
    (hA : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients A.coord α) = coefficients A.coord α)
    (hB : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1) (coefficients B.coord α) = coefficients B.coord α)
    (hAhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients A.coord α = 0)
    (hBhom : ∀ α, Finsupp.weight (fun _ : σ => (1 : ℕ)) α ≠ j - 1 → coefficients B.coord α = 0)
    (hAK : j = 2 → ∀ α, coefficients A.coord α ∈ K.baseChange ℝ)
    (hBK : j = 2 → ∀ α, coefficients B.coord α ∈ K.baseChange ℝ)
    (hAV : 2 < j → ∀ α, coefficients A.coord α ∈ V)
    (hBV : 2 < j → ∀ α, coefficients B.coord α ∈ V)
    (hPK : ∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P.coord α) ∈ K.baseChange ℝ)
    (hlower : ∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P.coord α) ∈ V)
    (S R : κ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (small rational : σ → VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (k : σ → κ → ℝ)
    (hSR : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S R)
    (hsystem : PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P small rational
      (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S (k i)))
    (hsmall : ∀ i α, coefficients (small i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hrational : ∀ i α, coefficients (rational i) α ∈ V ⊔ (F.realLayer j).toSubmodule)
    (hS : ∀ z α, coefficients (dualAdjoint A⁻¹ (S z) - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hR : ∀ z α, coefficients (dualAdjoint B (R z) - monomial 0 ((1 : ℝ) ⊗ₜ[ℚ] (e z : L))) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hbracket : ∀ z α, ⁅coefficients (A⁻¹ * P * B⁻¹).coord α, (1 : ℝ) ⊗ₜ[ℚ] (e z : L)⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule)
    (hAbound : CoefficientBound (b.baseChange ℝ) T (Real.exp p) A.coord)
    (hBgrid : CoefficientGrid (b.baseChange ℝ) m B.coord)
    (hSbound : ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp p) (dualAdjoint A⁻¹ (S z)))
    (hRgrid : ∀ z, CoefficientGrid (b.baseChange ℝ) m (dualAdjoint B (R z)))
    (hsmallBound : ∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp p / T i)
      (dualAdjoint A⁻¹ (small i - formalLogDerivative i A)))
    (hrationalGrid : ∀ i, CoefficientGrid (b.baseChange ℝ) m
      (dualAdjoint B (rational i) - formalLogDerivative i B))
    (hSshift : ∀ z, dualAdjoint A⁻¹ (S z) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hRshift : ∀ z, dualAdjoint B (R z) ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hsmallShift : ∀ i, dualAdjoint A⁻¹ (small i - formalLogDerivative i A) ∈
      shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1)
    (hrationalShift : ∀ i, dualAdjoint B (rational i) - formalLogDerivative i B ∈
      shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) :
    let S₀ := basisPolynomialLift (Pi.basisFun ℝ κ) S
    let R₀ := basisPolynomialLift (Pi.basisFun ℝ κ) R
    let S' := (dualAdjointAddEquiv A⁻¹).toAddMonoidHom.comp S₀.toAddMonoidHom
    let R' := (dualAdjointAddEquiv B).toAddMonoidHom.comp R₀.toAddMonoidHom
    ∃ (a c : σ → κ → ℝ) (n : ℕ),
      0 < n ∧ (n : ℝ) ≤ Real.exp (bracketTransitionBudget p) ∧
      let P' := A⁻¹ * P * B⁻¹
      let small' := fun i => dualAdjoint A⁻¹ (small i - formalLogDerivative i A) + if j = 2 then S' (a i) else 0
      let rational' := fun i => dualAdjoint B (rational i) - formalLogDerivative i B + if j = 2 then R' (c i) else 0
      let k' := fun i => if j = 2 then k i - a i - c i else k i
      let extra' := fun i => S' (k' i)
      (∀ α, coefficients P'.coord α ∈ U) ∧
        (∀ α, basisGradeProjection (b.baseChange ℝ) w 1 (coefficients P'.coord α) ∈ K.baseChange ℝ) ∧
        (∀ α d, 2 ≤ d → d < j → basisGradeProjection (b.baseChange ℝ) w d (coefficients P'.coord α) ∈ V) ∧
        PolynomialLiftSystemMod (V.restrictScalars ℚ) P' S' R' ∧
        PolynomialDerivativeSystemMod (V.restrictScalars ℚ) P' small' rational' extra' ∧
        (∀ i α, coefficients (small' i) α ∈ V ⊔ (F.realLayer j).toSubmodule ∧
          coefficients (rational' i) α ∈ V ⊔ (F.realLayer j).toSubmodule) ∧
        (∀ i α, coefficients (extra' i - VectorPolynomial.map
          ((basisGradeProjection (b.baseChange ℝ) w 1).restrictScalars ℚ)
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L) P'.coord)) α ∈
            V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i α, coefficients
          ((MvPolynomial.pderiv i).toLinearMap.rTensor (ℝ ⊗[ℚ] L)
            (VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) P'.coord) -
            VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (small' i) -
            VectorPolynomial.map ((basisGradeProjection (b.baseChange ℝ) w j).restrictScalars ℚ) (rational' i)) α ∈ V) ∧
        (∀ α x, x ∈ K.baseChange ℝ → ⁅coefficients P'.coord α, x⁆ ∈
          V ⊔ (F.realLayer (j + 1)).toSubmodule) ∧
        (∀ i, CoefficientBound (b.baseChange ℝ) T (Real.exp (bracketTransitionBudget p) / T i) (small' i) ∧
          CoefficientGrid (b.baseChange ℝ) n (rational' i) ∧
          small' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1 ∧
          rational' i ∈ shiftedGradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) 1) ∧
        ∀ z, CoefficientBound (b.baseChange ℝ) T (Real.exp (bracketTransitionBudget p)) (dualAdjoint A⁻¹ (S z)) ∧
          CoefficientGrid (b.baseChange ℝ) n (dualAdjoint B (R z)) := by
  classical
  intro S₀ R₀ S' R'
  let I := bracketSystemLift e
  have hchoice : ∃ (a c : σ → κ → ℝ) (d : ℕ), 0 < d ∧
      (d : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      (j = 2 → ∀ i, I (a i) = coefficients A.coord (Finsupp.single i 1) ∧
        I (c i) = coefficients B.coord (Finsupp.single i 1)) ∧
      ∀ i, ‖a i‖ ≤ Real.exp ((p + 2) ^ 8) / T i ∧ c i ∈ realDenominatorGrid d := by
    by_cases hj2 : j = 2
    · obtain ⟨a, c, d, hd, hdp, hdirs⟩ := exists_uniform_polynomial_kernel_directions b e hH hm he hp
        (Real.exp_nonneg p) hambient hkernel hHp hmp le_rfl A.coord B.coord (hAK hj2) (hBK hj2)
        T hT hAbound hBgrid
      exact ⟨a, c, d, hd, hdp, fun _ i => ⟨(hdirs i).1, (hdirs i).2.1⟩,
        fun i => ⟨(hdirs i).2.2.1, (hdirs i).2.2.2⟩⟩
    · refine ⟨0, 0, 1, by decide, ?_, fun h => (hj2 h).elim, fun i => ?_⟩
      · simpa only [Nat.cast_one] using Real.one_le_exp (by positivity : 0 ≤ (p + 2) ^ 9)
      · constructor
        · simp only [Pi.zero_apply, norm_zero]
          exact div_nonneg (Real.exp_nonneg _) (hT i).le
        · exact ⟨0, by ext z; simp⟩
  obtain ⟨a, c, d, hd, hdp, hdirs, hcoordinates⟩ := hchoice
  let n := m * (m * d)
  have hn : 0 < n := Nat.mul_pos hm (Nat.mul_pos hm hd)
  have hmdiv : m ∣ n := dvd_mul_right m (m * d)
  obtain ⟨hbase, habsorb, hnbound⟩ := bracket_transition_budget_bounds hp (Fintype.card κ) m d hkernel hmp hdp
  refine ⟨a, c, n, hn, hnbound, ?_⟩
  intro P' small' rational' k' extra'
  have hI : ∀ x, basisGradeProjection (b.baseChange ℝ) w 1 (I x) = I x :=
    fun x => hK _ (bracketSystemLift_mem e x)
  have hSR₀ : PolynomialLiftSystemMod (V.restrictScalars ℚ) P S₀ R₀ :=
    hSR.extend_basis (Pi.basisFun ℝ κ) V P S R
  have hSall : ∀ x α, coefficients (dualAdjoint A⁻¹ (S₀ x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    apply basisPolynomialLift_adjoint_residual (Pi.basisFun ℝ κ) A⁻¹ S I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule)
    intro z α
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hS z α
  have hRall : ∀ x α, coefficients (dualAdjoint B (R₀ x) - monomial 0 (I x)) α ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    apply basisPolynomialLift_adjoint_residual (Pi.basisFun ℝ κ) B R I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule)
    intro z α
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hR z α
  have hbracketall : ∀ α x, x ∈ K.baseChange ℝ → ⁅coefficients P'.coord α, x⁆ ∈
      V ⊔ (F.realLayer (j + 1)).toSubmodule := by
    intro α x hx
    obtain ⟨v, rfl⟩ := exists_subspace_basis_coordinates e x hx
    apply real_bracket_mem_of_basis (Pi.basisFun ℝ κ) I
      (V ⊔ (F.realLayer (j + 1)).toSubmodule) (coefficients P'.coord α) _ v
    intro z
    simpa only [I, Pi.basisFun_apply, bracketSystemLift_single] using hbracket z α
  have hgeometry := F.formal_bracket_to_current_layer b w hF hs U V (K.baseChange ℝ) hUV hV
    I.toAddMonoidHom hI hj P A B hPU hAU hBU hA hB hAhom hBhom hAK hBK hAV hBV hPK hlower
    S₀.toAddMonoidHom R₀.toAddMonoidHom small rational k a c
    (fun h i => (hdirs h i).1) (fun h i => (hdirs h i).2)
    hSR₀ hsystem hsmall hrational hSall hRall hbracketall
  refine ⟨hgeometry.1, hgeometry.2.1, hgeometry.2.2.1, hgeometry.2.2.2.1,
    hgeometry.2.2.2.2.1, hgeometry.2.2.2.2.2.1, hgeometry.2.2.2.2.2.2.1,
    hgeometry.2.2.2.2.2.2.2, hbracketall, ?_, ?_⟩
  · intro i
    by_cases hj2 : j = 2
    · have ha : ‖(Pi.basisFun ℝ κ).equivFun (a i)‖ ≤ Real.exp ((p + 2) ^ 8) / T i := by
        rw [Pi.basisFun_equivFun]
        exact (hcoordinates i).1
      have hc : (Pi.basisFun ℝ κ).equivFun (c i) ∈ realDenominatorGrid d := by
        rw [Pi.basisFun_equivFun]
        exact (hcoordinates i).2
      have hbound := basisPolynomialLift_reabsorption_bound (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint A⁻¹ (S z)) (b.baseChange ℝ) T hT (Real.exp p) (Real.exp p)
        (Real.exp ((p + 2) ^ 8)) (T i) (Real.exp_nonneg p) hSbound _ (hsmallBound i) (a i) ha
      have hgrid := basisPolynomialLift_reabsorption_grid (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint B (R z)) (b.baseChange ℝ) d m m hRgrid _ (hrationalGrid i) (c i) hc
      have hSsh := basisPolynomialLift_shiftedGraded (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint A⁻¹ (S z)) (b.baseChange ℝ) w (fun _ : σ => 1) 1 hSshift (a i)
      have hRsh := basisPolynomialLift_shiftedGraded (Pi.basisFun ℝ κ)
        (fun z => dualAdjoint B (R z)) (b.baseChange ℝ) w (fun _ : σ => 1) 1 hRshift (c i)
      rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
        (Pi.basisFun ℝ κ) A⁻¹ S] at hbound hSsh
      rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
        (Pi.basisFun ℝ κ) B R] at hgrid hRsh
      simp only [small', rational', ite_eq_left hj2]
      exact ⟨hbound.mono _ T hT (div_le_div_of_nonneg_right habsorb (hT i).le), hgrid,
        (shiftedGradedPolynomialSubmodule _ _ _ _).add_mem (hsmallShift i) hSsh,
        (shiftedGradedPolynomialSubmodule _ _ _ _).add_mem (hrationalShift i) hRsh⟩
    · simp only [small', rational', ite_eq_right hj2, add_zero]
      exact ⟨(hsmallBound i).mono _ T hT (div_le_div_of_nonneg_right hbase (hT i).le),
        fun α => realDenominatorGrid_subset_of_dvd hm hmdiv (hrationalGrid i α),
        hsmallShift i, hrationalShift i⟩
  · intro z
    exact ⟨(hSbound z).mono _ T hT hbase,
      fun α => realDenominatorGrid_subset_of_dvd hm hmdiv (hRgrid z α)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
