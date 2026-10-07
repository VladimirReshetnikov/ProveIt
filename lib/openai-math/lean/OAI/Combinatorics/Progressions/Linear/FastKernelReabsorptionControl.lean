import OAI.Combinatorics.Progressions.Estimates.ExtractedInitialState

namespace OAI

section

namespace Erdos3

theorem norm_add_lift_coordinate_bound {E K V H : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup K] [Module ℝ K]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [SeminormedAddCommGroup H] [NormedSpace ℝ H]
    (N : E →ₗ[ℝ] V) (NK : K →ₗ[ℝ] H) (S : K →ₗ[ℝ] E)
    (small : E) (a : K) (M C A T : ℝ) (hC : 0 ≤ C) (hT : 0 < T)
    (hsmall : ‖N small‖ ≤ M / T) (ha : ‖NK a‖ ≤ A / T)
    (hS : ∀ x, ‖N (S x)‖ ≤ C * ‖NK x‖) :
    ‖N (small + S a)‖ ≤ (M + C * A) / T := by
  rw [map_add]
  calc
    _ ≤ ‖N small‖ + ‖N (S a)‖ := norm_add_le _ _
    _ ≤ M / T + C * (A / T) :=
      add_le_add hsmall ((hS a).trans (mul_le_mul_of_nonneg_left ha hC))
    _ = _ := by field_simp [hT.ne']

theorem rational_lift_reabsorption_grid {ι κ K : Type*} [Fintype κ]
    [AddCommGroup K] [Module ℝ K]
    (R : K →ₗ[ℝ] (ι → ℝ)) (v : κ → K) (c : κ → ℝ) (r : ι → ℝ) (l m n : ℕ)
    (hc : c ∈ realDenominatorGrid l) (hR : ∀ k, R (v k) ∈ realDenominatorGrid m)
    (hr : r ∈ realDenominatorGrid n) :
    r + R (∑ k, c k • v k) ∈ realDenominatorGrid (n * (m * l)) := by
  have hgrid := linear_lift_grid_of_coefficients R v c l m hc hR
  have h := realDenominatorGrid_sub_product n (m * l) r (-R (∑ k, c k • v k)) hr
    (realDenominatorGrid_neg (m * l) hgrid)
  simpa only [sub_neg_eq_add] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι ν τ K L V H : Type*} [Fintype σ] [DecidableEq σ] [Fintype ν]
  [AddCommGroup K] [Module ℝ K] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V]
  [SeminormedAddCommGroup H] [NormedSpace ℝ H] {s : ℕ}
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

theorem realFast_kernel_reabsorption_controlled
    (a b c : 𝓖) (S R : K →ₗ[ℝ] 𝓔)
    (hSR : S = (ρ (a * b * c)).toLinearMap.comp R)
    (I : K →ₗ[ℝ] (ℝ ⊗[ℚ] (L ⧸ F.layer 2))) (hS : (P).comp S = I) (hR : (P).comp R = I)
    (small rational : σ → 𝓔) (k A B : σ → K)
    (hsystem : ∀ i, Y (a * b * c) i = small i + ρ (a * b * c) (rational i) + S (k i))
    (N : 𝓔 →ₗ[ℝ] V) (NK : K →ₗ[ℝ] H) (coord : 𝓔 →ₗ[ℝ] (τ → ℝ))
    (C M D J A₀ : ℝ) (hC : 0 ≤ C) (hJ : 0 ≤ J) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (haction : ∀ x, ‖N ((ρ a).symm x)‖ ≤ C * ‖N x‖)
    (hsmall : ∀ i, ‖N (small i)‖ ≤ M / T i) (hYa : ∀ i, ‖N (Y a i)‖ ≤ D / T i)
    (hSbound : ∀ x, ‖N (S x)‖ ≤ J * ‖NK x‖) (hA : ∀ i, ‖NK (A i)‖ ≤ A₀ / T i)
    (v : ν → K) (l q rden : ℕ) (hRgrid : ∀ j, coord (R (v j)) ∈ realDenominatorGrid l)
    (hrational : ∀ i, coord (rational i) ∈ realDenominatorGrid l)
    (hc : ∀ x, coord x ∈ realDenominatorGrid l → coord (ρ c x) ∈ realDenominatorGrid q)
    (hYc : ∀ i, coord (Y c i) ∈ realDenominatorGrid q)
    (β : σ → ν → ℝ) (hB : ∀ i, B i = ∑ j, β i j • v j)
    (hβ : ∀ i, β i ∈ realDenominatorGrid rden) :
    let S' := (ρ a).symm.toLinearMap.comp S
    let R' := (ρ c).toLinearMap.comp R
    let small' := fun i => (ρ a).symm (small i - Y a i) + S' (A i)
    let rational' := fun i => ρ c (rational i) - Y c i + R' (B i)
    S' = (ρ b).toLinearMap.comp R' ∧ (P).comp S' = I ∧ (P).comp R' = I ∧
      (∀ x, ‖N (S' x)‖ ≤ (C * J) * ‖NK x‖) ∧
      (∀ j, coord (R' (v j)) ∈ realDenominatorGrid q) ∧
      ∀ i, Y b i = small' i + ρ b (rational' i) + S' (k i - A i - B i) ∧
        ‖N (small' i)‖ ≤ (C * (M + D) + (C * J) * A₀) / T i ∧
        coord (rational' i) ∈ realDenominatorGrid (q * (q * rden)) := by
  intro S' R' small' rational'
  have hdata := F.realFast_derivative_removal_controlled U e ω hF a b c S R hSR I hS hR
    small rational k hsystem N coord C M D hC T hT haction hsmall hYa
    (fun x => J * ‖NK x‖) hSbound v l q hRgrid hrational hc hYc
  obtain ⟨hfactor, hhorS, hhorR, hS', hR', hderiv⟩ := hdata
  have hSbound' (x : K) : ‖N (S' x)‖ ≤ (C * J) * ‖NK x‖ := by
    simpa only [mul_assoc] using hS' x
  refine ⟨hfactor, hhorS, hhorR, hSbound', hR', fun i => ?_⟩
  obtain ⟨hraw, hrawNorm, hrawGrid⟩ := hderiv i
  refine ⟨?_, ?_, ?_⟩
  · have h := linear_derivative_absorb (ρ b).toLinearMap S' R' hfactor (Y b i)
      ((ρ a).symm (small i - Y a i)) (ρ c (rational i) - Y c i) (k i) (-A i) (-B i) hraw
    simp only [map_neg, sub_neg_eq_add, ← sub_eq_add_neg] at h
    exact h
  · exact norm_add_lift_coordinate_bound N NK S' _ (A i) (C * (M + D)) (C * J) A₀
      (T i) (mul_nonneg hC hJ) (hT i) hrawNorm (hA i) hSbound'
  · change coord (ρ c (rational i) - Y c i + R' (B i)) ∈ _
    rw [map_add, hB i]
    exact rational_lift_reabsorption_grid (coord.comp R') v (β i) _ rden q q (hβ i) hR' hrawGrid

end Erdos3.NilpotentLieFiltration

end

end OAI
