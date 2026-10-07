import OAI.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder

namespace OAI

section

namespace Erdos3

open Module MvPolynomial

variable {ι L : Type*} [Fintype ι]
  [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
  (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
  (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
  (hc : ∀ i j k, RationalHeightLE (c i j k) H)

include hstructure hc

theorem lieBCH_pair_coordinates_bound (x₁ y₁ x₂ y₂ : L) {B δ : ℝ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx₁ : ∀ i, |e.repr x₁ i| ≤ B) (hy₁ : ∀ i, |e.repr y₁ i| ≤ B)
    (hx₂ : ∀ i, |e.repr x₂ i| ≤ B) (hy₂ : ∀ i, |e.repr y₂ i| ≤ B)
    (hxx : ∀ i, |e.repr x₁ i - e.repr x₂ i| ≤ δ)
    (hyy : ∀ i, |e.repr y₁ i - e.repr y₂ i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x₁ y₁) k - e.repr (lieBCH s x₂ y₂) k| ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun z => e.repr (![x₁, y₁] z.1) z.2
  let w : Fin 2 × ι → ℝ := fun z => e.repr (![x₂, y₂] z.1) z.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (z : Fin 2 × ι) : |v z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx₁ i
    · exact hy₁ i
  have hw (z : Fin 2 × ι) : |w z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx₂ i
    · exact hy₂ i
  have hvw (z : Fin 2 × ι) : |v z - w z| ≤ δ := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hxx i
    · exact hyy i
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hevalv : aeval v P = e.repr (lieBCH s x₁ y₁) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x₁ y₁ k
  have hevalw : aeval w P = e.repr (lieBCH s x₂ y₂) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x₂ y₂ k
  rw [hevalv, hevalw] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

theorem lieBCH_pair_coordinate_dist_le (x₁ y₁ x₂ y₂ : L) {B δ : ℝ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx₁ : ‖e.equivFun x₁‖ ≤ B) (hy₁ : ‖e.equivFun y₁‖ ≤ B)
    (hx₂ : ‖e.equivFun x₂‖ ≤ B) (hy₂ : ‖e.equivFun y₂‖ ≤ B)
    (hxx : dist (e.equivFun x₁) (e.equivFun x₂) ≤ δ)
    (hyy : dist (e.equivFun y₁) (e.equivFun y₂) ≤ δ) :
    dist (e.equivFun (lieBCH s x₁ y₁)) (e.equivFun (lieBCH s x₂ y₂)) ≤
      bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  apply (dist_pi_le_iff (mul_nonneg (bchBoxCoordinateBound_nonneg s _ H (by linarith)) hδ)).mpr
  intro i
  have hcoord (x : L) (hx : ‖e.equivFun x‖ ≤ B) (j : ι) : |e.repr x j| ≤ B := by
    calc
      _ ≤ ‖e.equivFun x‖ := by
        simpa only [Real.norm_eq_abs, Basis.equivFun_apply] using norm_le_pi_norm (e.equivFun x) j
      _ ≤ B := hx
  have hdiff (x y : L) (hxy : dist (e.equivFun x) (e.equivFun y) ≤ δ) (j : ι) :
      |e.repr x j - e.repr y j| ≤ δ := by
    calc
      _ ≤ dist (e.equivFun x) (e.equivFun y) := by
        simpa only [Real.dist_eq, Basis.equivFun_apply] using dist_le_pi_dist (e.equivFun x) (e.equivFun y) j
      _ ≤ δ := hxy
  exact lieBCH_pair_coordinates_bound e c hstructure hc x₁ y₁ x₂ y₂ hB hδ
    (hcoord _ hx₁) (hcoord _ hy₁) (hcoord _ hx₂) (hcoord _ hy₂) (hdiff _ _ hxx) (hdiff _ _ hyy) i

theorem lieBCH_coordinate_norm_le
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (x y : L) {B : ℝ} (hB : 1 ≤ B)
    (hx : ‖e.equivFun x‖ ≤ B) (hy : ‖e.equivFun y‖ ≤ B) :
    ‖e.equivFun (lieBCH s x y)‖ ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * B := by
  have hB₀ : 0 ≤ B := by linarith
  simpa only [lieBCH_zero_left hnil, map_zero, norm_zero, dist_zero_right] using
    lieBCH_pair_coordinate_dist_le (s := s) e c hstructure hc x y 0 0 hB hB₀
      hx hy (by simpa using hB₀) (by simpa using hB₀)
      (by simpa using hx) (by simpa using hy)

end Erdos3

end

end OAI
