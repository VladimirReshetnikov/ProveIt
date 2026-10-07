import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover

namespace OAI

section

namespace Erdos3.VectorPolynomial.NormalizedPolynomialTwist

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {K X : Type*} [Fintype K] [Fintype X]
variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable {periodCap coverCap : ℝ} {L : ℝ≥0}

theorem integerPhysicalSite_local_parameter_dist
    (N : X → ℕ) (P : K → ℕ) (hP : ∀ k, 0 < P k)
    (frame : Option K × X → ℤ) (u v : K → ℤ)
    (C : K → ℝ) (hC : ∀ k, 0 ≤ C k) {η : ℝ} (hη : 0 ≤ η)
    (hslope : ∀ k x, |(frame (some k, x) : ℝ) / N x| * P k ≤ C k)
    (hcell : ∀ k, |(u k : ℝ) / P k - (v k : ℝ) / P k| ≤ η) :
    dist (fun x => (integerPhysicalSite u frame x : ℝ) / N x)
      (fun x => (integerPhysicalSite v frame x : ℝ) / N x) ≤ η * ∑ k, C k := by
  apply (dist_pi_le_iff (mul_nonneg hη (Finset.sum_nonneg (fun k _ => hC k)))).mpr
  intro x
  rw [Real.dist_eq]
  have heq : (integerPhysicalSite u frame x : ℝ) / N x -
      (integerPhysicalSite v frame x : ℝ) / N x =
      ∑ k, ((u k : ℝ) / P k - (v k : ℝ) / P k) *
        ((frame (some k, x) : ℝ) / N x) * P k := by
    simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, add_div,
      Finset.sum_div]
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hk : (P k : ℝ) ≠ 0 := by exact_mod_cast (hP k).ne'
    field_simp
  rw [heq]
  calc
    _ ≤ ∑ k, |((u k : ℝ) / P k - (v k : ℝ) / P k) *
        ((frame (some k, x) : ℝ) / N x) * P k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, η * C k := by
      apply Finset.sum_le_sum
      intro k _
      simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (P k) : (0 : ℝ) ≤ _), mul_assoc]
      exact mul_le_mul (hcell k) (hslope k x) (by positivity) hη
    _ = _ := (Finset.mul_sum _ _ _).symm

omit [Fintype X] in

theorem integerPhysicalSite_residue_of_parameter_residue
    (q : ℕ) (frame : Option K × X → ℤ) (u v : K → ℤ)
    (hcell : ∀ k, (u k : ZMod q) = (v k : ZMod q)) :
    (fun x => (integerPhysicalSite u frame x : ZMod q)) =
      (fun x => (integerPhysicalSite v frame x : ZMod q)) := by
  funext x
  simp only [integerPhysicalSite, Int.cast_add, Int.cast_sum, Int.cast_mul, hcell]

theorem eval_local_parameter_freezing [IsEmpty (Σ j, J j)]
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L)
    (N : X → ℕ) (P : K → ℕ) (hP : ∀ k, 0 < P k)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (frame : Option K × X → ℤ) (u v : K → ℤ)
    (C : K → ℝ) (hC : ∀ k, 0 ≤ C k) {η : ℝ} (hη : 0 ≤ η)
    (hslope : ∀ k x, |(frame (some k, x) : ℝ) / N x| * P k ≤ C k)
    (hcell : ∀ k, |(u k : ℝ) / P k - (v k : ℝ) / P k| ≤ η)
    (hres : ∀ k, (u k : ZMod W.modulus) = (v k : ZMod W.modulus)) :
    ‖W.eval N poly (integerPhysicalSite u frame) -
      W.eval N poly (integerPhysicalSite v frame)‖ ≤ (L : ℝ) * η * ∑ k, C k := by
  have hu : physicalGridFactorInput W.cover poly
      (fun x => (integerPhysicalSite u frame x : ℝ)) = 0 := Subsingleton.elim _ _
  have hv : physicalGridFactorInput W.cover poly
      (fun x => (integerPhysicalSite v frame x : ℝ)) = 0 := Subsingleton.elim _ _
  have hres' := integerPhysicalSite_residue_of_parameter_residue W.modulus frame u v hres
  have he := W.frozenTorus_spatial_error
    (fun x => (integerPhysicalSite v frame x : ZMod W.modulus))
    (fun x => (integerPhysicalSite u frame x : ℝ) / N x)
    (fun x => (integerPhysicalSite v frame x : ℝ) / N x) 0
  simp only [eval, hu, hv, hres']
  refine he.trans ?_
  exact (mul_le_mul_of_nonneg_left
    (integerPhysicalSite_local_parameter_dist N P hP frame u v C hC hη hslope hcell)
    L.coe_nonneg).trans_eq (by ring)

theorem correlation_after_freezing {T : Type*} [Fintype T]
    (μ : FiniteProbabilityWeights T) (twist signal : T → ℂ) (c : ℂ)
    (hc : ‖c‖ ≤ 1) (hsignal : ∀ t, ‖signal t‖ ≤ 1)
    {ε δ : ℝ} (hfreeze : ∀ t, μ.weight t ≠ 0 → ‖twist t - c‖ ≤ ε)
    (hbias : δ ≤ ‖μ.complexMean (fun t => star (twist t) * signal t)‖) :
    δ - ε ≤ ‖μ.complexMean signal‖ := by
  have he := μ.norm_complexMean_sub_le
    (fun t => star (twist t) * signal t) (fun t => star c * signal t)
    (fun _ => ε) (fun t ht => by
      rw [← sub_mul, ← star_sub, norm_mul, norm_star]
      exact (mul_le_mul (hfreeze t ht) (hsignal t) (norm_nonneg _) (by
        exact (norm_nonneg _).trans (hfreeze t ht))).trans_eq (mul_one _))
  rw [μ.mean_const] at he
  have hconst : μ.complexMean (fun t => star c * signal t) = star c * μ.complexMean signal := by
    simp only [FiniteProbabilityWeights.complexMean, Finset.mul_sum]
    congr 1
    funext t
    ring
  have hb : ‖μ.complexMean (fun t => star c * signal t)‖ ≤ ‖μ.complexMean signal‖ := by
    rw [hconst, norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_eq (one_mul _)
  have ht := norm_le_norm_sub_add
    (μ.complexMean (fun t => star (twist t) * signal t))
    (μ.complexMean (fun t => star c * signal t))
  linarith

end Erdos3.VectorPolynomial.NormalizedPolynomialTwist

end

end OAI
