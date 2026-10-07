/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.MvPolynomial.Funext
import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTermCount

namespace OAI


namespace Erdos3

open MvPolynomial
open scoped BigOperators

noncomputable def scaleMvPolynomialAxes {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    MvPolynomial σ ℝ :=
  ∑ α ∈ P.support, monomial α (P.coeff α * monomialScale T α)

theorem scaleMvPolynomialAxes_coeff {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ)
    (α : σ →₀ ℕ) :
    (scaleMvPolynomialAxes T P).coeff α = P.coeff α * monomialScale T α := by
  classical
  rw [scaleMvPolynomialAxes, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · simp only [notMem_support_iff.mp h, zero_mul]

theorem scaleMvPolynomialAxes_support_subset {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    (scaleMvPolynomialAxes T P).support ⊆ P.support := by
  intro α hα
  rw [mem_support_iff, scaleMvPolynomialAxes_coeff] at hα
  exact mem_support_iff.mpr (left_ne_zero_of_mul hα)

theorem scaleMvPolynomialAxes_totalDegree_le {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ) :
    (scaleMvPolynomialAxes T P).totalDegree ≤ P.totalDegree :=
  totalDegree_le_of_support_subset (scaleMvPolynomialAxes_support_subset T P)

theorem scaleMvPolynomialAxes_eval {σ : Type*} (T : σ → ℝ) (P : MvPolynomial σ ℝ)
    (x : σ → ℝ) :
    eval x (scaleMvPolynomialAxes T P) = eval (fun i => T i * x i) P := by
  classical
  rw [scaleMvPolynomialAxes, eval_sum, eval_eq]
  apply Finset.sum_congr rfl
  intro α _
  rw [eval_monomial]
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring

theorem scaleMvPolynomialAxes_mass_le {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (P : MvPolynomial σ ℝ) {M : ℝ}
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤ P.support.card * M := by
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (scaleMvPolynomialAxes_support_subset T P)]
  calc
    _ ≤ ∑ _α ∈ P.support, M := by
      apply Finset.sum_le_sum
      intro α _
      rw [scaleMvPolynomialAxes_coeff, abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      exact (le_div_iff₀ (monomialScale_pos T hT α)).mp (hcoeff α)
    _ = P.support.card * M := by simp

end Erdos3


namespace Erdos3

open scoped BigOperators

theorem abs_monomialScale_le_pow {σ : Type*} (T : σ → ℝ) {K : ℝ}
    (hT : ∀ i, |T i| ≤ K) (α : σ →₀ ℕ) :
    |monomialScale T α| ≤ K ^ (α.sum fun _ n => n) := by
  classical
  calc
    _ = ∏ i ∈ α.support, |T i| ^ α i := by
      simp only [monomialScale, Finsupp.prod, Finset.abs_prod, abs_pow]
    _ ≤ ∏ i ∈ α.support, K ^ α i :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hT i) _)
    _ = K ^ (α.sum fun _ n => n) := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

theorem scaleMvPolynomialAxes_mass_le_of_abs_le {σ : Type*}
    (T : σ → ℝ) (P : MvPolynomial σ ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hT : ∀ i, |T i| ≤ K) {d : ℕ} (hP : P.totalDegree ≤ d) :
    realPolynomialMass (scaleMvPolynomialAxes T P) ≤ K ^ d * realPolynomialMass P := by
  classical
  rw [realPolynomialMass_eq_sum_of_support_subset _ P.support
    (scaleMvPolynomialAxes_support_subset T P)]
  calc
    _ ≤ ∑ α ∈ P.support, |P.coeff α| * K ^ d := by
      apply Finset.sum_le_sum
      intro α hα
      rw [scaleMvPolynomialAxes_coeff, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (abs_monomialScale_le_pow T hT α).trans
        (pow_le_pow_right₀ hK ((MvPolynomial.le_totalDegree hα).trans hP))
    _ = K ^ d * realPolynomialMass P := by
      rw [← Finset.sum_mul]
      exact mul_comm _ _

theorem jointPolynomialDilation_mass_le {U B : Type*}
    (c : U → ℝ) (S : MvPolynomial (U ⊕ B) ℝ) {K : ℝ} (hK : 1 ≤ K)
    (hc : ∀ i, |c i| ≤ K) {d : ℕ} (hS : S.totalDegree ≤ d) :
    realPolynomialMass (scaleMvPolynomialAxes (Sum.elim c (fun _ => 1)) S) ≤
      K ^ d * realPolynomialMass S := by
  apply scaleMvPolynomialAxes_mass_le_of_abs_le _ S hK _ hS
  intro i
  cases i with
  | inl i => exact hc i
  | inr i => simpa only [Sum.elim_inr, abs_one] using hK

end Erdos3


namespace Erdos3
open MvPolynomial
open scoped BigOperators

private theorem abs_prod_sub_prod_unit_sum {ι : Type*} (S : Finset ι)
    (f g e : ι → ℝ) (he : ∀ i ∈ S, 0 ≤ e i)
    (hf : ∀ i ∈ S, |f i| ≤ 1) (hg : ∀ i ∈ S, |g i| ≤ 1)
    (hfg : ∀ i ∈ S, |f i - g i| ≤ e i) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ ∑ i ∈ S, e i := by
  classical
  revert he hf hg hfg
  induction S using Finset.induction_on with
  | empty => intro _ _ _ _; simp
  | @insert a S ha ih =>
    intro he hf hg hfg
    have hrec := ih (fun i hi => he i (Finset.mem_insert_of_mem hi))
      (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      (fun i hi => hg i (Finset.mem_insert_of_mem hi))
      (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
    have hprod : |∏ i ∈ S, g i| ≤ 1 := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    calc
      _ = |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) + (f a - g a) * ∏ i ∈ S, g i| := by
        congr 1
        ring
      _ ≤ |f a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| +
          |f a - g a| * |∏ i ∈ S, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ 1 * (∑ i ∈ S, e i) + e a * 1 :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (abs_nonneg _) zero_le_one)
          (mul_le_mul (hfg a (Finset.mem_insert_self _ _)) hprod
            (abs_nonneg _) (he a (Finset.mem_insert_self _ _)))
      _ = _ := by ring

theorem abs_eval_sub_eval_unit_mass_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (x y : σ → ℝ) {δ : ℝ} {m : ℕ}
    (hδ : 0 ≤ δ) (hx : ∀ i, |x i| ≤ 1) (hy : ∀ i, |y i| ≤ 1)
    (hxy : ∀ i, |x i - y i| ≤ δ) (hdegree : P.totalDegree ≤ m) :
    |eval x P - eval y P| ≤ (m : ℝ) * realPolynomialMass P * δ := by
  classical
  have hmonomial (α : σ →₀ ℕ) (hα : α ∈ P.support) :
      |(∏ i, x i ^ α i) - ∏ i, y i ^ α i| ≤ (m : ℝ) * δ := by
    have he (i : σ) : |x i ^ α i - y i ^ α i| ≤ δ * α i := by
      simpa only [one_pow, mul_one] using abs_pow_sub_pow_box_bound
        (B := (1 : ℝ)) le_rfl hδ (hx i) (hy i) (hxy i) (le_refl (α i))
    have hp := abs_prod_sub_prod_unit_sum Finset.univ
      (fun i => x i ^ α i) (fun i => y i ^ α i) (fun i => δ * α i)
      (fun _ _ => by positivity)
      (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hx i))
      (fun i _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (hy i))
      (fun i _ => he i)
    have hsum : (∑ i, (α i : ℝ)) ≤ (m : ℝ) := by
      exact_mod_cast (show (∑ i, α i) ≤ m by
        have hs : α.sum (fun (_ : σ) (n : ℕ) => n) = ∑ i, α i :=
          Finsupp.sum_fintype α (fun _ n => n) (fun _ => rfl)
        rw [← hs]
        exact (MvPolynomial.le_totalDegree hα).trans hdegree)
    apply hp.trans
    rw [← Finset.mul_sum]
    nlinarith [mul_le_mul_of_nonneg_left hsum hδ]
  change |P.eval₂ (RingHom.id ℝ) x - P.eval₂ (RingHom.id ℝ) y| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ α ∈ P.support, |P.coeff α| * ((m : ℝ) * δ) := by
      apply Finset.sum_le_sum
      intro α hα
      change |P.coeff α * ∏ i, x i ^ α i - P.coeff α * ∏ i, y i ^ α i| ≤ _
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hmonomial α hα) (abs_nonneg _)
    _ = _ := by rw [← Finset.sum_mul]; unfold realPolynomialMass; ring

theorem abs_eval_sub_eval_normalized_mass_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x y : σ → ℝ) {M δ : ℝ} {m : ℕ}
    (hmass : realPolynomialMass (scaleMvPolynomialAxes T P) ≤ M)
    (hδ : 0 ≤ δ) (hx : ∀ i, |x i| ≤ T i) (hy : ∀ i, |y i| ≤ T i)
    (hxy : ∀ i, |x i - y i| ≤ T i * δ) (hdegree : P.totalDegree ≤ m) :
    |eval x P - eval y P| ≤ (m : ℝ) * M * δ := by
  have hunit (v : σ → ℝ) (hv : ∀ i, |v i| ≤ T i) (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i)]
    exact (div_le_one (hT i)).mpr (hv i)
  have hdiff (i : σ) : |x i / T i - y i / T i| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos (hT i)]
    exact (div_le_iff₀ (hT i)).mpr (by simpa only [mul_comm] using hxy i)
  have hev (v : σ → ℝ) : eval (fun i => v i / T i) (scaleMvPolynomialAxes T P) = eval v P := by
    rw [scaleMvPolynomialAxes_eval]
    apply congrArg (fun z : σ → ℝ => eval z P)
    funext i
    exact mul_div_cancel₀ (v i) (hT i).ne'
  have h := abs_eval_sub_eval_unit_mass_bound (scaleMvPolynomialAxes T P)
    (fun i => x i / T i) (fun i => y i / T i) hδ (hunit x hx) (hunit y hy) hdiff
    ((scaleMvPolynomialAxes_totalDegree_le T P).trans hdegree)
  rw [hev, hev] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg m)) hδ)

end Erdos3


namespace Erdos3

open MvPolynomial

theorem scaleMvPolynomialAxes_eq_aeval {σ : Type*} (T : σ → ℝ)
    (P : MvPolynomial σ ℝ) :
    scaleMvPolynomialAxes T P =
      MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P := by
  apply MvPolynomial.funext
  intro x
  rw [scaleMvPolynomialAxes_eval]
  change aeval (fun i => T i * x i) P = aeval x (aeval _ P)
  rw [comp_aeval_apply]
  simp

theorem scaleMvPolynomialAxes_mem_weightedSupportLE {σ : Type*} (T : σ → ℝ)
    (w : σ → ℕ) (d : ℕ) {P : MvPolynomial σ ℝ}
    (hP : P ∈ weightedSupportLE w d) :
    scaleMvPolynomialAxes T P ∈ weightedSupportLE w d := by
  intro α hα
  exact hP (scaleMvPolynomialAxes_support_subset T P hα)

theorem rationalAxisScaling_map_real {σ : Type*} (T : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    MvPolynomial.map (algebraMap ℚ ℝ)
        (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P) =
      scaleMvPolynomialAxes (fun i => (T i : ℝ)) (MvPolynomial.map (algebraMap ℚ ℝ) P) := by
  rw [scaleMvPolynomialAxes_eq_aeval]
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP => simp only [map_mul, aeval_X, map_X, map_C, hP]; rfl

theorem rationalAxisScaling_support_subset {σ : Type*} (T : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P).support ⊆
      P.support := by
  intro α hα
  have hreal : α ∈ (MvPolynomial.map (algebraMap ℚ ℝ)
      (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P)).support := by
    rw [mem_support_iff, coeff_map]
    change ((((aeval fun i => C (T i) * X i) P).coeff α : ℚ) : ℝ) ≠ 0
    exact_mod_cast (mem_support_iff.mp hα)
  rw [rationalAxisScaling_map_real] at hreal
  have hsource := scaleMvPolynomialAxes_support_subset (fun i => (T i : ℝ))
    (MvPolynomial.map (algebraMap ℚ ℝ) P) hreal
  apply mem_support_iff.mpr
  intro hz
  rw [mem_support_iff, coeff_map, hz, map_zero] at hsource
  exact hsource rfl

theorem rationalAxisScaling_totalDegree_le {σ : Type*} (T : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    (MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P).totalDegree ≤
      P.totalDegree :=
  totalDegree_le_of_support_subset (rationalAxisScaling_support_subset T P)

theorem rationalAxisScaling_mem_weightedSupportLE {σ : Type*} (T : σ → ℚ)
    (w : σ → ℕ) (d : ℕ) {P : MvPolynomial σ ℚ}
    (hP : P ∈ weightedSupportLE w d) :
    MvPolynomial.aeval (fun i => MvPolynomial.C (T i) * MvPolynomial.X i) P ∈
      weightedSupportLE w d := by
  intro α hα
  exact hP (rationalAxisScaling_support_subset T P hα)

end Erdos3


namespace Erdos3

open MvPolynomial

variable {U B : Type*}

theorem jointPolynomialDilation_coefficientGrid
    (R : MvPolynomial (U ⊕ B) ℝ) (q l d : ℕ) (hq : 0 < q)
    (hdegree : R.totalDegree ≤ d) (hR : realPolynomialCoefficientGrid l R) :
    realPolynomialCoefficientGrid (q ^ d * l)
      (scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)⁻¹) (fun _ : B => 1)) R) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [scaleMvPolynomialAxes_eq_aeval, Nat.mul_comm (q ^ d) l]
  apply realPolynomialCoefficientGrid_substitute R _ l q d hdegree hR
  intro i
  cases i with
  | inl u =>
    apply (realPolynomialCoefficientGrid_iff _ _).mpr
    simp only [Sum.elim_inl]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hq0, map_one, one_mul]
    exact X_mem_integralRealPolynomialSubring _
  | inr b =>
    simpa only [Sum.elim_inr, map_one, one_mul] using
      realPolynomialCoefficientGrid_X q (Sum.inr b : U ⊕ B)

theorem jointPolynomialDilation_totalDegree_le
    (R : MvPolynomial (U ⊕ B) ℝ) (q : ℕ) :
    (scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)⁻¹) (fun _ : B => 1)) R).totalDegree ≤
      R.totalDegree :=
  scaleMvPolynomialAxes_totalDegree_le _ R

noncomputable def jointRationalPolynomialDilation (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) :
    MvPolynomial (U ⊕ B) ℚ :=
  aeval (fun i => C (Sum.elim (fun _ : U => (q : ℚ)⁻¹) (fun _ : B => 1) i) * X i) R

theorem jointRationalPolynomialDilation_map (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) :
    map (algebraMap ℚ ℝ) (jointRationalPolynomialDilation q R) =
      scaleMvPolynomialAxes (Sum.elim (fun _ : U => (q : ℝ)⁻¹) (fun _ : B => 1))
        (map (algebraMap ℚ ℝ) R) := by
  rw [jointRationalPolynomialDilation, rationalAxisScaling_map_real]
  congr 1
  funext i
  cases i <;> simp

theorem jointRationalPolynomialDilation_eval₂ (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ)
    (u : U → ℝ) (b : B → ℝ) :
    eval₂ (algebraMap ℚ ℝ) (Sum.elim u b) (jointRationalPolynomialDilation q R) =
      eval₂ (algebraMap ℚ ℝ) (Sum.elim (fun i => u i / (q : ℝ)) b) R := by
  rw [← eval_map, jointRationalPolynomialDilation_map, scaleMvPolynomialAxes_eval, eval_map]
  congr 1
  funext i
  cases i <;> simp [div_eq_mul_inv, mul_comm]

theorem jointRationalPolynomialDilation_totalDegree_le
    (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) :
    (jointRationalPolynomialDilation q R).totalDegree ≤ R.totalDegree :=
  rationalAxisScaling_totalDegree_le _ R

theorem jointRationalPolynomialDilation_denominatorGrid
    (R : MvPolynomial (U ⊕ B) ℚ) (q l d : ℕ) (hq : 0 < q)
    (hdegree : R.totalDegree ≤ d)
    (hR : (fun α => R.coeff α) ∈ denominatorGrid l) :
    (fun α => (jointRationalPolynomialDilation q R).coeff α) ∈
      denominatorGrid (q ^ d * l) := by
  apply (realPolynomialCoefficientGrid_ratCast_iff _ _).mp
  rw [jointRationalPolynomialDilation_map]
  apply jointPolynomialDilation_coefficientGrid _ q l d hq
  · apply le_trans (b := R.totalDegree) ?_ hdegree
    unfold totalDegree
    apply Finset.sup_le
    intro α hα
    exact le_totalDegree (support_map_subset (algebraMap ℚ ℝ) R hα)
  · exact (realPolynomialCoefficientGrid_ratCast_iff _ _).mpr hR

theorem jointRationalPolynomialDilation_mem_weightedSupportLE
    (q : ℕ) (R : MvPolynomial (U ⊕ B) ℚ) (w : U ⊕ B → ℕ) (d : ℕ)
    (hR : R ∈ weightedSupportLE w d) :
    jointRationalPolynomialDilation q R ∈ weightedSupportLE w d :=
  rationalAxisScaling_mem_weightedSupportLE _ w d hR

end Erdos3

end OAI
