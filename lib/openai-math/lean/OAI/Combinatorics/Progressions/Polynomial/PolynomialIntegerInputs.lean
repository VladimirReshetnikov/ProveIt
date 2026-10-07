/- Modified for ProveIt: import Lean 4.32 compatibility declarations and
simplify zero polynomial coefficients explicitly. Statements unchanged. -/
import OAI.Compat.BigOperators
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.MetricSpace.Lipschitz
import OAI.Combinatorics.Progressions.Estimates.UniformProductAccuracy
import OAI.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
import OAI.Combinatorics.Progressions.Linear.RationalMatrixSeparation
import OAI.Combinatorics.Progressions.Polynomial.IntegerPolynomialCongruence
import OAI.Combinatorics.Progressions.Polynomial.PolynomialTermCount

namespace OAI

section

namespace Erdos3

open MvPolynomial

def RationalPolynomialHeightLE {σ : Type*} (p : MvPolynomial σ ℚ) (H : ℕ) : Prop :=
  ∀ m, RationalHeightLE (p.coeff m) H

namespace RationalPolynomialHeightLE

variable {σ : Type*} {p : MvPolynomial σ ℚ} {H K : ℕ}

theorem mono (hp : RationalPolynomialHeightLE p H) (hHK : H ≤ K) :
    RationalPolynomialHeightLE p K := fun m => (hp m).mono hHK

theorem one_le (hp : RationalPolynomialHeightLE p H) : 1 ≤ H :=
  (Nat.one_le_iff_ne_zero.mpr (p.coeff 0).den_ne_zero).trans (hp 0).2

theorem zero (hH : 1 ≤ H) : RationalPolynomialHeightLE (0 : MvPolynomial σ ℚ) H := by
  intro m
  simpa only [MvPolynomial.coeff_zero] using rationalHeightLE_zero hH

theorem C {q : ℚ} (hq : RationalHeightLE q H) :
    RationalPolynomialHeightLE (MvPolynomial.C q : MvPolynomial σ ℚ) H := by
  classical
  intro m
  rw [coeff_C]
  split_ifs
  · exact hq
  · exact rationalHeightLE_zero
      ((Nat.one_le_iff_ne_zero.mpr q.den_ne_zero).trans hq.2)

theorem X (x : σ) : RationalPolynomialHeightLE (MvPolynomial.X x : MvPolynomial σ ℚ) 1 := by
  classical
  intro m
  rw [coeff_X]
  split_ifs
  · exact rationalHeightLE_one le_rfl
  · exact rationalHeightLE_zero le_rfl

theorem C_mul {q : ℚ} (hq : RationalHeightLE q H)
    (hp : RationalPolynomialHeightLE p K) :
    RationalPolynomialHeightLE (MvPolynomial.C q * p) (H * K) := by
  intro m
  rw [coeff_C_mul]
  exact hq.mul (hp m)

theorem mul_X (hp : RationalPolynomialHeightLE p H) (x : σ) :
    RationalPolynomialHeightLE (p * MvPolynomial.X x) H := by
  classical
  intro m
  rw [coeff_mul_X']
  split_ifs
  · exact hp _
  · exact rationalHeightLE_zero hp.one_le

theorem sum {ι : Type*} [Fintype ι] (p : ι → MvPolynomial σ ℚ)
    (hp : ∀ i, RationalPolynomialHeightLE (p i) H) :
    RationalPolynomialHeightLE (∑ i, p i) ((Fintype.card ι + 1) * H ^ Fintype.card ι) := by
  classical
  intro m
  rw [coeff_sum]
  exact rationalHeightLE_sum (fun i => (p i).coeff m) (fun i => hp i m)

theorem sum_finset {ι : Type*} (t : Finset ι) (p : ι → MvPolynomial σ ℚ)
    (hp : ∀ i ∈ t, RationalPolynomialHeightLE (p i) H) :
    RationalPolynomialHeightLE (∑ i ∈ t, p i) ((t.card + 1) * H ^ t.card) := by
  classical
  simpa only [Fintype.card_coe, Finset.sum_coe_sort] using
    sum (fun i : t => p i) (fun i => hp i i.property)

end RationalPolynomialHeightLE

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

noncomputable def polynomialDenominator (P : MvPolynomial σ ℚ) : ℕ :=
  arrayDenominator (fun m : P.support => P.coeff m.val)

theorem polynomialDenominator_pos (P : MvPolynomial σ ℚ) : 0 < polynomialDenominator P :=
  arrayDenominator_pos _

theorem polynomialDenominator_le (P : MvPolynomial σ ℚ) {H : ℕ}
    (hP : RationalPolynomialHeightLE P H) : polynomialDenominator P ≤ H ^ P.support.card := by
  simpa only [polynomialDenominator, Fintype.card_coe] using
    arrayDenominator_le (fun m : P.support => P.coeff m.val) (fun m => (hP m.val).2)

noncomputable def integralNumeratorPolynomial (P : MvPolynomial σ ℚ) (q s : ℕ) :
    MvPolynomial σ ℤ := by
  classical
  exact ∑ m : P.support, monomial m.val
    (clearedArray (fun n : P.support => P.coeff n.val) m * (q : ℤ) ^ (s - m.val.sum (fun _ n => n)))

theorem product_scaled_powers [Fintype σ] (x : σ → ℚ) (q : ℚ) (m : σ →₀ ℕ) :
    (∏ i, (q * x i) ^ m i) = q ^ m.sum (fun _ n => n) * ∏ i, x i ^ m i := by
  classical
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]

theorem integralNumeratorPolynomial_eval [Fintype σ] (P : MvPolynomial σ ℚ) (q s : ℕ)
    (hdegree : P.totalDegree ≤ s) (x : σ → ℚ) (z : σ → ℤ)
    (hz : ∀ i, (q : ℚ) * x i = (z i : ℚ)) :
    ((eval z (integralNumeratorPolynomial P q s) : ℤ) : ℚ) =
      (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * eval x P := by
  classical
  rw [integralNumeratorPolynomial, map_sum]
  push_cast
  simp only [eval_monomial, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [eval_eq']
  rw [← Finset.sum_coe_sort P.support]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hm : m.val.sum (fun _ n => n) ≤ s := (le_totalDegree m.property).trans hdegree
  rw [clearedArray_cast]
  have hprod : ((m.val.prod (fun i n => z i ^ n) : ℤ) : ℚ) =
      (q : ℚ) ^ m.val.sum (fun _ n => n) * ∏ i, x i ^ m.val i := by
    rw [Finsupp.prod_pow]
    simp only [Int.cast_prod, Int.cast_pow]
    simp_rw [← hz]
    exact product_scaled_powers x (q : ℚ) m.val
  rw [hprod]
  change ((polynomialDenominator P : ℚ) * P.coeff m.val) * (q : ℚ) ^ (s - m.val.sum (fun _ n => n)) *
      ((q : ℚ) ^ m.val.sum (fun _ n => n) * ∏ i, x i ^ m.val i) = _
  calc
    _ = (polynomialDenominator P : ℚ) *
        ((q : ℚ) ^ (s - m.val.sum (fun _ n => n)) * (q : ℚ) ^ m.val.sum (fun _ n => n)) *
        (P.coeff m.val * ∏ i, x i ^ m.val i) := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hm]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem abs_aeval_le_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℚ)
    (v : σ → ℝ) {A B : ℝ} {s : ℕ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hcoeff : ∀ m, |((P.coeff m : ℚ) : ℝ)| ≤ A) (hv : ∀ i, |v i| ≤ B)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P| ≤ P.support.card * A * B ^ s := by
  classical
  change |P.eval₂ (algebraMap ℚ ℝ) v| ≤ _
  rw [eval₂_eq']
  calc
    _ ≤ ∑ m ∈ P.support, |algebraMap ℚ ℝ (P.coeff m) * ∏ i, v i ^ m i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ P.support, A * B ^ s := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_mul, Finset.abs_prod]
      have hprod : (∏ i, |v i ^ m i|) ≤ B ^ s := by
        calc
          _ = ∏ i, |v i| ^ m i := by simp only [abs_pow]
          _ ≤ ∏ i, B ^ m i :=
            Finset.prod_le_prod₀ (fun _ _ => by positivity)
              (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hv i) _)
          _ = B ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ B ^ s := by
            apply pow_le_pow_right₀ hB
            have hmdegree := (le_totalDegree hm).trans hdegree
            rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hmdegree
      exact mul_le_mul (hcoeff m) hprod (by positivity) hA
    _ = _ := by simp [mul_assoc]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal

theorem abs_aeval_sub_aeval_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℚ)
    (v w : σ → ℝ) {A B δ : ℝ} {s : ℕ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hcoeff : ∀ m, |((P.coeff m : ℚ) : ℝ)| ≤ A)
    (hv : ∀ i, |v i| ≤ B) (hw : ∀ i, |w i| ≤ B) (hvw : ∀ i, |v i - w i| ≤ δ)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P - aeval w P| ≤
      P.support.card * A * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)) * δ := by
  classical
  have hmonomial (m : σ →₀ ℕ) (hm : m ∈ P.support) :
      |(∏ i, v i ^ m i) - ∏ i, w i ^ m i| ≤
        Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ := by
    have hmdeg (i : σ) : m i ≤ s :=
      (monomial_le_degreeOf i hm).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ B) (i : σ) : |u i ^ m i| ≤ B ^ s := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hu i) _).trans (pow_le_pow_right₀ hB (hmdeg i))
    simpa only [Finset.card_univ] using
      abs_finset_prod_sub_prod_le Finset.univ (fun i => v i ^ m i) (fun i => w i ^ m i)
        (one_le_pow₀ hB) (by positivity)
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i)
        (fun i _ => abs_pow_sub_pow_box_bound hB hδ (hv i) (hw i) (hvw i) (hmdeg i))
  change |P.eval₂ (algebraMap ℚ ℝ) v - P.eval₂ (algebraMap ℚ ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ P.support, |algebraMap ℚ ℝ (P.coeff m) * ∏ i, v i ^ m i -
          algebraMap ℚ ℝ (P.coeff m) * ∏ i, w i ^ m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ P.support, A * (Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hcoeff m) (hmonomial m hm) (abs_nonneg _) hA
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
      ring

theorem lipschitzOn_mvPolynomial_aeval_box {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℚ)
    (A B : ℝ≥0) {s : ℕ} (hB : 1 ≤ B)
    (hcoeff : ∀ m, |((P.coeff m : ℚ) : ℝ)| ≤ A) (hdegree : P.totalDegree ≤ s) :
    LipschitzOnWith ((P.support.card : ℝ≥0) * A * Fintype.card σ * s *
      B ^ (s * (Fintype.card σ + 1))) (fun v : σ → ℝ => aeval v P)
      {v | ∀ i, |v i| ≤ B} := by
  apply LipschitzOnWith.of_dist_le_mul
  intro v hv w hw
  rw [Real.dist_eq]
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hdiff (i : σ) : |v i - w i| ≤ dist v w := by
    simpa only [Real.dist_eq] using dist_le_pi_dist v w i
  simpa only [NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow] using
    abs_aeval_sub_aeval_box_bound P v w A.coe_nonneg hBr dist_nonneg hcoeff hv hw hdiff hdegree

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem monomialScale_mul_normalized_prod {σ : Type*} [Fintype σ]
    (T v : σ → ℝ) (hT : ∀ i, 0 < T i) (α : σ →₀ ℕ) :
    monomialScale T α * (∏ i, (v i / T i) ^ α i) = ∏ i, v i ^ α i := by
  classical
  rw [monomialScale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← mul_pow, mul_div_cancel₀ _ (hT i).ne']

theorem abs_eval_le_scaled_box_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T v : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α)
    (hv : ∀ i, |v i| ≤ T i) :
    |eval v P| ≤ P.support.card * M := by
  classical
  have hv' (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i), div_le_one (hT i)]
    exact hv i
  change |P.eval₂ (RingHom.id ℝ) v| ≤ _
  rw [eval₂_eq']
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _α ∈ P.support, M := by
      apply Finset.sum_le_sum
      intro α _
      change |P.coeff α * ∏ i, v i ^ α i| ≤ M
      rw [← monomialScale_mul_normalized_prod T v hT α, abs_mul,
        abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      have hprod : |∏ i, (v i / T i) ^ α i| ≤ 1 := by
        rw [Finset.abs_prod]
        apply Finset.prod_le_one₀ (fun _ _ => abs_nonneg _)
        intro i _
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (hv' i)
      calc
        _ ≤ (M / monomialScale T α) * (monomialScale T α * 1) :=
          mul_le_mul (hcoeff α)
            (mul_le_mul_of_nonneg_left hprod (monomialScale_pos T hT α).le)
            (mul_nonneg (monomialScale_pos T hT α).le (abs_nonneg _))
            (div_nonneg hM (monomialScale_pos T hT α).le)
        _ = M := by rw [mul_one, div_mul_cancel₀ _ (monomialScale_pos T hT α).ne']
    _ = _ := by simp

theorem abs_eval_sub_eval_scaled_box_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T v w : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M δ : ℝ} {s : ℕ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α)
    (hv : ∀ i, |v i| ≤ T i) (hw : ∀ i, |w i| ≤ T i)
    (hvw : ∀ i, |v i - w i| ≤ T i * δ) (hdegree : P.totalDegree ≤ s) :
    |eval v P - eval w P| ≤ P.support.card * M * Fintype.card σ * s * δ := by
  classical
  have hunit (u : σ → ℝ) (hu : ∀ i, |u i| ≤ T i) (i : σ) :
      |u i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i), div_le_one (hT i)]
    exact hu i
  have hdiff (i : σ) : |v i / T i - w i / T i| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos (hT i), div_le_iff₀ (hT i), mul_comm]
    exact hvw i
  have hmonomial (α : σ →₀ ℕ) (hα : α ∈ P.support) :
      |(∏ i, (v i / T i) ^ α i) - ∏ i, (w i / T i) ^ α i| ≤
        Fintype.card σ * (δ * s) := by
    have hdeg (i : σ) : α i ≤ s :=
      (monomial_le_degreeOf i hα).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ T i) (i : σ) :
        |(u i / T i) ^ α i| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hunit u hu i)
    have hp (i : σ) : |(v i / T i) ^ α i - (w i / T i) ^ α i| ≤ δ * s := by
      simpa only [one_pow, mul_one] using abs_pow_sub_pow_box_bound
        (le_refl (1 : ℝ)) hδ (hunit v hv i) (hunit w hw i) (hdiff i) (hdeg i)
    simpa only [Finset.card_univ, one_pow, mul_one] using
      abs_finset_prod_sub_prod_le Finset.univ
        (fun i => (v i / T i) ^ α i) (fun i => (w i / T i) ^ α i)
        (le_refl (1 : ℝ)) (mul_nonneg hδ (Nat.cast_nonneg s))
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i) (fun i _ => hp i)
  change |P.eval₂ (RingHom.id ℝ) v - P.eval₂ (RingHom.id ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _α ∈ P.support, M * (Fintype.card σ * (δ * s)) := by
      apply Finset.sum_le_sum
      intro α hα
      change |P.coeff α * ∏ i, v i ^ α i - P.coeff α * ∏ i, w i ^ α i| ≤ _
      rw [← mul_sub, ← monomialScale_mul_normalized_prod T v hT α,
        ← monomialScale_mul_normalized_prod T w hT α, ← mul_sub,
        abs_mul, abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      calc
        _ ≤ (M / monomialScale T α) *
            (monomialScale T α * (Fintype.card σ * (δ * s))) :=
          mul_le_mul (hcoeff α)
            (mul_le_mul_of_nonneg_left (hmonomial α hα) (monomialScale_pos T hT α).le)
            (mul_nonneg (monomialScale_pos T hT α).le (abs_nonneg _))
            (div_nonneg hM (monomialScale_pos T hT α).le)
        _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ (monomialScale_pos T hT α).ne']
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem rational_polynomial_eval_sub_integer_multiple {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (q s l : ℕ) (hq : 0 < q) (hdegree : P.totalDegree ≤ s)
    (x y : σ → ℚ) (hx : x ∈ denominatorGrid q) (hy : y ∈ denominatorGrid q)
    (hxy : x - y ∈ scaledIntegerGrid (l * polynomialDenominator P * q ^ s)) :
    ∃ k : ℤ, eval x P - eval y P = (l : ℚ) * k := by
  classical
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := hy
  obtain ⟨v, hv⟩ := hxy
  let T := l * polynomialDenominator P * q ^ s
  let Q := integralNumeratorPolynomial P q s
  have hdiff : ∀ i, (T : ℤ) ∣ z i - w i := by
    intro i
    refine ⟨(q : ℤ) * v i, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    have hi := congrFun hv i
    change x i - y i = (T : ℚ) * (v i : ℚ) at hi
    have hzi : (q : ℚ) * x i = (z i : ℚ) := hz i
    have hwi : (q : ℚ) * y i = (w i : ℚ) := hw i
    rw [← hzi, ← hwi, ← mul_sub, hi]
    ring
  obtain ⟨k, hk⟩ := integer_polynomial_sub_dvd Q z w (T : ℤ) hdiff
  refine ⟨k, ?_⟩
  have hD : (polynomialDenominator P : ℚ) ≠ 0 := by exact_mod_cast (polynomialDenominator_pos P).ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  apply mul_left_cancel₀ (mul_ne_zero hD (pow_ne_zero s hq'))
  calc
    (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * (eval x P - eval y P) =
        ((eval z Q - eval w Q : ℤ) : ℚ) := by
      push_cast
      rw [integralNumeratorPolynomial_eval P q s hdegree x z hz,
        integralNumeratorPolynomial_eval P q s hdegree y w hw]
      ring
    _ = ((T : ℤ) * k : ℤ) := by rw [hk]
    _ = (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * ((l : ℚ) * k) := by
      push_cast
      dsimp [T]
      push_cast
      ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {ι σ : Type*} [Fintype ι]

noncomputable def polynomialFamilyDenominator (P : ι → MvPolynomial σ ℚ) : ℕ :=
  ∏ i, polynomialDenominator (P i)

theorem polynomialFamilyDenominator_pos (P : ι → MvPolynomial σ ℚ) :
    0 < polynomialFamilyDenominator P :=
  Finset.prod_pos (fun i _ => polynomialDenominator_pos (P i))

theorem polynomialDenominator_dvd_family (P : ι → MvPolynomial σ ℚ) (i : ι) :
    polynomialDenominator (P i) ∣ polynomialFamilyDenominator P :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem polynomialDenominator_exp_bound (P : MvPolynomial σ ℚ) {p : ℝ}
    (hp : 0 ≤ p) (a c : ℕ)
    (hcoeff : ∀ m, ((P.coeff m).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : (P.support.card : ℝ) ≤ (p + 2) ^ c) :
    (polynomialDenominator P : ℝ) ≤ Real.exp ((p + 2) ^ (a + c)) := by
  classical
  unfold polynomialDenominator arrayDenominator
  rw [Nat.cast_prod]
  apply product_exponential_budget _ _ hp a c
  · intro i _
    positivity
  · intro i _
    exact hcoeff i.val
  · simpa only [Finset.card_univ, Fintype.card_coe] using hcard

theorem polynomialFamilyDenominator_exp_bound (P : ι → MvPolynomial σ ℚ) {p : ℝ}
    (hp : 0 ≤ p) (a b c : ℕ)
    (hcoeff : ∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : ∀ i, ((P i).support.card : ℝ) ≤ (p + 2) ^ c)
    (hι : (Fintype.card ι : ℝ) ≤ (p + 2) ^ b) :
    (polynomialFamilyDenominator P : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + b)) := by
  classical
  unfold polynomialFamilyDenominator
  rw [Nat.cast_prod]
  apply product_exponential_budget _ _ hp (a + c) b
  · intro i _
    positivity
  · intro i _
    exact polynomialDenominator_exp_bound (P i) hp a c (hcoeff i) (hcard i)
  · simpa only [Finset.card_univ] using hι

theorem rational_polynomial_family_eval_sub_mem_grid [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (q s l : ℕ) (hq : 0 < q)
    (hdegree : ∀ i, (P i).totalDegree ≤ s) (x y : σ → ℚ)
    (hx : x ∈ denominatorGrid q) (hy : y ∈ denominatorGrid q)
    (hxy : x - y ∈ scaledIntegerGrid (l * polynomialFamilyDenominator P * q ^ s)) :
    (fun i => eval x (P i) - eval y (P i)) ∈ scaledIntegerGrid l := by
  classical
  have h (i : ι) : ∃ k : ℤ, eval x (P i) - eval y (P i) = (l : ℚ) * k := by
    apply rational_polynomial_eval_sub_integer_multiple (P i) q s l hq (hdegree i) x y hx hy
    apply scaledIntegerGrid_subset_of_dvd _ hxy
    exact mul_dvd_mul (mul_dvd_mul dvd_rfl (polynomialDenominator_dvd_family P i)) dvd_rfl
  choose z hz using h
  exact ⟨z, funext hz⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem slowPolynomial_oscillation_on_slice {I : Type*} [Fintype I]
    (N : I → ℕ) {q : ℕ} (A : ResidueBoxSlice N q)
    (hA : ∀ i, 0 < A.length i) {ρ M : ℝ} {s : ℕ}
    (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (hwidth : ∀ i, (q : ℝ) * A.length i ≤ ρ * N i)
    (P : MvPolynomial I ℝ) (hdegree : P.totalDegree ≤ s)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (j : ∀ i, Fin (A.length i)) :
    |MvPolynomial.eval (fun i => ((A.point j i).val : ℝ)) P -
        MvPolynomial.eval (fun i => (A.start i : ℝ)) P| ≤
      ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s * M * Fintype.card I * s * ρ := by
  have hstart (i : I) : A.start i < N i := by
    simpa only [Nat.mul_zero, Nat.add_zero] using A.inside i 0 (hA i)
  have hN (i : I) : (0 : ℝ) < N i := by exact_mod_cast (Nat.zero_le _).trans_lt (hstart i)
  have hv (i : I) : |((A.point j i).val : ℝ)| ≤ (N i : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (A.point j i).isLt.le
  have hw (i : I) : |(A.start i : ℝ)| ≤ (N i : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (hstart i).le
  have hvw (i : I) : |((A.point j i).val : ℝ) - (A.start i : ℝ)| ≤ (N i : ℝ) * ρ := by
    change |((A.start i + q * (j i).val : ℕ) : ℝ) - (A.start i : ℝ)| ≤ _
    rw [Nat.cast_add, Nat.cast_mul, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    have hj : ((j i).val : ℝ) ≤ A.length i := by exact_mod_cast (j i).isLt.le
    exact (mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg q)).trans (by simpa [mul_comm] using hwidth i)
  have hbound := abs_eval_sub_eval_scaled_box_bound P (fun i => (N i : ℝ))
    (fun i => ((A.point j i).val : ℝ)) (fun i => (A.start i : ℝ)) hN hM hρ hcoeff hv hw hvw hdegree
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  exact hbound.trans (by gcongr)

theorem exists_slowPolynomial_residueSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) {q : ℕ} (hq : 0 < q) {ρ M : ℝ} {s : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hM : 0 ≤ M)
    (hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i)
    (P : MvPolynomial I ℝ) (hdegree : P.totalDegree ≤ s)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j)) ∧
      ∀ j : (∀ i, Fin (A.length i)),
        |MvPolynomial.eval (fun i => ((A.point j i).val : ℝ)) P -
            MvPolynomial.eval (fun i => (A.start i : ℝ)) P| ≤
          ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s * M * Fintype.card I * s * ρ := by
  obtain ⟨A, hA, hscore⟩ := exists_narrow_residueBoxSlice N hq hρ hρ1 hlarge f
  exact ⟨A, fun i => ⟨(hA i).1, (hA i).2.1⟩, hscore,
    slowPolynomial_oscillation_on_slice N A (fun i => (hA i).1) hρ.le hM
      (fun i => (hA i).2.2) P hdegree hcoeff⟩

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem polynomialFamilyDenominator_degree_budget {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (r : ℕ) {p : ℝ}
    (hdegree : ∀ i, (P i).totalDegree ≤ r) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hcoeff : ∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp p) :
    (polynomialFamilyDenominator P : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3)) := by
  let t := p + (r + 3 : ℕ)
  have ht : 3 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hpT : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hr : (r : ℝ) + 1 ≤ t := by dsimp [t]; push_cast; linarith
  have hvars : (Fintype.card σ : ℝ) + 1 ≤ t := by
    dsimp [t]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hcard : ∀ i, ((P i).support.card : ℝ) ≤ t ^ (r + 1) := by
    intro i
    have h := (Nat.cast_le (α := ℝ)).mpr (polynomial_support_card_le (P i) (hdegree i))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h
    apply h.trans
    calc
      _ ≤ t * t ^ r := mul_le_mul hr (pow_le_pow_left₀ (by positivity) hvars r) (by positivity) (by linarith)
      _ = t ^ (r + 1) := (pow_succ' _ _).symm
  have hD := polynomialFamilyDenominator_exp_bound P (p := t - 2) (by linarith) 1 1 (r + 1)
    (by intro i m; rw [sub_add_cancel, pow_one]; exact (hcoeff i m).trans (Real.exp_le_exp.mpr hpT))
    (by simpa only [sub_add_cancel] using hcard)
    (by rw [sub_add_cancel, pow_one]; exact hι.trans hpT)
  simpa only [sub_add_cancel, show 1 + (r + 1) + 1 = r + 3 by omega, t, Nat.cast_add, Nat.cast_ofNat] using hD

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem polynomial_integer_value_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (z : σ → ℤ) :
    ∃ a : ℤ, (polynomialDenominator P : ℚ) * eval (fun i => (z i : ℚ)) P = (a : ℚ) := by
  refine ⟨eval z (integralNumeratorPolynomial P 1 P.totalDegree), ?_⟩
  have h := integralNumeratorPolynomial_eval P 1 P.totalDegree le_rfl
    (fun i => (z i : ℚ)) z (by simp)
  simpa only [Nat.cast_one, one_pow, mul_one] using h.symm

theorem polynomial_family_integer_values_grid {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (z : σ → ℤ) :
    (fun i => eval (fun j => (z j : ℚ)) (P i)) ∈ denominatorGrid (polynomialFamilyDenominator P) := by
  classical
  have h (i : ι) : ∃ a : ℤ,
      (polynomialFamilyDenominator P : ℚ) * eval (fun j => (z j : ℚ)) (P i) = (a : ℚ) := by
    obtain ⟨k, hk⟩ := polynomialDenominator_dvd_family P i
    obtain ⟨a, ha⟩ := polynomial_integer_value_denominator (P i) z
    refine ⟨(k : ℤ) * a, ?_⟩
    rw [hk, Nat.cast_mul]
    calc
      _ = (k : ℚ) * ((polynomialDenominator (P i) : ℚ) * eval (fun j => (z j : ℚ)) (P i)) := by ring
      _ = _ := by rw [ha]; push_cast; rfl
  choose a ha using h
  exact ⟨a, ha⟩

theorem integer_difference_mem_grid {σ : Type*} (x y : σ → ℤ) (M : ℕ)
    (hxy : ∀ i, (M : ℤ) ∣ x i - y i) :
    (fun i => (x i : ℚ)) - (fun i => (y i : ℚ)) ∈ scaledIntegerGrid M := by
  classical
  choose z hz using hxy
  refine ⟨z, ?_⟩
  funext i
  have hi := congrArg (fun a : ℤ => (a : ℚ)) (hz i)
  push_cast at hi
  exact hi

theorem polynomial_family_integer_congruence {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (r l : ℕ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (x y : σ → ℤ) (hxy : ∀ j, ((l * polynomialFamilyDenominator P : ℕ) : ℤ) ∣ x j - y j) :
    (fun i => eval (fun j => (x j : ℚ)) (P i) - eval (fun j => (y j : ℚ)) (P i)) ∈
      scaledIntegerGrid l := by
  apply rational_polynomial_family_eval_sub_mem_grid P 1 r l (by omega) hdegree
  · exact ⟨x, by simp⟩
  · exact ⟨y, by simp⟩
  · simpa only [one_pow, mul_one] using integer_difference_mem_grid x y _ hxy

end Erdos3

end

end OAI
