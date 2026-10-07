import Mathlib

namespace OAI

section

namespace Erdos3

theorem natPolynomial_eval_nonneg (P : Polynomial ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))

theorem exists_natPolynomial_eval_budget (P : Polynomial ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + N) ^ N := by
  let N := P.eval 1 + P.natDegree + 2
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro p hp
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by dsimp [N]; omega)
  have ht : 1 ≤ p + N := by linarith
  have hcoeff : ((P.eval 1 : ℕ) : ℝ) ≤ p + N := by
    have h : P.eval 1 ≤ N := by dsimp [N]; omega
    exact (Nat.cast_le.mpr h).trans (le_add_of_nonneg_left hp)
  have hsum : (∑ n ∈ P.support, (P.coeff n : ℝ)) = ((P.eval 1 : ℕ) : ℝ) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [one_pow, mul_one, Nat.cast_sum]
  calc
    P.eval₂ (Nat.castRingHom ℝ) p = ∑ n ∈ P.support, (P.coeff n : ℝ) * p ^ n := by
      rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      rfl
    _ ≤ ∑ n ∈ P.support, (P.coeff n : ℝ) * (p + N) ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (pow_le_pow_left₀ hp (le_add_of_nonneg_right (Nat.cast_nonneg N)) n).trans
      exact pow_le_pow_right₀ ht (Polynomial.le_natDegree_of_mem_supp n hn)
    _ = ((P.eval 1 : ℕ) : ℝ) * (p + N) ^ P.natDegree := by rw [← Finset.sum_mul, hsum]
    _ ≤ (p + N) * (p + N) ^ P.natDegree :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (by linarith) _)
    _ = (p + N) ^ (P.natDegree + 1) := (pow_succ' _ _).symm
    _ ≤ (p + N) ^ N := pow_le_pow_right₀ ht (by dsimp [N]; omega)

end Erdos3

end

section

namespace Erdos3

theorem exists_majorPhaseDetectedDecomposition_budget (a b c m d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let E := (p + a) ^ a
      let Q := E + p + 1
      let P := (Q + b) ^ b + Q
      let D := (P + c) ^ c
      let B := (p + C) ^ C
      E ≤ B ∧ E + D ≤ B ∧ (m : ℝ) * p + D ≤ B ∧
        (m : ℝ) * E + D ≤ B ∧ (d : ℝ) * E + D ≤ B ∧
        (d : ℝ) * p + D ≤ B ∧ D ≤ B := by
  let E : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := E + Polynomial.X + 1
  let P : Polynomial ℕ := (Q + Polynomial.C b) ^ b + Q
  let D : Polynomial ℕ := (P + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (E + D + Polynomial.C (m + d + 1) * (Polynomial.X + E) + 1)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  let e : ℝ := (p + a) ^ a
  let q : ℝ := e + p + 1
  let r : ℝ := (q + b) ^ b + q
  let δ : ℝ := (r + c) ^ c
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have htotal : e + δ + ((m : ℝ) + d + 1) * (p + e) + 1 ≤ (p + C) ^ C := by
    simpa [E, Q, P, D, e, q, r, δ, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  change e ≤ _ ∧ e + δ ≤ _ ∧ (m : ℝ) * p + δ ≤ _ ∧
    (m : ℝ) * e + δ ≤ _ ∧ (d : ℝ) * e + δ ≤ _ ∧
    (d : ℝ) * p + δ ≤ _ ∧ δ ≤ _
  have hmp : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hme : 0 ≤ (m : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
  have hdp : 0 ≤ (d : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hde : 0 ≤ (d : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem pow_mul_exp_le_exp_of_le_budget {q p D B : ℝ} {h m : ℕ}
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp p) (hp : 0 ≤ p)
    (hh : h ≤ m) (hbudget : (m : ℝ) * p + D ≤ B) :
    q ^ h * Real.exp D ≤ Real.exp B := by
  calc
    q ^ h * Real.exp D ≤ (Real.exp p) ^ h * Real.exp D :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq h) (Real.exp_nonneg D)
    _ = Real.exp ((h : ℝ) * p + D) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp B := by
      apply Real.exp_le_exp.mpr
      have hmul : (h : ℝ) * p ≤ (m : ℝ) * p :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh) hp
      linarith

theorem nat_pow_mul_le_exp_of_le_budget {q l d : ℕ} {p D B : ℝ}
    (hq : (q : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp D)
    (hbudget : (d : ℝ) * p + D ≤ B) :
    ((q ^ d * l : ℕ) : ℝ) ≤ Real.exp B := by
  calc
    ((q ^ d * l : ℕ) : ℝ) = (q : ℝ) ^ d * (l : ℝ) := by norm_cast
    _ ≤ (Real.exp p) ^ d * Real.exp D :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg q) hq d) hl
        (Nat.cast_nonneg l) (pow_nonneg (Real.exp_nonneg p) d)
    _ = Real.exp ((d : ℝ) * p + D) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp B := Real.exp_le_exp.mpr hbudget

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

def polynomialDensityBudget (e : ℕ) (P : ℝ) : ℝ :=
  (P+e)^e + (P+1)*P + P + 1

theorem polynomialDensityBudget_nonneg (e : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ polynomialDensityBudget e P := by
  unfold polynomialDensityBudget
  positivity

theorem polynomialDensityBudget_dominates (e : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    P ≤ polynomialDensityBudget e P ∧
      (P+e)^e ≤ polynomialDensityBudget e P ∧
      (P+1)*P ≤ polynomialDensityBudget e P := by
  have he : 0 ≤ (P+e)^e := by positivity
  have hp : 0 ≤ (P+1)*P := by positivity
  unfold polynomialDensityBudget
  constructor
  · linarith
  constructor <;> linarith

theorem coefficientSampleDomain_card_le_budget {I K : Type*} [Fintype I] [Fintype K]
    (e : ℕ) {P : ℝ} (hP : 0 ≤ P) (hI : (Fintype.card I : ℝ) ≤ P)
    (hK : (Fintype.card K : ℝ) ≤ P) :
    (Fintype.card (Option K × I) : ℝ) ≤ polynomialDensityBudget e P := by
  calc
    _ = ((Fintype.card K : ℝ)+1)*(Fintype.card I : ℝ) := by simp
    _ ≤ (P+1)*P := by gcongr
    _ ≤ _ := (polynomialDensityBudget_dominates e hP).2.2

theorem exists_polynomial_density_threshold (e A₀ : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P →
      (polynomialDensityBudget e P + A₀)^A₀ ≤ (P+A)^A := by
  let t : Polynomial ℕ := (Polynomial.X+Polynomial.C e)^e +
    (Polynomial.X+1)*Polynomial.X + Polynomial.X + 1
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget ((t+Polynomial.C A₀)^A₀)
  refine ⟨A, hA, ?_⟩
  intro P hP
  simpa [t, polynomialDensityBudget, Polynomial.eval₂_pow] using hb P hP

end Erdos3.VectorPolynomial

end

end OAI
