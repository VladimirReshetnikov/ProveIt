import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Pochhammer
import OAI.Combinatorics.Progressions.Estimates.FiniteDifferenceStability
import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename

namespace OAI

section

namespace Erdos3

open scoped BigOperators fwdDiff

theorem fwdDiff_iter_eq_zero_of_local {V : Type*} [AddCommGroup V]
    (g : ℕ → V) {d N : ℕ}
    (hzero : ∀ x, x + d < N → (fwdDiff 1)^[d] g x = 0)
    (k : ℕ) (hk : d ≤ k) : ∀ x, x + k < N → (fwdDiff 1)^[k] g x = 0 := by
  induction k, hk using Nat.le_induction with
  | base => exact hzero
  | succ k hk ih =>
    intro x hx
    rw [Function.iterate_succ_apply']
    change (fwdDiff 1)^[k] g (x + 1) - (fwdDiff 1)^[k] g x = 0
    rw [ih (x + 1) (by omega), ih x (by omega), sub_self]

theorem finite_interval_newton_formula (g : ℕ → ℤ) {s N : ℕ}
    (hzero : ∀ x, x + s + 1 < N → (fwdDiff 1)^[s + 1] g x = 0)
    (n : ℕ) (hn : n < N) :
    g n = ∑ k ∈ Finset.range (s + 1), (n.choose k : ℤ) * (fwdDiff 1)^[k] g 0 := by
  have hnewton := shift_eq_sum_fwdDiff_iter 1 g n 0
  simp only [nsmul_eq_mul, Nat.cast_id, mul_one, zero_add] at hnewton
  rw [hnewton]
  by_cases hns : n ≤ s
  · apply Finset.sum_subset (Finset.range_mono (by omega : n + 1 ≤ s + 1))
    intro k _ hk
    have hnk : n < k := by simp only [Finset.mem_range] at hk; omega
    simp [Nat.choose_eq_zero_of_lt hnk]
  · symm
    apply Finset.sum_subset (Finset.range_mono (by omega : s + 1 ≤ n + 1))
    intro k hk hks
    have hsk : s + 1 ≤ k := by simpa only [Finset.mem_range, not_lt] using hks
    have hkN : 0 + k < N := by have := Finset.mem_range.mp hk; omega
    have hz := fwdDiff_iter_eq_zero_of_local g (d := s + 1)
      (fun x hx => hzero x (by omega)) k hsk 0 hkN
    simp [hz]

noncomputable def integerNewtonPolynomial (s : ℕ) (c : ℕ → ℤ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (s + 1),
    Polynomial.C ((c k : ℝ) / (k.factorial : ℝ)) * descPochhammer ℝ k

theorem integerNewtonPolynomial_natDegree_le (s : ℕ) (c : ℕ → ℤ) :
    (integerNewtonPolynomial s c).natDegree ≤ s := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  rw [descPochhammer_natDegree]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)

theorem integerNewtonPolynomial_eval_nat (s n : ℕ) (c : ℕ → ℤ) :
    (integerNewtonPolynomial s c).eval (n : ℝ) =
      ((∑ k ∈ Finset.range (s + 1), (n.choose k : ℤ) * c k : ℤ) : ℝ) := by
  simp only [integerNewtonPolynomial, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C, Int.cast_sum, Int.cast_mul, Int.cast_natCast]
  apply Finset.sum_congr rfl
  intro k _
  rw [Nat.cast_choose_eq_descPochhammer_div (K := ℝ)]
  ring

theorem integerNewtonPolynomial_integer_valued (s n : ℕ) (c : ℕ → ℤ) :
    ∃ z : ℤ, (integerNewtonPolynomial s c).eval (n : ℝ) = z :=
  ⟨_, integerNewtonPolynomial_eval_nat s n c⟩

theorem exists_integer_polynomial_of_local_differences (g : ℕ → ℤ) {s N : ℕ}
    (hzero : ∀ x, x + s + 1 < N → (fwdDiff 1)^[s + 1] g x = 0) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ s ∧
      (∀ n : ℕ, ∃ z : ℤ, Q.eval (n : ℝ) = z) ∧
      ∀ n < N, Q.eval (n : ℝ) = (g n : ℝ) := by
  refine ⟨integerNewtonPolynomial s (fun index => (fwdDiff 1)^[index] g 0),
    integerNewtonPolynomial_natDegree_le _ _,
    fun n => integerNewtonPolynomial_integer_valued _ n _, ?_⟩
  intro n hn
  rw [integerNewtonPolynomial_eval_nat, ← finite_interval_newton_formula g hzero n hn]

theorem exists_integer_polynomial_lift (P : Polynomial ℝ) (g : ℕ → ℤ)
    {s N : ℕ} {ε : ℝ} (hdegree : P.natDegree ≤ s)
    (hsmall : (2 : ℝ) ^ (s + 1) * ε < 1)
    (happrox : ∀ n < N, ‖(g n : ℝ) - P.eval (n : ℝ)‖ ≤ ε) :
    ∃ Q : Polynomial ℝ, Q.natDegree ≤ s ∧
      (∀ n : ℕ, ∃ z : ℤ, Q.eval (n : ℝ) = z) ∧
      (∀ n < N, Q.eval (n : ℝ) = (g n : ℝ)) ∧
      ∀ n < N, ‖Q.eval (n : ℝ) - P.eval (n : ℝ)‖ ≤ ε := by
  obtain ⟨Q, hdeg, hint, heq⟩ := exists_integer_polynomial_of_local_differences g
    (integer_polynomial_lift_differences P g hdegree hsmall happrox)
  refine ⟨Q, hdeg, hint, heq, ?_⟩
  intro n hn
  rw [heq n hn]
  exact happrox n hn

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [Unique σ] [CommRing R]

theorem singleParameter_natDegree_le {p : MvPolynomial σ R} {h : ℕ}
    (hp : p ∈ weightedSupportLE (fun _ : σ => 1) h) :
    (uniqueAlgEquiv R σ p).natDegree ≤ h := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_uniqueAlgEquiv]
  by_contra hne
  have hbound := hp (mem_support_iff.mpr hne)
  change Finsupp.weight (fun _ : σ => 1) (Finsupp.single default n) ≤ h at hbound
  simp only [Finsupp.weight_single, smul_eq_mul, mul_one] at hbound
  omega

theorem singleParameter_symm_degree {p : Polynomial R} {h : ℕ}
    (hp : p.natDegree ≤ h) :
    (uniqueAlgEquiv R σ).symm p ∈ weightedSupportLE (fun _ : σ => 1) h := by
  intro α hα
  have hne := mem_support_iff.mp hα
  change ((uniqueAlgEquiv R σ).symm p).coeff α ≠ 0 at hne
  rw [coeff_uniqueAlgEquiv_symm] at hne
  have hbound := (Polynomial.le_natDegree_of_ne_zero hne).trans hp
  change Finsupp.weight (fun _ : σ => 1) α ≤ h
  rw [Finsupp.unique_single α, Finsupp.weight_single]
  simpa only [smul_eq_mul, mul_one] using hbound

theorem singleParameter_eval (p : MvPolynomial σ R) (x : R) :
    (uniqueAlgEquiv R σ p).eval x = aeval (fun _ : σ => x) p := by
  exact eval₂_const_uniqueAlgEquiv (φ := RingHom.id R)

theorem singleParameter_symm_eval (p : Polynomial R) (x : R) :
    aeval (fun _ : σ => x) ((uniqueAlgEquiv R σ).symm p) = p.eval x := by
  exact eval₂_const_uniqueAlgEquiv_symm (φ := RingHom.id R)

theorem exists_singleParameter_integer_lift (P : MvPolynomial σ ℝ) (g : ℕ → ℤ)
    {h N : ℕ} {ε : ℝ}
    (hdegree : P ∈ weightedSupportLE (fun _ : σ => 1) h)
    (hsmall : (2 : ℝ) ^ (h + 1) * ε < 1)
    (happrox : ∀ n < N, ‖(g n : ℝ) - aeval (fun _ => (n : ℝ)) P‖ ≤ ε) :
    ∃ Q : MvPolynomial σ ℝ,
      Q ∈ weightedSupportLE (fun _ : σ => 1) h ∧
      (∀ n : ℕ, ∃ z : ℤ, aeval (fun _ => (n : ℝ)) Q = z) ∧
      (∀ n < N, aeval (fun _ => (n : ℝ)) Q = (g n : ℝ)) ∧
      ∀ n < N, ‖aeval (fun _ => (n : ℝ)) Q - aeval (fun _ => (n : ℝ)) P‖ ≤ ε := by
  obtain ⟨Q, hQ, hint, heq, hclose⟩ := exists_integer_polynomial_lift
    (uniqueAlgEquiv ℝ σ P) g (singleParameter_natDegree_le hdegree) hsmall
    (by simpa only [singleParameter_eval] using happrox)
  refine ⟨(uniqueAlgEquiv ℝ σ).symm Q, singleParameter_symm_degree hQ, ?_, ?_, ?_⟩
  · simpa only [singleParameter_symm_eval] using hint
  · simpa only [singleParameter_symm_eval] using heq
  · simpa only [singleParameter_symm_eval, singleParameter_eval] using hclose

end Erdos3

end

end OAI
