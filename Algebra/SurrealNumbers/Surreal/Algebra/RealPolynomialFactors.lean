import Mathlib.Analysis.Polynomial.Order
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Coprime factors of a depressed odd-degree real polynomial

This is the ordinary-real residue-polynomial prerequisite for the odd-degree
root argument of Conway, *On Numbers and Games*, Chapter 3, Theorem 25,
relevant to `found:sub:realclosed` in the foundations article. A monic,
depressed polynomial other than `X^n` is not a power of one linear factor.
For an odd-degree real polynomial, extracting the full multiplicity of any
real root then gives two coprime monic factors of positive degree. One factor
has odd degree and is suitable for induction on degree.

Only the intermediate value properties of ordinary real polynomials are used.
No real-closedness or factor-lifting assertion about the surreal field is made.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

/-- A positive-degree depressed polynomial other than `X^n` cannot be a pure
power of a linear factor. This finite algebraic observation only needs
characteristic zero. -/
theorem depressed_ne_linear_pow {K : Type*} [Field K] [CharZero K]
    {P : K[X]} (hpos : 0 < P.natDegree)
    (hdep : P.coeff (P.natDegree - 1) = 0)
    (hne : P ≠ X ^ P.natDegree) (a : K) :
    P ≠ (X - C a) ^ P.natDegree := by
  intro heq
  have hnext : P.nextCoeff = 0 := by
    simp only [nextCoeff, if_neg hpos.ne', hdep]
  have h := congrArg nextCoeff heq
  rw [hnext, (monic_X_sub_C a).nextCoeff_pow, nextCoeff_X_sub_C,
    nsmul_eq_mul] at h
  have ha : a = 0 := by
    have hn : (P.natDegree : K) ≠ 0 := Nat.cast_ne_zero.mpr hpos.ne'
    exact neg_eq_zero.mp ((mul_eq_zero.mp h.symm).resolve_left hn)
  apply hne
  simpa only [ha, C_0, sub_zero] using heq

/-- An odd-degree monic real polynomial has a real root. The proof uses
Mathlib's polynomial sign consequences of the intermediate value theorem. -/
theorem real_monic_odd_exists_root {P : ℝ[X]} (hP : P.Monic)
    (hodd : Odd P.natDegree) : ∃ a : ℝ, P.IsRoot a := by
  by_contra h
  have hn : ∀ a : ℝ, ¬ P.IsRoot a := by simpa only [not_exists] using h
  have hp : 0 < P.eval 0 := zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun a ha => (hn a ha).elim) (by simp [hP.leadingCoeff])
  have hm := zero_lt_negOnePow_mul_eval_of_lt_roots_of_leadingCoeff_nonneg
    (P := P) (x := 0) (fun a ha => (hn a ha).elim) (by simp [hP.leadingCoeff])
  have hi : Odd (P.natDegree : ℤ) := by exact_mod_cast hodd
  rw [Int.negOnePow_odd _ hi] at hm
  norm_num at hm
  exact (not_lt_of_ge hp.le) hm

/-- Removing the full multiplicity of a real root produces two coprime,
positive-degree monic factors, provided the polynomial is not a pure power
of a linear factor. -/
theorem real_exists_coprime_monic_factors {P : ℝ[X]} (hP : P.Monic)
    (hroot : ∃ a : ℝ, P.IsRoot a)
    (hne : ∀ a : ℝ, P ≠ (X - C a) ^ P.natDegree) :
    ∃ f g : ℝ[X], P = f * g ∧ f.Monic ∧ g.Monic ∧ IsCoprime f g ∧
      0 < f.natDegree ∧ 0 < g.natDegree := by
  obtain ⟨a, ha⟩ := hroot
  obtain ⟨g, heq, hnot⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP.ne_zero a
  let f : ℝ[X] := (X - C a) ^ P.rootMultiplicity a
  have hf : f.Monic := (monic_X_sub_C a).pow _
  have hfg : P = f * g := heq
  have hg : g.Monic := hf.of_mul_monic_left (hfg ▸ hP)
  have hfdeg : f.natDegree = P.rootMultiplicity a := by
    simp only [f, natDegree_pow, natDegree_X_sub_C, mul_one]
  have hfpos : 0 < f.natDegree := hfdeg ▸ (rootMultiplicity_pos hP.ne_zero).mpr ha
  have hgpos : 0 < g.natDegree := by
    by_contra h
    have hgdeg : g.natDegree = 0 := by omega
    have hg1 : g = 1 := by
      have hc : g.coeff 0 = 1 := by simpa only [leadingCoeff, hgdeg] using hg.leadingCoeff
      rw [eq_C_of_natDegree_eq_zero hgdeg, hc, C_1]
    have hPf : P = f := by simpa only [hg1, mul_one] using hfg
    have hdeg : P.natDegree = P.rootMultiplicity a := (congrArg natDegree hPf).trans hfdeg
    exact hne a (by simpa only [hdeg] using hPf)
  have hcop : IsCoprime f g :=
    ((irreducible_X_sub_C a).coprime_iff_not_dvd.mpr hnot).pow_left
  exact ⟨f, g, hfg, hf, hg, hcop, hfpos, hgpos⟩

/-- The ordinary residue-polynomial factorization needed for induction in the
odd-degree-root argument: the first factor has positive odd degree strictly
below that of `P`, and the second factor also has positive degree. -/
theorem real_depressed_odd_coprime_factorization {P : ℝ[X]} (hP : P.Monic)
    (hodd : Odd P.natDegree) (hdep : P.coeff (P.natDegree - 1) = 0)
    (hne : P ≠ X ^ P.natDegree) :
    ∃ f g : ℝ[X], P = f * g ∧ f.Monic ∧ g.Monic ∧ IsCoprime f g ∧
      Odd f.natDegree ∧ 0 < f.natDegree ∧ f.natDegree < P.natDegree ∧
      0 < g.natDegree := by
  have hpos : 0 < P.natDegree := hodd.pos
  obtain ⟨f, g, heq, hf, hg, hcop, hfpos, hgpos⟩ :=
    real_exists_coprime_monic_factors hP (real_monic_odd_exists_root hP hodd)
      (depressed_ne_linear_pow hpos hdep hne)
  have hdeg : P.natDegree = f.natDegree + g.natDegree := by
    rw [heq, natDegree_mul hf.ne_zero hg.ne_zero]
  by_cases hfodd : Odd f.natDegree
  · exact ⟨f, g, heq, hf, hg, hcop, hfodd, hfpos, by omega, hgpos⟩
  · have hgodd : Odd g.natDegree := by
      rw [hdeg, Nat.odd_add] at hodd
      exact Nat.not_even_iff_odd.mp (fun heven => hfodd (hodd.mpr heven))
    exact ⟨g, f, heq.trans (mul_comm _ _), hg, hf, hcop.symm,
      hgodd, hgpos, by omega, hfpos⟩

end

end Surreal.FinitePolynomial
