import Surreal.Algebra.RealPolynomialFactors
import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# Coprime residue factors over an arbitrary real closed field

This generalizes the residue-polynomial step of Conway's odd-degree root
argument from the ordinary real field to any ordered real closed field.
The root-multiplicity splitting itself only needs a coefficient field and
an existing root. Mathlib supplies odd-degree roots over a real closed field;
the existing depressed-polynomial lemma excludes a pure linear power.

These are finite polynomial statements. A Hahn or surreal root theorem
still needs its normalization, factor lifting, and degree induction.
-/

namespace Surreal.FinitePolynomial

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- Extracting the full multiplicity of a root gives two positive-degree,
coprime monic factors when the polynomial is not a power of one linear factor.
This step does not require an order or any closedness of the field. -/
theorem exists_coprime_monic_factors {P : K[X]} (hP : P.Monic)
    (hroot : ∃ a : K, P.IsRoot a)
    (hne : ∀ a : K, P ≠ (X - C a) ^ P.natDegree) :
    ∃ f g : K[X], P = f * g ∧ f.Monic ∧ g.Monic ∧ IsCoprime f g ∧
      0 < f.natDegree ∧ 0 < g.natDegree := by
  obtain ⟨a, ha⟩ := hroot
  obtain ⟨g, heq, hnot⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP.ne_zero a
  let f : K[X] := (X - C a) ^ P.rootMultiplicity a
  have hf : f.Monic := (monic_X_sub_C a).pow _
  have hfg : P = f * g := heq
  have hg : g.Monic := hf.of_mul_monic_left (hfg ▸ hP)
  have hfdeg : f.natDegree = P.rootMultiplicity a := by
    simp only [f, natDegree_pow, natDegree_X_sub_C, mul_one]
  have hfpos : 0 < f.natDegree := hfdeg ▸ (rootMultiplicity_pos hP.ne_zero).mpr ha
  have hgpos : 0 < g.natDegree := by
    by_contra h
    have hgdeg : g.natDegree = 0 := by omega
    have hg1 : g = 1 := eq_one_of_monic_natDegree_zero hg hgdeg
    have hPf : P = f := by simpa only [hg1, mul_one] using hfg
    have hdeg : P.natDegree = P.rootMultiplicity a := (congrArg natDegree hPf).trans hfdeg
    exact hne a (by simpa only [hdeg] using hPf)
  have hcop : IsCoprime f g :=
    ((irreducible_X_sub_C a).coprime_iff_not_dvd.mpr hnot).pow_left
  exact ⟨f, g, hfg, hf, hg, hcop, hfpos, hgpos⟩

/-- If the polynomial has odd degree, one of its proper coprime factors has
positive odd degree. The existence of a root is explicit in this field-level lemma. -/
theorem exists_odd_coprime_monic_factors_of_root {P : K[X]} (hP : P.Monic)
    (hodd : Odd P.natDegree) (hroot : ∃ a : K, P.IsRoot a)
    (hne : ∀ a : K, P ≠ (X - C a) ^ P.natDegree) :
    ∃ f g : K[X], P = f * g ∧ f.Monic ∧ g.Monic ∧ IsCoprime f g ∧
      Odd f.natDegree ∧ 0 < f.natDegree ∧ f.natDegree < P.natDegree ∧
      0 < g.natDegree := by
  obtain ⟨f, g, heq, hf, hg, hcop, hfpos, hgpos⟩ :=
    exists_coprime_monic_factors hP hroot hne
  have hdeg : P.natDegree = f.natDegree + g.natDegree := by
    rw [heq, natDegree_mul hf.ne_zero hg.ne_zero]
  by_cases hfodd : Odd f.natDegree
  · exact ⟨f, g, heq, hf, hg, hcop, hfodd, hfpos, by omega, hgpos⟩
  · have hgodd : Odd g.natDegree := by
      rw [hdeg, Nat.odd_add] at hodd
      exact Nat.not_even_iff_odd.mp (fun heven => hfodd (hodd.mpr heven))
    exact ⟨g, f, heq.trans (mul_comm _ _), hg, hf, hcop.symm,
      hgodd, hgpos, by omega, hfpos⟩

/-- A nontrivial depressed odd-degree monic polynomial over an ordered real
closed field has the proper odd-degree coprime factor needed for induction. -/
theorem realClosed_depressed_odd_coprime_factorization
    [LinearOrder K] [IsStrictOrderedRing K] [IsRealClosed K]
    {P : K[X]} (hP : P.Monic) (hodd : Odd P.natDegree)
    (hdep : P.coeff (P.natDegree - 1) = 0) (hne : P ≠ X ^ P.natDegree) :
    ∃ f g : K[X], P = f * g ∧ f.Monic ∧ g.Monic ∧ IsCoprime f g ∧
      Odd f.natDegree ∧ 0 < f.natDegree ∧ f.natDegree < P.natDegree ∧
      0 < g.natDegree :=
  exists_odd_coprime_monic_factors_of_root hP hodd
    (IsRealClosed.exists_isRoot_of_odd_natDegree hodd)
    (depressed_ne_linear_pow hodd.pos hdep hne)

end

end Surreal.FinitePolynomial
