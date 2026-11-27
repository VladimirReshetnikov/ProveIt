import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Monomial
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Minimum support of a polynomial annihilator

This file formalizes the algebraic definition of support size in the article's
singular-moduli section, its minimal-polynomial upper bound, and the equivalent
criterion in terms of linear independence of powers.
-/

namespace GRHArticle.SingularModuli

open Polynomial
open scoped BigOperators

variable {K L M : Type*} [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]

/-- The element has a nonzero polynomial annihilator with at most `t` terms. -/
def HasSparseAnnihilator (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
    (x : L) (t : ℕ) : Prop :=
  ∃ p : K[X], p ≠ 0 ∧ p.support.card ≤ t ∧ aeval x p = 0

theorem HasSparseAnnihilator.mono {x : L} {s t : ℕ}
    (h : HasSparseAnnihilator K x s) (hst : s ≤ t) : HasSparseAnnihilator K x t := by
  obtain ⟨p, hp, hsize, hzero⟩ := h
  exact ⟨p, hp, hsize.trans hst, hzero⟩

/-- The support bound in equation `smd:eq:trivial`. -/
theorem hasSparseAnnihilator_natDegree_add_one {x : L} (hx : IsIntegral K x) :
    HasSparseAnnihilator K x ((minpoly K x).natDegree + 1) := by
  refine ⟨minpoly K x, minpoly.ne_zero hx, ?_, minpoly.aeval K x⟩
  simpa using Finset.card_le_card (supp_subset_range_natDegree_succ (p := minpoly K x))

theorem hasSparseAnnihilator_iff_dvd_minpoly (x : L) (t : ℕ) :
    HasSparseAnnihilator K x t ↔
      ∃ p : K[X], p ≠ 0 ∧ p.support.card ≤ t ∧ minpoly K x ∣ p := by
  simp only [HasSparseAnnihilator, minpoly.dvd_iff]

/-- The least support size of a nonzero annihilator of an algebraic element. -/
noncomputable def minimumSupport {x : L} (hx : IsIntegral K x) : ℕ := by
  classical
  exact Nat.find ⟨_, hasSparseAnnihilator_natDegree_add_one hx⟩

theorem hasSparseAnnihilator_minimumSupport {x : L} (hx : IsIntegral K x) :
    HasSparseAnnihilator K x (minimumSupport hx) := by
  classical
  exact Nat.find_spec ⟨_, hasSparseAnnihilator_natDegree_add_one hx⟩

theorem minimumSupport_le_iff {x : L} (hx : IsIntegral K x) (t : ℕ) :
    minimumSupport hx ≤ t ↔ HasSparseAnnihilator K x t := by
  classical
  constructor
  · exact (hasSparseAnnihilator_minimumSupport hx).mono
  · exact Nat.find_min' ⟨_, hasSparseAnnihilator_natDegree_add_one hx⟩

theorem minimumSupport_le_natDegree_add_one {x : L} (hx : IsIntegral K x) :
    minimumSupport hx ≤ (minpoly K x).natDegree + 1 :=
  (minimumSupport_le_iff hx _).2 (hasSparseAnnihilator_natDegree_add_one hx)

theorem minimumSupport_pos {x : L} (hx : IsIntegral K x) : 0 < minimumSupport hx := by
  obtain ⟨p, hp, hsize, _⟩ := hasSparseAnnihilator_minimumSupport hx
  exact (Finset.card_pos.mpr (support_nonempty.mpr hp)).trans_le hsize

/-- An algebra embedding preserves the exact set of attainable support bounds. -/
theorem hasSparseAnnihilator_algHom_iff (f : L →ₐ[K] M) (x : L) (t : ℕ) :
    HasSparseAnnihilator K (f x) t ↔ HasSparseAnnihilator K x t := by
  constructor
  · rintro ⟨p, hp, hsize, hzero⟩
    refine ⟨p, hp, hsize, f.injective ?_⟩
    change f (aeval x p) = f 0
    rw [← aeval_algHom_apply f, hzero, map_zero]
  · rintro ⟨p, hp, hsize, hzero⟩
    exact ⟨p, hp, hsize, by simp [aeval_algHom_apply, hzero]⟩

theorem hasSparseAnnihilator_one_iff (x : L) :
    HasSparseAnnihilator K x 1 ↔ x = 0 := by
  constructor
  · rintro ⟨p, hp, hsize, hzero⟩
    obtain ⟨n, a, rfl⟩ := card_support_le_one_iff_monomial.mp hsize
    rw [aeval_monomial, mul_eq_zero] at hzero
    rcases hzero with ha | hn
    · have ha' : a = 0 := (algebraMap K L).injective (ha.trans (map_zero _).symm)
      simp [ha'] at hp
    · by_contra hx
      exact pow_ne_zero _ hx hn
  · rintro rfl
    exact ⟨X, X_ne_zero, by simp, by simp⟩

/-- The only element with a one-term annihilator is zero. -/
theorem minimumSupport_eq_one_iff {x : L} (hx : IsIntegral K x) :
    minimumSupport hx = 1 ↔ x = 0 := by
  rw [← hasSparseAnnihilator_one_iff (K := K) x, ← minimumSupport_le_iff hx]
  have hpos := minimumSupport_pos hx
  omega

/-- The nonzero degree-one case of the article's exact support formula. -/
theorem minimumSupport_eq_two_of_natDegree_one {x : L} (hx : IsIntegral K x)
    (hdegree : (minpoly K x).natDegree = 1) (hzero : x ≠ 0) :
    minimumSupport hx = 2 := by
  have hupper : minimumSupport hx ≤ 2 := by
    simpa [hdegree] using minimumSupport_le_natDegree_add_one hx
  have hlower : ¬ minimumSupport hx ≤ 1 := by
    intro h
    exact hzero ((hasSparseAnnihilator_one_iff x).1 ((minimumSupport_le_iff hx 1).1 h))
  omega

/-- The powers with exponents in `s` are independent exactly when no nonzero
polynomial supported in `s` vanishes at the element. -/
theorem linearIndepOn_powers_iff (x : L) (s : Finset ℕ) :
    LinearIndepOn K (fun n : ℕ ↦ x ^ n) (s : Set ℕ) ↔
      ∀ p : K[X], p.support ⊆ s → aeval x p = 0 → p = 0 := by
  classical
  rw [linearIndepOn_finset_iff]
  constructor
  · intro hind p hs hp
    have hsum : ∑ n ∈ s, p.coeff n • x ^ n = 0 := by
      rw [← Finset.sum_subset hs]
      · simpa only [aeval_def, eval₂_eq_sum, Polynomial.sum, Algebra.smul_def] using hp
      · intro n _ hn
        have hz : p.coeff n = 0 := by simpa only [mem_support_iff, not_not] using hn
        rw [hz, zero_smul]
    have hcoeff (n : ℕ) : p.coeff n = 0 := by
      by_cases hn : n ∈ s
      · exact hind p.coeff hsum n hn
      · exact not_ne_iff.mp fun hc ↦ hn (hs (mem_support_iff.mpr hc))
    exact Polynomial.ext fun n ↦ by simpa using hcoeff n
  · intro h c hsum n hn
    let p : K[X] := ∑ i ∈ s, monomial i (c i)
    have hcoeff (i : ℕ) : p.coeff i = if i ∈ s then c i else 0 := by
      simp [p, coeff_monomial]
    have hs : p.support ⊆ s := by
      intro i hi
      by_contra hni
      exact (mem_support_iff.mp hi) (by simp [hcoeff, hni])
    have hzero : aeval x p = 0 := by
      simpa only [p, map_sum, aeval_monomial, ← Algebra.smul_def] using hsum
    have hp : p = 0 := h p hs hzero
    simpa [hp, hn] using (hcoeff n).symm

/-- A sparsity obstruction is equivalent to independence for every allowed
finite set of exponents, with no bound on the exponents themselves. -/
theorem not_hasSparseAnnihilator_iff (x : L) (t : ℕ) :
    ¬ HasSparseAnnihilator K x t ↔
      ∀ s : Finset ℕ, s.card ≤ t → LinearIndepOn K (fun n : ℕ ↦ x ^ n) (s : Set ℕ) := by
  classical
  constructor
  · intro h s hs
    rw [linearIndepOn_powers_iff]
    intro p hsubset hzero
    by_contra hp
    exact h ⟨p, hp, (Finset.card_le_card hsubset).trans hs, hzero⟩
  · rintro h ⟨p, hp, hsize, hzero⟩
    exact hp ((linearIndepOn_powers_iff x p.support).1 (h p.support hsize) p
      (fun _ hn ↦ hn) hzero)

/-- The criterion for attaining the minimal-polynomial upper bound. -/
theorem minimumSupport_eq_natDegree_add_one_iff {x : L} (hx : IsIntegral K x) :
    minimumSupport hx = (minpoly K x).natDegree + 1 ↔
      ∀ s : Finset ℕ, s.card ≤ (minpoly K x).natDegree →
        LinearIndepOn K (fun n : ℕ ↦ x ^ n) (s : Set ℕ) := by
  rw [← not_hasSparseAnnihilator_iff, ← minimumSupport_le_iff hx]
  have hupper := minimumSupport_le_natDegree_add_one hx
  omega

end GRHArticle.SingularModuli
