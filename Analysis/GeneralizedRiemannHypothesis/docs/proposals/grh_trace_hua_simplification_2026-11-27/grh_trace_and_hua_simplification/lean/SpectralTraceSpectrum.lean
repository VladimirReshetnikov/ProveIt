import SpectralTraceCore
import Mathlib.LinearAlgebra.Charpoly.Basic

/-!
# A dimension bound for the common spectral polynomial

This file supplies the remaining finite interpolation bookkeeping.  It does
not prove the line-relation spectral trace certificate.
-/

noncomputable section

open Polynomial LinearMap Module

namespace SpectralTraceCore

lemma zero_not_mem_charpoly_roots_of_det_ne_zero
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    (T : End K V) (hT : T.det ≠ 0) : 0 ∉ T.charpoly.roots := by
  intro hroot
  have hroot0 := (isRoot_of_mem_roots hroot).eq_zero
  have hdet : ((-1 : K) • T).det ≠ 0 := by
    rw [det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hT
  exact hdet (by simpa [T.eval_charpoly] using hroot0)

lemma card_distinct_charpoly_roots_le
    {K V : Type*} [Field K] [DecidableEq K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (T : End K V) : T.charpoly.roots.toFinset.card ≤ finrank K V := by
  classical
  calc T.charpoly.roots.toFinset.card ≤ T.charpoly.roots.card :=
      Multiset.toFinset_card_le _
    _ ≤ T.charpoly.natDegree := card_roots' _
    _ = finrank K V := T.charpoly_natDegree

/-- A common polynomial at the roots of two invertible endomorphisms can have
zero constant term and degree at most the sum of the dimensions.  The statement
works over any field; over the complex numbers these roots are all eigenvalues. -/
theorem exists_common_root_interpolant
    {K V V' : Type*} [Field K]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    [AddCommGroup V'] [Module K V'] [Module.Finite K V']
    (T : End K V) (T' : End K V') (hT : T.det ≠ 0) (hT' : T'.det ≠ 0)
    (f : K → K) :
    ∃ p : K[X], p.coeff 0 = 0 ∧ p.natDegree ≤ finrank K V + finrank K V' ∧
      ∀ z : K, T.charpoly.IsRoot z ∨ T'.charpoly.IsRoot z → p.eval z = f z := by
  classical
  let S : Finset K := T.charpoly.roots.toFinset ∪ T'.charpoly.roots.toFinset
  have hS0 : (0 : K) ∉ S := by
    simpa [S] using And.intro (zero_not_mem_charpoly_roots_of_det_ne_zero T hT)
      (zero_not_mem_charpoly_roots_of_det_ne_zero T' hT')
  have hScard : S.card ≤ finrank K V + finrank K V' :=
    (Finset.card_union_le _ _).trans
      (Nat.add_le_add (card_distinct_charpoly_roots_le T) (card_distinct_charpoly_roots_le T'))
  obtain ⟨p, hp0, hpdegree, hpvalues⟩ := exists_interpolant_zero_constant S hS0 f
  refine ⟨p, hp0, hpdegree.trans hScard, fun z hz ↦ hpvalues z ?_⟩
  rcases hz with hz | hz
  · exact Finset.mem_union_left _ (Multiset.mem_toFinset.mpr
      ((mem_roots T.charpoly_monic.ne_zero).mpr hz))
  · exact Finset.mem_union_right _ (Multiset.mem_toFinset.mpr
      ((mem_roots T'.charpoly_monic.ne_zero).mpr hz))

#print axioms exists_common_root_interpolant

end SpectralTraceCore
