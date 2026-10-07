import OAI.Combinatorics.Progressions.Estimates.PowerIndexFromOrderedGenerators
import OAI.Combinatorics.Progressions.Nilpotent.RealBCHOrderedReduction

namespace OAI

section

namespace Erdos3

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {d s : ℕ}
  (e : Basis (Fin d) ℝ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realOrderedBasisTailProduct (i : ℕ) (t : Fin d → ℝ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).drop i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

noncomputable def realOrderedBasisProduct (t : Fin d → ℝ) : NilpotentLieBCHGroup L s hnil :=
  realOrderedBasisTailProduct e hnil 0 t

theorem realOrderedBasisTailProduct_terminal {i : ℕ} (hi : d ≤ i) (t : Fin d → ℝ) :
    realOrderedBasisTailProduct e hnil i t = 1 := by
  simp only [realOrderedBasisTailProduct,
    List.drop_eq_nil_of_le (as := List.finRange d) (i := i) (by simpa using hi),
    List.map_nil, List.prod_nil]

theorem realOrderedBasisTailProduct_step (j : Fin d) (t : Fin d → ℝ) :
    realOrderedBasisTailProduct e hnil j.val t =
      (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil) * realOrderedBasisTailProduct e hnil (j.val + 1) t := by
  unfold realOrderedBasisTailProduct
  rw [List.drop_eq_getElem_cons (by simp), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem realOrderedBasisTailProduct_congr (i : ℕ) {t u : Fin d → ℝ}
    (h : ∀ j : Fin d, i ≤ j.val → t j = u j) :
    realOrderedBasisTailProduct e hnil i t = realOrderedBasisTailProduct e hnil i u := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  rw [h j (mem_drop_finRange_iff.mp hj)]

noncomputable def realOrderedBasisPrefixProduct (i : ℕ) (t : Fin d → ℝ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).take i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

theorem realOrderedBasisProduct_eq_prefix_mul_tail (i : ℕ) (t : Fin d → ℝ) :
    realOrderedBasisProduct e hnil t =
      realOrderedBasisPrefixProduct e hnil i t * realOrderedBasisTailProduct e hnil i t := by
  unfold realOrderedBasisProduct realOrderedBasisPrefixProduct realOrderedBasisTailProduct
  rw [List.drop_zero, ← List.prod_append, ← List.map_append, List.take_append_drop]

theorem realOrderedBasisPrefixProduct_congr (i : ℕ) {t u : Fin d → ℝ}
    (h : ∀ j : Fin d, j.val < i → t j = u j) :
    realOrderedBasisPrefixProduct e hnil i t = realOrderedBasisPrefixProduct e hnil i u := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  obtain ⟨k, hk, hkj⟩ := List.mem_take_iff_getElem.mp hj
  have hval : k = j.val := by simpa using congrArg Fin.val hkj
  rw [h j (by omega)]

variable [IsScalarTower ℚ ℝ L]

namespace IsRealCentralLieBasis

variable {e} (he : IsRealCentralLieBasis e)
include he

theorem realOrderedBasisTailProduct_mem_tail (i : ℕ) (t : Fin d → ℝ) :
    (realOrderedBasisTailProduct e hnil i t).coord ∈ realBasisTail e i := by
  change realOrderedBasisTailProduct e hnil i t ∈
    NilpotentLieBCHGroup.subgroup (he.tailIdeal i).toLieSubalgebra
  unfold realOrderedBasisTailProduct
  apply list_prod_mem
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  exact (realBasisTail e i).smul_mem _ (real_basis_mem_tail e j (mem_drop_finRange_iff.mp hj))

theorem realOrderedBasisTailProduct_leading (j : Fin d) (t : Fin d → ℝ) :
    e.repr (realOrderedBasisTailProduct e hnil j.val t).coord j = t j := by
  rw [realOrderedBasisTailProduct_step]
  exact he.leading_coordinate hnil j (t j) _ (he.realOrderedBasisTailProduct_mem_tail hnil _ t)

theorem mul_tail_coordinate (a b : NilpotentLieBCHGroup L s hnil) (j : Fin d)
    (hb : b.coord ∈ realBasisTail e (j.val + 1)) :
    e.repr (a * b).coord j = e.repr a.coord j := by
  change e.repr (lieBCH s a.coord b.coord) j = _
  rw [he.bch_low_coordinate hnil (j.val + 1) a.coord hb j (Nat.le_succ _),
    hb j (Nat.lt_succ_self _), add_zero]

theorem mul_basis_coordinate (a : NilpotentLieBCHGroup L s hnil) (j : Fin d) (t : ℝ) :
    e.repr (a * (⟨t • e j⟩ : NilpotentLieBCHGroup L s hnil)).coord j =
      e.repr a.coord j + t := by
  change e.repr (lieBCH s a.coord (t • e j)) j = _
  rw [he.bch_low_coordinate hnil j.val a.coord
    ((realBasisTail e j.val).smul_mem t (real_basis_mem_tail e j le_rfl)) j le_rfl]
  simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one]

theorem mul_realOrderedBasisProduct_coordinate (a : NilpotentLieBCHGroup L s hnil)
    (t : Fin d → ℝ) (j : Fin d) :
    e.repr (a * realOrderedBasisProduct e hnil t).coord j =
      e.repr (a * realOrderedBasisPrefixProduct e hnil j.val t).coord j + t j := by
  calc
    _ = e.repr (((a * realOrderedBasisPrefixProduct e hnil j.val t) *
        (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)) *
        realOrderedBasisTailProduct e hnil (j.val + 1) t).coord j := by
      rw [realOrderedBasisProduct_eq_prefix_mul_tail e hnil j.val,
        realOrderedBasisTailProduct_step]
      simp only [mul_assoc]
    _ = e.repr ((a * realOrderedBasisPrefixProduct e hnil j.val t) *
        (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).coord j :=
      he.mul_tail_coordinate hnil _ _ j (he.realOrderedBasisTailProduct_mem_tail hnil _ t)
    _ = _ := he.mul_basis_coordinate hnil _ j (t j)

end IsRealCentralLieBasis
end Erdos3

end

end OAI
