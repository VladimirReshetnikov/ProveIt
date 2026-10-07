import OAI.Combinatorics.Progressions.Linear.BoundedAdaptedBasis

namespace OAI

section

namespace Erdos3.IsRealCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L] {d s : ℕ}
  {e : Basis (Fin d) ℝ L} (he : IsRealCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he hnil

theorem bch_remainder_mem_tail (i : ℕ) (a : L) {b : L} (hb : b ∈ realBasisTail e i) :
    lieBCH s a b - (a + b) ∈ realBasisTail e (i + 1) :=
  lieBCH_sub_add_mem hnil (he.tailIdeal (i + 1)) a b (he.lie_mem_tail_succ i a hb)

theorem bch_low_coordinate (i : ℕ) (a : L) {b : L} (hb : b ∈ realBasisTail e i)
    (k : Fin d) (hk : k.val ≤ i) :
    e.repr (lieBCH s a b) k = e.repr a k + e.repr b k := by
  have h := he.bch_remainder_mem_tail hnil i a hb k (Nat.lt_succ_of_le hk)
  rw [map_sub, Finsupp.sub_apply, map_add, Finsupp.add_apply] at h
  exact sub_eq_zero.mp h

theorem peel_mem_tail (j : Fin d) (g : NilpotentLieBCHGroup L s hnil)
    (hg : g.coord ∈ realBasisTail e j.val) :
    (((⟨e.repr g.coord j • e j⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * g).coord) ∈
      realBasisTail e (j.val + 1) := by
  change lieBCH s (-(e.repr g.coord j • e j)) g.coord ∈ _
  have herr := he.bch_remainder_mem_tail hnil j.val (-(e.repr g.coord j • e j)) hg
  have hlin : -(e.repr g.coord j • e j) + g.coord ∈ realBasisTail e (j.val + 1) := by
    simpa only [sub_eq_add_neg, add_comm] using real_sub_coordinate_mem_tail e j hg
  simpa only [sub_add_cancel] using (realBasisTail e (j.val + 1)).add_mem herr hlin

theorem leading_coordinate (j : Fin d) (t : ℝ) (r : NilpotentLieBCHGroup L s hnil)
    (hr : r.coord ∈ realBasisTail e (j.val + 1)) :
    e.repr (((⟨t • e j⟩ : NilpotentLieBCHGroup L s hnil) * r).coord) j = t := by
  change e.repr (lieBCH s (t • e j) r.coord) j = t
  rw [he.bch_low_coordinate hnil j.val (t • e j)
    (realBasisTail_antitone e (Nat.le_succ j.val) hr) j le_rfl]
  simp only [map_smul, Finsupp.smul_apply, Basis.repr_self, Finsupp.single_eq_same,
    smul_eq_mul, mul_one, hr j (Nat.lt_succ_self j.val), add_zero]

end Erdos3.IsRealCentralLieBasis

end

end OAI
