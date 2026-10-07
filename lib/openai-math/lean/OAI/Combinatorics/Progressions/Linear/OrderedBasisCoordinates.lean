import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.TakeDrop
import OAI.Combinatorics.Progressions.Nilpotent.BCHOrderedReduction

namespace OAI

section

namespace Erdos3

open Module

theorem mem_drop_finRange_iff {d i : ℕ} {j : Fin d} :
    j ∈ (List.finRange d).drop i ↔ i ≤ j.val := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨k, hk, heq⟩
    have hval : i + k = j.val := by simpa using congrArg Fin.val heq
    omega
  · intro hij
    refine ⟨j.val - i, ?_, ?_⟩
    · simp only [List.length_finRange]
      omega
    · apply Fin.ext
      simp only [List.getElem_finRange, Fin.val_cast]
      omega

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  (e : Basis (Fin d) ℚ L) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def orderedBasisTailProduct (i : ℕ) (t : Fin d → ℚ) :
    NilpotentLieBCHGroup L s hnil :=
  (((List.finRange d).drop i).map fun j => (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil)).prod

noncomputable def orderedBasisProduct (t : Fin d → ℚ) : NilpotentLieBCHGroup L s hnil :=
  orderedBasisTailProduct e hnil 0 t

theorem orderedBasisTailProduct_terminal {i : ℕ} (hi : d ≤ i) (t : Fin d → ℚ) :
    orderedBasisTailProduct e hnil i t = 1 := by
  simp only [orderedBasisTailProduct,
    List.drop_eq_nil_of_le (as := List.finRange d) (i := i) (by simpa using hi),
    List.map_nil, List.prod_nil]

theorem orderedBasisTailProduct_step (j : Fin d) (t : Fin d → ℚ) :
    orderedBasisTailProduct e hnil j.val t =
      (⟨t j • e j⟩ : NilpotentLieBCHGroup L s hnil) * orderedBasisTailProduct e hnil (j.val + 1) t := by
  unfold orderedBasisTailProduct
  rw [List.drop_eq_getElem_cons (by simp), List.map_cons, List.prod_cons]
  simp only [List.getElem_finRange, Fin.cast_mk, Fin.eta]

theorem orderedBasisTailProduct_congr (i : ℕ) {t u : Fin d → ℚ}
    (h : ∀ j : Fin d, i ≤ j.val → t j = u j) :
    orderedBasisTailProduct e hnil i t = orderedBasisTailProduct e hnil i u := by
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  rw [h j (mem_drop_finRange_iff.mp hj)]

namespace IsCentralLieBasis

variable {e} (he : IsCentralLieBasis e)
include he

theorem orderedBasisTailProduct_mem_tail (i : ℕ) (t : Fin d → ℚ) :
    (orderedBasisTailProduct e hnil i t).coord ∈ basisTail e i := by
  change orderedBasisTailProduct e hnil i t ∈
    NilpotentLieBCHGroup.subgroup (he.tailIdeal i).toLieSubalgebra
  unfold orderedBasisTailProduct
  apply list_prod_mem
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  exact (basisTail e i).smul_mem _ (basis_mem_tail e j (mem_drop_finRange_iff.mp hj))

theorem orderedBasisTailProduct_leading (j : Fin d) (t : Fin d → ℚ) :
    e.repr (orderedBasisTailProduct e hnil j.val t).coord j = t j := by
  rw [orderedBasisTailProduct_step]
  exact he.leading_coordinate hnil j (t j) _ (he.orderedBasisTailProduct_mem_tail hnil _ t)

end IsCentralLieBasis
end Erdos3

end

section

namespace Erdos3.IsCentralLieBasis

open Module

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d s : ℕ}
  {e : Basis (Fin d) ℚ L} (he : IsCentralLieBasis e)
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include he

theorem exists_orderedBasisTailProduct_aux (k i : ℕ) (hik : i + k = d)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ basisTail e i) :
    ∃ t : Fin d → ℚ, orderedBasisTailProduct e hnil i t = g := by
  classical
  induction k generalizing i g with
  | zero =>
      have hi : i = d := by omega
      subst i
      refine ⟨fun _ => 0, ?_⟩
      rw [orderedBasisTailProduct_terminal e hnil le_rfl]
      apply NilpotentLieBCHGroup.ext
      have hz : g.coord = 0 := by
        simpa only [basisTail_terminal, Submodule.mem_bot] using hg
      exact hz.symm
  | succ k ih =>
      have hi : i < d := by omega
      let j : Fin d := ⟨i, hi⟩
      let c : ℚ := e.repr g.coord j
      let a : NilpotentLieBCHGroup L s hnil := ⟨c • e j⟩
      let r := a⁻¹ * g
      have hr : r.coord ∈ basisTail e (i + 1) := he.peel_mem_tail hnil j g hg
      obtain ⟨t, ht⟩ := ih (i + 1) (by omega) r hr
      let u := Function.update t j c
      have huj : u j = c := by simp [u]
      have hu : orderedBasisTailProduct e hnil (i + 1) u =
          orderedBasisTailProduct e hnil (i + 1) t := by
        apply orderedBasisTailProduct_congr
        intro l hl
        have hlj : l ≠ j := by
          intro h
          subst l
          change i + 1 ≤ i at hl
          omega
        exact Function.update_of_ne hlj ..
      refine ⟨u, ?_⟩
      change orderedBasisTailProduct e hnil j.val u = g
      rw [orderedBasisTailProduct_step, huj]
      change a * orderedBasisTailProduct e hnil (i + 1) u = g
      rw [hu, ht]
      exact mul_inv_cancel_left a g

theorem exists_orderedBasisTailProduct {i : ℕ} (hi : i ≤ d)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ basisTail e i) :
    ∃ t : Fin d → ℚ, orderedBasisTailProduct e hnil i t = g :=
  he.exists_orderedBasisTailProduct_aux hnil (d - i) i (Nat.add_sub_of_le hi) g hg

theorem orderedBasisProduct_surjective : Function.Surjective (orderedBasisProduct e hnil) := by
  intro g
  exact he.exists_orderedBasisTailProduct hnil (Nat.zero_le d) g (by simp [basisTail_zero])

theorem orderedBasisTailProduct_eq_of_product_eq {t u : Fin d → ℚ}
    (h : orderedBasisProduct e hnil t = orderedBasisProduct e hnil u)
    (i : ℕ) (hi : i ≤ d) :
    orderedBasisTailProduct e hnil i t = orderedBasisTailProduct e hnil i u := by
  induction i with
  | zero => exact h
  | succ i ih =>
      have hid : i < d := by omega
      let j : Fin d := ⟨i, hid⟩
      have ht := ih (by omega)
      change orderedBasisTailProduct e hnil j.val t =
        orderedBasisTailProduct e hnil j.val u at ht
      have hc : t j = u j := by
        have hc := congrArg (fun g => e.repr g.coord j) ht
        simpa only [he.orderedBasisTailProduct_leading hnil j] using hc
      rw [orderedBasisTailProduct_step, orderedBasisTailProduct_step, hc] at ht
      exact mul_left_cancel ht

theorem orderedBasisProduct_injective : Function.Injective (orderedBasisProduct e hnil) := by
  intro t u h
  funext j
  have ht := he.orderedBasisTailProduct_eq_of_product_eq hnil h j.val (Nat.le_of_lt j.isLt)
  have hc := congrArg (fun g => e.repr g.coord j) ht
  simpa only [he.orderedBasisTailProduct_leading hnil j] using hc

noncomputable def orderedBasisEquiv : (Fin d → ℚ) ≃ NilpotentLieBCHGroup L s hnil :=
  Equiv.ofBijective (orderedBasisProduct e hnil)
    ⟨he.orderedBasisProduct_injective hnil, he.orderedBasisProduct_surjective hnil⟩

theorem orderedBasisEquiv_apply (t : Fin d → ℚ) :
    he.orderedBasisEquiv hnil t = orderedBasisProduct e hnil t := rfl

theorem orderedBasisProduct_coordinates (g : NilpotentLieBCHGroup L s hnil) :
    orderedBasisProduct e hnil ((he.orderedBasisEquiv hnil).symm g) = g :=
  (he.orderedBasisEquiv hnil).apply_symm_apply g

end Erdos3.IsCentralLieBasis

end

end OAI
