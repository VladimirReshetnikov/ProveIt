import GowersSzemeredi.Section05
import Mathlib.GroupTheory.OrderOfElement

/-!
# Modular-progression normalization in Gowers's Section 5

This module proves Lemma 5.12.  The catalogue's notion of a proper modular
progression only asks that its parametrization have no repetitions.  Hence an
arbitrary finite initial orbit can first be shortened to the cardinality of
its carrier; the resulting progression has the same carrier and is proper.
-/

set_option autoImplicit false

noncomputable section

open scoped ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private def modAPOrbit {N : Nat} (P : ModAP N) (i : Nat) : ZMod N :=
  P.start + (i : ZMod N) * P.step

private lemma modAP_carrier_eq_image_range {N : Nat} (P : ModAP N) :
    P.carrier = (Finset.range P.length).image (modAPOrbit P) := by
  classical
  ext x
  unfold ModAP.carrier modAPOrbit
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_range]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

private lemma modAPOrbit_mod_order {N : Nat} [NeZero N] (P : ModAP N) (i : Nat) :
    modAPOrbit P (i % addOrderOf P.step) = modAPOrbit P i := by
  unfold modAPOrbit
  congr 1
  simpa only [nsmul_eq_mul] using
    mod_addOrderOf_nsmul P.step i

private lemma modAPOrbit_injOn_order {N : Nat} [NeZero N] (P : ModAP N) :
    Set.InjOn (modAPOrbit P) (Set.Iio (addOrderOf P.step)) := by
  intro i hi j hj hij
  have hmul : (i : ZMod N) * P.step = (j : ZMod N) * P.step := by
    exact add_left_cancel hij
  have hnsmul : i • P.step = j • P.step := by
    simpa only [nsmul_eq_mul] using hmul
  have hmod := ((isOfFinAddOrder_of_finite P.step).nsmul_inj_mod).mp hnsmul
  simpa only [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hmod

private lemma modAP_carrier_eq_order_range_of_le {N : Nat} [NeZero N]
    (P : ModAP N) (horder : addOrderOf P.step ≤ P.length) :
    P.carrier = (Finset.range (addOrderOf P.step)).image (modAPOrbit P) := by
  classical
  rw [modAP_carrier_eq_image_range]
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨i % addOrderOf P.step, ?_, modAPOrbit_mod_order P i⟩
    exact Finset.mem_range.mpr (Nat.mod_lt _ (addOrderOf_pos P.step))
  · intro x hx
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨i, hi, rfl⟩ := hx
    exact ⟨i, Finset.range_mono horder hi, rfl⟩

private lemma modAP_carrier_card {N : Nat} [NeZero N] (P : ModAP N) :
    P.carrier.card = min P.length (addOrderOf P.step) := by
  classical
  by_cases hlength : P.length ≤ addOrderOf P.step
  · have hinj : Set.InjOn (modAPOrbit P) (Finset.range P.length : Set Nat) := by
      intro i hi j hj hij
      apply modAPOrbit_injOn_order P
      · exact lt_of_lt_of_le (Finset.mem_range.mp hi) hlength
      · exact lt_of_lt_of_le (Finset.mem_range.mp hj) hlength
      · exact hij
    rw [min_eq_left hlength, modAP_carrier_eq_image_range,
      Finset.card_image_iff.mpr hinj, Finset.card_range]
  · have horder : addOrderOf P.step ≤ P.length := Nat.le_of_lt (Nat.lt_of_not_ge hlength)
    have hinj : Set.InjOn (modAPOrbit P)
        (Finset.range (addOrderOf P.step) : Set Nat) := by
      intro i hi j hj hij
      exact modAPOrbit_injOn_order P (Finset.mem_range.mp hi)
        (Finset.mem_range.mp hj) hij
    rw [min_eq_right horder, modAP_carrier_eq_order_range_of_le P horder,
      Finset.card_image_iff.mpr hinj, Finset.card_range]

private def normalizedModAP {N : Nat} (P : ModAP N) : ModAP N :=
  { P with length := P.carrier.card }

private lemma normalizedModAP_carrier {N : Nat} [NeZero N] (P : ModAP N) :
    (normalizedModAP P).carrier = P.carrier := by
  classical
  let t := addOrderOf P.step
  have hcard := modAP_carrier_card P
  by_cases hlength : P.length ≤ t
  · have heq : P.carrier.card = P.length := by
      simpa only [t, min_eq_left hlength] using hcard
    simp only [normalizedModAP, heq]
  · have horder : t ≤ P.length := Nat.le_of_lt (Nat.lt_of_not_ge hlength)
    have heq : P.carrier.card = t := by
      simpa only [t, min_eq_right horder] using hcard
    rw [modAP_carrier_eq_order_range_of_le P horder]
    change ({ P with length := P.carrier.card } : ModAP N).carrier = _
    rw [modAP_carrier_eq_image_range, heq]
    rfl

private lemma normalizedModAP_isProper {N : Nat} [NeZero N] (P : ModAP N) :
    (normalizedModAP P).IsProper := by
  rw [ModAP.IsProper, normalizedModAP_carrier]
  rfl

/-- Gowers's Lemma 5.12 under the catalogue's carrier-based notion of
properness. -/
theorem lemma_5_12_holds : lemma_5_12 := by
  intro N m _ Q hcard
  by_cases hm : m = 0
  · have hcard0 : Q.carrier.card = 0 := hcard.trans hm
    refine ⟨0, Fin.elim0, ?_, ?_, ?_⟩
    · constructor
      · intro x
        have hQempty : Q.carrier = ∅ := Finset.card_eq_zero.mp hcard0
        simp [hQempty]
      · intro i
        exact Fin.elim0 i
    · intro j
      exact Fin.elim0 j
    · simp [hm]
  · let P : Fin 1 → ModAP N := fun _ => normalizedModAP Q
    refine ⟨1, P, ?_, ?_, ?_⟩
    · constructor
      · intro x
        simp [P, normalizedModAP_carrier]
      · intro i j hij
        exact (bne_iff_ne.mp hij (Subsingleton.elim i j)).elim
    · intro j
      exact normalizedModAP_isProper Q
    · have hmone : (1 : Real) ≤ m := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm)
      have hsqrt : (1 : Real) ≤ Real.sqrt m := Real.one_le_sqrt.mpr hmone
      have hbound : (1 : Real) ≤ 4 * Real.sqrt (m : Real) := calc
        (1 : Real) ≤ 4 := by norm_num
        _ ≤ 4 * Real.sqrt m := by
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left hsqrt (show (0 : Real) ≤ 4 by norm_num)
      simpa only [Nat.cast_one] using hbound

end LeanProofs.GowersSzemeredi
