import GowersSzemeredi.Proofs05ProgressionMoments
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! A uniform bound for directions that repeat an index in a modular
progression. The cyclic torsion bound applies to composite moduli as well. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

noncomputable def badProgressionDirections (N L : Nat) [NeZero N] : Finset (ZMod N) :=
  (Finset.Ico 1 L).biUnion fun h => Finset.univ.filter fun d => (h : ZMod N) * d = 0

theorem badProgressionDirections_card_le {N L : Nat} [NeZero N] :
    (badProgressionDirections N L).card ≤ L * (L - 1) / 2 := by
  classical
  calc
    _ ≤ ∑ h ∈ Finset.Ico 1 L,
        (Finset.univ.filter fun d : ZMod N => (h : ZMod N) * d = 0).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ h ∈ Finset.Ico 1 L, h := by
      apply Finset.sum_le_sum
      intro h hh
      have hh0 : 0 < h := (Finset.mem_Ico.mp hh).1
      simpa only [nsmul_eq_mul] using
        (IsAddCyclic.card_nsmul_eq_zero_le (α := ZMod N) hh0)
    _ ≤ ∑ h ∈ Finset.range L, h := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro h hh
        exact Finset.mem_range.mpr (Finset.mem_Ico.mp hh).2
      · intros
        exact Nat.zero_le _
    _ = L * (L - 1) / 2 := Finset.sum_range_id L

theorem progression_direction_injective {N L : Nat} [NeZero N] (d : ZMod N)
    (hd : d ∉ badProgressionDirections N L) :
    Function.Injective (fun i : Fin L => (i.val : ZMod N) * d) := by
  classical
  have hordered (i j : Fin L) (hij : i.val < j.val)
      (heq : (i.val : ZMod N) * d = (j.val : ZMod N) * d) : False := by
    apply hd
    apply Finset.mem_biUnion.mpr
    refine ⟨j.val - i.val, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Nat.cast_sub hij.le, sub_mul, heq, sub_self]
  intro i j heq
  by_contra hne
  have hne' : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · exact hordered i j hlt heq
  · exact hordered j i hgt heq.symm

theorem progression_proper_of_good_direction {N L : Nat} [NeZero N] (a d : ZMod N)
    (hd : d ∉ badProgressionDirections N L) :
    (ModAP.mk a d L).IsProper := by
  classical
  have hinj : Function.Injective (fun i : Fin L => a + (i.val : ZMod N) * d) := by
    intro i j hij
    exact progression_direction_injective d hd (add_left_cancel hij)
  exact (Finset.card_image_of_injective _ hinj).trans (Finset.card_fin L)

theorem badProgressionDirections_scaled_card_lt {N L : Nat} [NeZero N]
    (hL : 2 ≤ L) (hN : L ^ 3 ≤ N) :
    2 * (L : Real) * (badProgressionDirections N L).card < N := by
  have hcard := badProgressionDirections_card_le (N := N) (L := L)
  have hround : (badProgressionDirections N L).card * 2 ≤ L * (L - 1) := by
    omega
  have hroundR : (badProgressionDirections N L).card * (2 : Real) ≤
      (L : Real) * (L - 1) := by
    have hr : (badProgressionDirections N L).card * (2 : Real) ≤
        (L : Real) * ((L - 1 : Nat) : Real) := by exact_mod_cast hround
    simpa only [Nat.cast_sub (by omega : 1 ≤ L), Nat.cast_one] using hr
  have hLr : (2 : Real) ≤ L := by exact_mod_cast hL
  have hNr : (L : Real) ^ 3 ≤ N := by exact_mod_cast hN
  have hmul := mul_le_mul_of_nonneg_left hroundR (show (0 : Real) ≤ L by positivity)
  nlinarith [sq_pos_of_pos (show (0 : Real) < L by linarith)]

end LeanProofs.GowersSzemeredi
