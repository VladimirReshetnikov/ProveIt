import GowersSzemeredi.Proofs16ResizedProgressionSums

/-! Four-pair encoding of an additive eight-tuple, with a closed chain of
shared anchor points. Six tiny entries bound every nontrivial prefix. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

abbrev PairedColumnTuple (N : Nat) := Fin 4 → ZMod N × ZMod N

def pairedColumnIndex {N : Nat} (q : PairedColumnTuple N) : ZMod N :=
  ∑ i, ((q i).1-(q i).2)

def pairedTupleShift {N : Nat} (q : PairedColumnTuple N) : Fin 4 → ZMod N :=
  ![0,(q 0).1-(q 0).2,
    ((q 0).1-(q 0).2)+((q 1).1-(q 1).2),
    ((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2)]

def pairedShiftWord {N : Nat} (q : PairedColumnTuple N) (i : Fin 4) : Fin 6 → ZMod N :=
  ![(if (0 : Fin 4) < i then (q 0).1 else 0),
    (if (0 : Fin 4) < i then -(q 0).2 else 0),
    (if (1 : Fin 4) < i then (q 1).1 else 0),
    (if (1 : Fin 4) < i then -(q 1).2 else 0),
    (if (2 : Fin 4) < i then (q 2).1 else 0),
    (if (2 : Fin 4) < i then -(q 2).2 else 0)]

theorem paired_shift_word_sum {N : Nat} (q : PairedColumnTuple N) (i : Fin 4) :
    ∑ j, pairedShiftWord q i j = pairedTupleShift q i := by
  fin_cases i <;> simp [pairedShiftWord, pairedTupleShift, Fin.sum_univ_succ] <;> ring

/-- All four chain vertices stay in `Q/16`, with a common candidate from
`Q/32` and eight endpoints from `Q/256`. -/
theorem paired_tuple_chain_mem {N : Nat} (Q : CenteredProgression N) (q : PairedColumnTuple N)
    (hq : ∀ i, (q i).1 ∈ (centeredProgressionShrink Q 256).carrier ∧
      (q i).2 ∈ (centeredProgressionShrink Q 256).carrier)
    {u : ZMod N} (hu : u ∈ (centeredProgressionShrink Q 32).carrier) (i : Fin 4) :
    u+pairedTupleShift q i ∈ (centeredProgressionShrink Q 16).carrier := by
  have hzero : (0 : ZMod N) ∈ (centeredProgressionShrink Q 256).carrier :=
    (centered_progression_mem_iff _ 0).mpr ⟨fun _ => 0, by simp, by simp⟩
  have hneg : ∀ j, -(q j).2 ∈ (centeredProgressionShrink Q 256).carrier :=
    fun j => cyclic_centered_progression_neg_mem _ (hq j).2
  have hword : ∀ j, pairedShiftWord q i j ∈ (centeredProgressionShrink Q 256).carrier := by
    intro j
    fin_cases j <;> dsimp [pairedShiftWord] <;> split_ifs <;>
      first | exact (hq 0).1 | exact hneg 0 | exact (hq 1).1 | exact hneg 1 |
        exact (hq 2).1 | exact hneg 2 | exact hzero
  have h := centered_progression_six_word_shift_mem Q u (pairedShiftWord q i) hu hword
  simpa only [paired_shift_word_sum] using h

/-- The final anchor returns to the first when the eight-tuple is additive. -/
theorem paired_chain_quad_additive {N : Nat} (q : PairedColumnTuple N)
    (hadd : pairedColumnIndex q = 0) (u : ZMod N) (i : Fin 4) :
    (q i).1-(q i).2 = (u+pairedTupleShift q (i+1))-(u+pairedTupleShift q i) := by
  have hsum := hadd
  rw [pairedColumnIndex, Fin.sum_univ_four] at hsum
  fin_cases i
  · change (q 0).1-(q 0).2 = (u+((q 0).1-(q 0).2))-(u+0)
    ring
  · change (q 1).1-(q 1).2 =
      (u+(((q 0).1-(q 0).2)+((q 1).1-(q 1).2)))-(u+((q 0).1-(q 0).2))
    ring
  · change (q 2).1-(q 2).2 =
      (u+(((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2)))-
        (u+(((q 0).1-(q 0).2)+((q 1).1-(q 1).2)))
    ring
  · change (q 3).1-(q 3).2 = (u+0)-
      (u+(((q 0).1-(q 0).2)+((q 1).1-(q 1).2)+((q 2).1-(q 2).2)))
    linear_combination hsum

end LeanProofs.GowersSzemeredi
