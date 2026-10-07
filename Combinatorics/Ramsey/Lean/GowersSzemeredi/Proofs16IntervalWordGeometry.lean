import GowersSzemeredi.Proofs16PartialWordObstruction
import GowersSzemeredi.Proofs16BalancedFieldWord

/-! Balanced words with the literal interval alphabet, and proper interval
boxes on which their partial-domain covering obstruction can be tested. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem balanced_word_cast_interval {N R : Nat} [NeZero N] (hRN : R ≤ N)
    (w : ZMod N → Fin R) (L beta : Real) (hbeta : 0 ≤ beta)
    (hw : ∀ P : ModAP N, P.IsProper → L ≤ P.length →
      ∀ c : Fin R, ((P.carrier.filter (fun x => w x = c)).card : Real) ≤ beta * P.length) :
    let f : ZMod N → ZMod N := fun x => ((w x).val : ZMod N)
    (∀ x, f x ∈ (modInterval N 0 R).carrier) ∧
      ∀ P : ModAP N, P.IsProper → L ≤ P.length →
        ∀ c : ZMod N, ((P.carrier.filter (fun x => f x = c)).card : Real) ≤ beta * P.length := by
  classical
  let f : ZMod N → ZMod N := fun x => ((w x).val : ZMod N)
  have hf (x : ZMod N) : f x ∈ (modInterval N 0 R).carrier := by
    refine Finset.mem_image.mpr ⟨w x, Finset.mem_univ _, ?_⟩
    simp [modInterval, f]
  refine ⟨hf, ?_⟩
  intro P hP hL c
  by_cases hc : c ∈ (modInterval N 0 R).carrier
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hc
    have hi' : (i.val : ZMod N) = c := by simpa [modInterval] using hi
    rw [← hi']
    have heq : P.carrier.filter (fun x => f x = (i.val : ZMod N)) =
        P.carrier.filter (fun x => w x = i) := by
      ext x
      simp only [Finset.mem_filter, f, (alphabet_natCast_injective hRN).eq_iff]
    rw [heq]
    exact hw P hP hL i
  · have heq : P.carrier.filter (fun x => f x = c) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hc ((Finset.mem_filter.mp hx).2 ▸ hf x)
    rw [heq, Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg hbeta (Nat.cast_nonneg _)

def alphabetIntervalBox (N k L : Nat) : Box N k where
  axis := fun _ => modInterval N 0 L
  commonDiff := 1
  axis_step := fun _ => rfl

theorem alphabetIntervalBox_proper {N k L : Nat} [NeZero N] (hLN : L ≤ N) :
    (alphabetIntervalBox N k L).IsProper := fun _ => modInterval_zero_isProper hLN

theorem alphabetIntervalBox_width (N k L : Nat) :
    (alphabetIntervalBox N (k + 1) L).width = L := by
  apply Nat.le_antisymm
  · exact (alphabetIntervalBox N (k + 1) L).width_le_axis_length (Fin.last k)
  · exact Box.le_width_of_le_axis _ (Nat.succ_pos _) (fun _ => le_rfl)

theorem alphabetIntervalBox_nonempty {N k L : Nat} [NeZero N] (hL : 0 < L) :
    (alphabetIntervalBox N k L).carrier.Nonempty := by
  classical
  refine ⟨fun _ => 0, ?_⟩
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
  intro i
  refine Finset.mem_image.mpr ⟨⟨0, hL⟩, Finset.mem_univ _, ?_⟩
  simp [alphabetIntervalBox, modInterval]

theorem alphabetIntervalBox_subset_slab {N k L : Nat} [NeZero N] :
    (alphabetIntervalBox N (k + 1) L).carrier ⊆
      lastProductSet (Finset.univ : Finset (Point N k)) (modInterval N 0 L).carrier := by
  classical
  intro x hx
  have hx' := (Finset.mem_filter.mp hx).2 (Fin.last k)
  simpa only [lastProductSet, Finset.mem_filter, Finset.mem_univ, true_and, alphabetIntervalBox, section16Last] using hx'

end LeanProofs.GowersSzemeredi
