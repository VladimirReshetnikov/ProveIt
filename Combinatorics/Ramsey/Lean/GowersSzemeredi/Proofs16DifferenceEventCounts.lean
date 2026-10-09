import GowersSzemeredi.Proofs16PopularDifferenceCounts
import OAI.Combinatorics.Progressions.Probability.DifferenceEventProbability

/-! Relate the selected Croot--Sisask difference event to finite pair and
four-term representation counts. The popular event has probability at
least one half at zero, and its shifted probability controls robust counts. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open OAI.Erdos3 OAI.Erdos3.CyclicCrootSisask

/-- The probability is the normalized count of shifted difference pairs. -/
theorem difference_event_probability_eq_pair_count {N : Nat} [NeZero N]
    (A K : Finset (ZMod N)) (t : ZMod N) :
    differenceEventProbability A A K t = ((shiftedDifferencePairs A K t).card : Real)/(A.card : Real)^2 := by
  unfold differenceEventProbability
  simp only [Finset.expect_eq_sum_div_card]
  rw [←Finset.sum_div, div_div]
  have hsum : (∑ a ∈ A, ∑ b ∈ A, realSetIndicator K (a-b+t)) =
      ((shiftedDifferencePairs A K t).card : Real) := by
    simp only [shiftedDifferencePairs, Finset.card_filter, Finset.sum_product]
    push_cast
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    by_cases h : a-b+t ∈ K <;> simp [realSetIndicator, h]
  rw [hsum, pow_two]

/-- Popular differences retain at least half the difference-event probability. -/
theorem popular_difference_event_probability_ge_half {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {delta : Real} (hd : 0 < delta)
    (hA : delta*N ≤ (A.card : Real)) :
    (1/2 : Real) ≤ differenceEventProbability A A (popularDifferenceSet A (delta^2*N/2)) 0 := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcard : (0 : Real) < A.card := (mul_pos hd hn).trans_le hA
  rw [difference_event_probability_eq_pair_count, le_div_iff₀ (sq_pos_of_pos hcard)]
  simpa only [one_div_mul_eq_div] using popular_difference_pairs_dense A hd.le hA

/-- A popular shifted event yields polynomially many four-term representations. -/
theorem four_difference_representations_ge_of_popular_event {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {delta : Real} (hd : 0 < delta)
    (hA : delta*N ≤ (A.card : Real)) (t : ZMod N)
    (hevent : (1/4 : Real) ≤ differenceEventProbability A A (popularDifferenceSet A (delta^2*N/2)) t) :
    delta^4/8*(N : Real)^3 ≤ ((fourDifferenceRepresentations A t).card : Real) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hcard : (0 : Real) < A.card := (mul_pos hd hn).trans_le hA
  have hpair : (A.card : Real)^2/4 ≤
      ((shiftedDifferencePairs A (popularDifferenceSet A (delta^2*N/2)) t).card : Real) := by
    rw [difference_event_probability_eq_pair_count, le_div_iff₀ (sq_pos_of_pos hcard)] at hevent
    simpa only [one_div_mul_eq_div] using hevent
  have hquad := four_difference_representations_ge_popular_pairs A
    (popularDifferenceSet A (delta^2*N/2)) t
    (fun d hd => (Finset.mem_filter.mp hd).2)
  have hsq : (delta*N)^2 ≤ (A.card : Real)^2 := pow_le_pow_left₀ (by positivity) hA 2
  calc
    delta^4/8*(N : Real)^3 = (delta^2*N/2)*((delta*N)^2/4) := by ring
    _ ≤ (delta^2*N/2)*((A.card : Real)^2/4) := by gcongr
    _ ≤ (delta^2*N/2)*(shiftedDifferencePairs A (popularDifferenceSet A (delta^2*N/2)) t).card :=
      mul_le_mul_of_nonneg_left hpair (by positivity)
    _ ≤ _ := hquad

end LeanProofs.GowersSzemeredi
