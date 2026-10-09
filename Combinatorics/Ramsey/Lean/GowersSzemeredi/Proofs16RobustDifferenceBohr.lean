import GowersSzemeredi.Proofs16DifferenceEventCounts
import OAI.Combinatorics.Progressions.Estimates.LocalizedSiftingAlmostPeriods

/-!
SPDX-License-Identifier: Apache-2.0

Adapted for ProveIt from openai/math revision
adc7f1241b42e322a6451854ab7e4b4c146bf78a, module
OAI/Combinatorics/Progressions/Estimates/LocalizedSiftingAlmostPeriods.lean.
The width/rank calculation of `exists_quartic_bogolyubov` is adapted to
an arbitrary difference event at error `1/4`. The result retains the
pointwise event estimate and supplies robust four-term counts via popular
differences. Copyright remains with the upstream copyright holders;
see the adjacent LICENSE.openai-math for provenance and Apache-2.0 terms.
No additional upstream module is imported into the selected port closure.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open OAI.Erdos3 OAI.Erdos3.CyclicCrootSisask
open scoped Pointwise NNReal

def robustDifferenceBohrConstant : Real := 3*almostPeriodicityWidthConstant (1/4)

theorem robustDifferenceBohrConstant_pos : 0 < robustDifferenceBohrConstant :=
  mul_pos (by norm_num) (almostPeriodicityWidthConstant_pos (by norm_num))

/-- A pointwise difference-event controller with quartic logarithmic rank. -/
theorem exists_difference_event_bohr_controller {N : Nat} [NeZero N]
    (A K : Finset (ZMod N)) {p : Real} (hp : 0 ≤ p)
    (hA : Real.exp (-p)*N ≤ (A.card : Real)) :
    ∃ R : OAI.Erdos3.CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      (R.rank : Real) ≤ 1+robustDifferenceBohrConstant*(p+1)^4 ∧
      Real.exp (-(robustDifferenceBohrConstant*(p+1))) ≤ R.radius ∧
      ∀ t ∈ R.carrier,
        |differenceEventProbability A A K t-differenceEventProbability A A K 0| ≤ (1/4 : Real) := by
  have hApos : (0 : Real) < A.card :=
    (mul_pos (Real.exp_pos _) (by exact_mod_cast NeZero.pos N)).trans_le hA
  have hAne : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hApos)
  have hN : (N : Real) ≤ Real.exp p*A.card := by
    have hmul := mul_le_mul_of_nonneg_left hA (Real.exp_pos p).le
    have he : Real.exp p*Real.exp (-p) = 1 := by rw [←Real.exp_add]; simp
    simpa only [←mul_assoc, he, one_mul] using hmul
  have hratio : (K.card : Real)/(-A).card ≤ Real.exp (2*p) := by
    rw [Finset.card_neg, div_le_iff₀ hApos]
    have hK : (K.card : Real) ≤ N := by exact_mod_cast (by simpa using Finset.card_le_univ K : K.card ≤ N)
    have hexp : Real.exp p ≤ Real.exp (2*p) := Real.exp_le_exp.mpr (by linarith)
    exact (hK.trans hN).trans (mul_le_mul_of_nonneg_right hexp hApos.le)
  have hdoub : ((A+(OAI.Erdos3.CyclicBohr.Set.whole : OAI.Erdos3.CyclicBohr.Set N).carrier).card : Real) ≤
      (2*Real.exp p)*A.card := by
    have hcard : ((A+(OAI.Erdos3.CyclicBohr.Set.whole : OAI.Erdos3.CyclicBohr.Set N).carrier).card : Real) ≤ N := by
      exact_mod_cast (by simpa using Finset.card_le_univ (A+(OAI.Erdos3.CyclicBohr.Set.whole : OAI.Erdos3.CyclicBohr.Set N).carrier) :
        (A+(OAI.Erdos3.CyclicBohr.Set.whole : OAI.Erdos3.CyclicBohr.Set N).carrier).card ≤ N)
    exact (hcard.trans hN).trans (by nlinarith [Real.exp_pos p])
  obtain ⟨R, hreg, hrank, hwidth, hupper, hsub, hshift⟩ := exists_quartic_local_almostPeriods
    OAI.Erdos3.CyclicBohr.Set.whole (by norm_num) OAI.Erdos3.CyclicBohr.Set.isRankRegular_whole
    hAne hAne.neg K (by norm_num : (0 : Real) < 1/4) (by norm_num) hp hratio hdoub
  let C := rankQuarticFactor (1/4)
  let D := C*(p+1)^4
  let a : Real := (100*2*((2*(⌈D⌉₊+1)+1 : Nat) : Real))⁻¹
  have hC : 0 < C := rankQuarticFactor_pos _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  simp only [OAI.Erdos3.CyclicBohr.Set.rank_whole, OAI.Erdos3.CyclicBohr.Set.radius_whole,
    max_self, Nat.cast_one, Nat.cast_ofNat, mul_one] at hrank hwidth hupper
  change (R.rank : Real) ≤ 1+D at hrank
  change min (((1/4 : Real)*Real.exp (-p)/6400)*(a/2))
    (((1/4 : Real)*Real.exp (-p))/(8*(D+1)))/2 ≤ R.radius at hwidth
  change R.radius ≤ ((1/4 : Real)*Real.exp (-p))/(8*(D+1)) at hupper
  have hscale : 1/(1000*(D+1)) ≤ a := by
    simpa only [a, mul_one] using OAI.Erdos3.BohrWidthBudget.selector_scale_lower_bound
      (d := 1) (by norm_num) hD
  have hrat : ((1/4 : Real)*Real.exp (-p))/(10240000000*(D+1)) ≤ R.radius := by
    have h := OAI.Erdos3.BohrWidthBudget.rational_width_lower_bound
      (u := (1/4 : Real)*Real.exp (-p)) (d := 1) (D := D) (w := 1) (v := 1) (a := a)
      (by positivity) (by norm_num) hD (by norm_num) (by norm_num) (by norm_num) (by simpa only [mul_one] using hscale)
    apply le_trans _ hwidth
    simpa only [one_pow, mul_one] using h
  have hwide : Real.exp (-(almostPeriodicityWidthConstant (1/4)*(1+p+Real.log 3))) ≤ R.radius := by
    have h := OAI.Erdos3.BohrWidthBudget.rational_width_ge_exponential
      (epsilon := 1/4) (C := C) (p := p) (d := 1) (w := 1)
      (by norm_num) hC.le hp (by norm_num) (by norm_num)
    apply le_trans _ hrat
    simpa only [almostPeriodicityWidthConstant, D, C, one_pow, mul_one, one_mul,
      show (2 : Real)+1 = 3 by norm_num] using h
  have hW : 0 < almostPeriodicityWidthConstant (1/4) := almostPeriodicityWidthConstant_pos (by norm_num)
  have hlog3 : Real.log 3 ≤ (2 : Real) := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 3)]
  have hbudget : almostPeriodicityWidthConstant (1/4)*(1+p+Real.log 3) ≤ robustDifferenceBohrConstant*(p+1) := by
    unfold robustDifferenceBohrConstant
    have h := mul_le_mul_of_nonneg_left hlog3 hW.le
    nlinarith [mul_nonneg hW.le hp]
  have hwide' : Real.exp (-(robustDifferenceBohrConstant*(p+1))) ≤ R.radius :=
    (Real.exp_le_exp.mpr (neg_le_neg hbudget)).trans hwide
  refine ⟨R, hreg, (Real.exp_pos _).trans_le hwide', ?_, ?_, hwide', ?_⟩
  · apply hupper.trans
    apply (div_le_one (by positivity)).mpr
    have h := Real.exp_le_one_iff.mpr (show -p ≤ 0 by linarith)
    nlinarith
  · have hCW := rankQuarticFactor_le_widthConstant (by norm_num : (0 : Real) < 1/4) (by norm_num)
    have hCC : C ≤ robustDifferenceBohrConstant := by
      dsimp [C, robustDifferenceBohrConstant]
      linarith
    have hmul : C*(p+1)^4 ≤ robustDifferenceBohrConstant*(p+1)^4 :=
      mul_le_mul_of_nonneg_right hCC (by positivity)
    exact hrank.trans (add_le_add le_rfl hmul)
  · intro t ht
    simpa only [differenceEventProbability_eq_triple, zero_add] using hshift t ht 0

/-- Every point of the controlled Bohr set has polynomially many four-term representations. -/
theorem exists_robust_difference_bohr {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {p : Real} (hp : 0 ≤ p)
    (hA : Real.exp (-p)*N ≤ (A.card : Real)) :
    ∃ R : OAI.Erdos3.CyclicBohr.Set N, R.IsRankRegular ∧ 0 < R.radius ∧ R.radius ≤ 1 ∧
      (R.rank : Real) ≤ 1+robustDifferenceBohrConstant*(p+1)^4 ∧
      Real.exp (-(robustDifferenceBohrConstant*(p+1))) ≤ R.radius ∧
      ∀ t ∈ R.carrier, (Real.exp (-p))^4/8*(N : Real)^3 ≤
        ((fourDifferenceRepresentations A t).card : Real) := by
  obtain ⟨R, hreg, hpos, hupper, hrank, hwidth, hevent⟩ := exists_difference_event_bohr_controller A
    (popularDifferenceSet A ((Real.exp (-p))^2*N/2)) hp hA
  have hzero := popular_difference_event_probability_ge_half A (Real.exp_pos _) hA
  refine ⟨R, hreg, hpos, hupper, hrank, hwidth, ?_⟩
  intro t ht
  apply four_difference_representations_ge_of_popular_event A (Real.exp_pos _) hA t
  have h := (abs_le.mp (hevent t ht)).1
  linarith

end LeanProofs.GowersSzemeredi
