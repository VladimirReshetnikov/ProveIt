import GowersSzemeredi.Proofs16DistinctSampling

/-! # One simultaneous sample with controlled discarded mass

The same sample is used for every affine class. The estimate is weighted
by class sizes, so it controls discarded points rather than merely the
number of unsuccessful classes.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace LeanProofs.GowersSzemeredi

/-- Averaging selects a single outcome whose total bad weight is small.
Zero-weight events need no probability estimate. -/
theorem finite_weighted_event_selection {Ω I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype I]
    (bad : I → Ω → Prop) [∀ i, DecidablePred (bad i)] (weight : I → ℝ) (σ : ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (hcount : ∀ i, weight i ≠ 0 →
      ((Finset.univ.filter (bad i)).card : ℝ) ≤ σ * Fintype.card Ω) :
    ∃ outcome, (∑ i, if bad i outcome then weight i else 0) ≤ σ * ∑ i, weight i := by
  classical
  have hsum : (∑ outcome : Ω, ∑ i, if bad i outcome then weight i else 0) ≤
      ∑ _outcome : Ω, σ * ∑ i, weight i := by
    calc
      _ = ∑ i, ((Finset.univ.filter (bad i)).card : ℝ) * weight i := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter]
        simp
      _ ≤ ∑ i, (σ * Fintype.card Ω) * weight i := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : weight i = 0
        · simp [hi]
        · exact mul_le_mul_of_nonneg_right (hcount i hi) (hw i)
      _ = _ := by simp [Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
  obtain ⟨outcome, _, h⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨outcome, h⟩

/-- The corrected distinct-anchor estimate selects one sample controlling
the total size of all failed classes. Empty classes are permitted. -/
theorem section16_sample_discarded_mass {α I : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype I]
    (C : I → Finset α) (q r : Nat) (σ : ℝ) (hσ : 0 < σ)
    (hclass : ∀ i, (C i).Nonempty →
      2 ≤ (C i).card ∧ σ * Fintype.card α ≤ (q : ℝ) * (C i).card)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * σ ^ 2) :
    ∃ sample : Fin r → α,
      (∑ i, if ¬ section16SampleHasDistinctPair (C i) sample
        then ((C i).card : ℝ) else 0) ≤ σ * ∑ i, ((C i).card : ℝ) := by
  classical
  have hcount : ∀ i, ((C i).card : ℝ) ≠ 0 →
      ((Finset.univ.filter (fun sample : Fin r → α =>
        ¬ section16SampleHasDistinctPair (C i) sample)).card : ℝ) ≤
        σ * Fintype.card (Fin r → α) := by
    intro i hi
    have hne : (C i).Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero (by exact_mod_cast hi))
    obtain ⟨hc, hdensity⟩ := hclass i hne
    have hp := section16_distinct_sampling_budget (C i) q r σ hσ hc hdensity hr
    exact (div_le_iff₀ (by exact_mod_cast Fintype.card_pos :
      (0 : ℝ) < Fintype.card (Fin r → α))).mp hp
  simpa only [ite_not] using finite_weighted_event_selection
    (fun i (sample : Fin r → α) => ¬ section16SampleHasDistinctPair (C i) sample)
    (fun i => ((C i).card : ℝ)) σ (fun _ => Nat.cast_nonneg _) hcount

/-- Retain whole successful classes, including the sampled anchors. -/
def section16RetainedClass {α : Type*} {r : Nat}
    (C : Finset α) (sample : Fin r → α) : Finset α :=
  if section16SampleHasDistinctPair C sample then C else ∅

theorem section16RetainedClass_subset {α : Type*} {r : Nat}
    (C : Finset α) (sample : Fin r → α) : section16RetainedClass C sample ⊆ C := by
  classical
  unfold section16RetainedClass
  split_ifs <;> simp

theorem section16RetainedClass_anchors {α : Type*} {r : Nat}
    (C : Finset α) (sample : Fin r → α)
    (hne : (section16RetainedClass C sample).Nonempty) :
    section16SampleHasDistinctPair (section16RetainedClass C sample) sample := by
  classical
  unfold section16RetainedClass at *
  split_ifs with h
  · exact h
  · simp [h] at hne

/-- A common sample retains at least a (1-sigma) fraction of the total
class mass, with two distinct sampled anchors in every retained class. -/
theorem section16_sample_retained_mass {α I : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype I]
    (C : I → Finset α) (q r : Nat) (σ : ℝ) (hσ : 0 < σ)
    (hclass : ∀ i, (C i).Nonempty →
      2 ≤ (C i).card ∧ σ * Fintype.card α ≤ (q : ℝ) * (C i).card)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * σ ^ 2) :
    ∃ sample : Fin r → α,
      (1 - σ) * (∑ i, ((C i).card : ℝ)) ≤
        ∑ i, ((section16RetainedClass (C i) sample).card : ℝ) := by
  obtain ⟨sample, hs⟩ := section16_sample_discarded_mass C q r σ hσ hclass hr
  refine ⟨sample, ?_⟩
  have hsplit : (∑ i, ((section16RetainedClass (C i) sample).card : ℝ)) +
      (∑ i, if ¬ section16SampleHasDistinctPair (C i) sample
        then ((C i).card : ℝ) else 0) = ∑ i, ((C i).card : ℝ) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : section16SampleHasDistinctPair (C i) sample <;>
      simp [section16RetainedClass, h]
  nlinarith [hs, hsplit]

end LeanProofs.GowersSzemeredi
