import GowersSzemeredi.Proofs16SampleSelection

/-! # Deleting small classes before distinct-anchor sampling

The ambient final-coordinate space must be long enough for every surviving
class to contain two points. This condition is explicit, rather than being
inferred from a positive real density threshold.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace LeanProofs.GowersSzemeredi

def section16LargeClass {α : Type*} [Fintype α]
    (C : Finset α) (q : Nat) (σ : ℝ) : Finset α :=
  if σ * Fintype.card α ≤ (q : ℝ) * C.card then C else ∅

theorem section16LargeClass_subset {α : Type*} [Fintype α]
    (C : Finset α) (q : Nat) (σ : ℝ) : section16LargeClass C q σ ⊆ C := by
  classical
  unfold section16LargeClass
  split_ifs <;> simp

theorem section16LargeClass_size {α : Type*} [Fintype α]
    (C : Finset α) (q : Nat) (σ : ℝ) (hq : 0 < q)
    (hlong : 2 * (q : ℝ) ≤ σ * Fintype.card α)
    (hne : (section16LargeClass C q σ).Nonempty) :
    2 ≤ (section16LargeClass C q σ).card ∧
      σ * Fintype.card α ≤ (q : ℝ) * (section16LargeClass C q σ).card := by
  classical
  unfold section16LargeClass at *
  split_ifs with h
  · refine ⟨?_, h⟩
    have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hc : (2 : ℝ) ≤ C.card := by nlinarith
    exact_mod_cast hc
  · simp [h] at hne

/-- The mass removed from one class is at most the density threshold. -/
theorem section16LargeClass_loss {α : Type*} [Fintype α]
    (C : Finset α) (q : Nat) (σ : ℝ) (hq : 0 < q) (hσ : 0 ≤ σ) :
    (C.card : ℝ) - (section16LargeClass C q σ).card ≤
      σ * Fintype.card α / q := by
  classical
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  unfold section16LargeClass
  split_ifs with h
  · simp only [sub_self]
    positivity
  · simp only [Finset.card_empty, Nat.cast_zero, sub_zero]
    apply (le_div_iff₀ hq').mpr
    linarith [not_le.mp h]

/-- For q classes per base point, the total pruning loss is at most
sigma times the ambient product cardinality. -/
theorem section16LargeClass_total_loss {α β : Type*} [Fintype α] [Fintype β]
    (q : Nat) (C : β × Fin q → Finset α) (σ : ℝ) (hq : 0 < q) (hσ : 0 ≤ σ) :
    (∑ i, ((C i).card : ℝ)) - (∑ i, ((section16LargeClass (C i) q σ).card : ℝ)) ≤
      σ * Fintype.card β * Fintype.card α := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _i : β × Fin q, σ * Fintype.card α / q :=
      Finset.sum_le_sum (fun i _ => section16LargeClass_loss (C i) q σ hq hσ)
    _ = _ := by
      have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
      field_simp

/-- Delete small classes, then select one sample. The combined discarded
mass is at most 2*sigma times the ambient product size. Each surviving
class keeps two distinct anchors from that same sample. -/
theorem section16_prune_and_sample {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β]
    (q r : Nat) (C : β × Fin q → Finset α) (σ : ℝ) (hq : 0 < q) (hσ : 0 < σ)
    (hlong : 2 * (q : ℝ) ≤ σ * Fintype.card α)
    (hmass : (∑ i, ((C i).card : ℝ)) ≤ (Fintype.card β : ℝ) * Fintype.card α)
    (hr : 6 * (q : ℝ) ≤ (r : ℝ) * σ ^ 2) :
    ∃ (sample : Fin r → α) (D : β × Fin q → Finset α),
      (∀ i, D i ⊆ C i) ∧
      (∀ i, (D i).Nonempty → section16SampleHasDistinctPair (D i) sample) ∧
      (∑ i, ((C i).card : ℝ)) - (∑ i, ((D i).card : ℝ)) ≤
        2 * σ * Fintype.card β * Fintype.card α := by
  let L := fun i => section16LargeClass (C i) q σ
  obtain ⟨sample, hs⟩ := section16_sample_retained_mass L q r σ hσ
    (fun i hi => section16LargeClass_size (C i) q σ hq hlong hi) hr
  refine ⟨sample, fun i => section16RetainedClass (L i) sample,
    fun i => (section16RetainedClass_subset _ _).trans (section16LargeClass_subset _ _ _),
    fun i hi => section16RetainedClass_anchors _ _ hi, ?_⟩
  have hloss := section16LargeClass_total_loss q C σ hq hσ.le
  have hsub : (∑ i, ((L i).card : ℝ)) ≤ ∑ i, ((C i).card : ℝ) := by
    apply Finset.sum_le_sum
    intro i _
    exact_mod_cast Finset.card_le_card (section16LargeClass_subset (C i) q σ)
  have hweighted := mul_le_mul_of_nonneg_left (hsub.trans hmass) hσ.le
  change (∑ i, ((C i).card : ℝ)) - (∑ i, ((L i).card : ℝ)) ≤ _ at hloss
  nlinarith [hs, hloss, hweighted]

end LeanProofs.GowersSzemeredi
