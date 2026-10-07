import GowersSzemeredi.Proofs16ClassPruning

/-! Size-weighted failure bounds give a linear inverse-loss sample budget.
Classes of size at least two are estimated without a minimum density;
singletons are charged separately before interpolation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace LeanProofs.GowersSzemeredi

/-- Weighting failure by class size eliminates the small-class density
cutoff: each class of size at least two costs at most 6*n/r in expectation. -/
theorem section16_weighted_distinct_failure {α : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α]
    (C : Finset α) (r : Nat) (hr : 0 < r) (hC : 2 ≤ C.card) :
    (C.card : Real) *
      (((Finset.univ.filter (fun sample : Fin r → α =>
        ¬ section16SampleHasDistinctPair C sample)).card : Real) /
        Fintype.card (Fin r → α)) ≤ 6 * Fintype.card α / r := by
  let n : Real := Fintype.card α
  let d : Real := (C.card / 2 : Nat)
  let x : Real := (n - d) / n
  have hn : 0 < n := by dsimp [n]; exact_mod_cast Fintype.card_pos
  have hr0 : (0 : Real) < r := by exact_mod_cast hr
  have hd : 0 ≤ d := by positivity
  have hdn : C.card / 2 ≤ Fintype.card α :=
    (Nat.div_le_self _ _).trans (Finset.card_le_univ C)
  have hdn' : d ≤ n := by dsimp [d, n]; exact_mod_cast hdn
  have hx : 0 ≤ x := div_nonneg (sub_nonneg.mpr hdn') hn.le
  have hc : (C.card : Real) ≤ 3 * d := by
    dsimp [d]
    exact_mod_cast (show C.card ≤ 3 * (C.card / 2) by omega)
  have hone : 1 - x = d / n := by dsimp [x]; field_simp; ring
  have hp := section16_pow_mul_linear_le_one hx r
  rw [hone] at hp
  have hp' : x ^ r * (n + (r : Real) * d) ≤ n := by
    calc
      _ = (x ^ r * (1 + (r : Real) * (d / n))) * n := by field_simp
      _ ≤ 1 * n := mul_le_mul_of_nonneg_right hp hn.le
      _ = n := one_mul _
  have hpn : (0 : Real) ≤ x ^ r * n := mul_nonneg (pow_nonneg hx _) hn.le
  have hcw := mul_le_mul_of_nonneg_right hc (mul_nonneg (Nat.cast_nonneg r) (pow_nonneg hx r))
  have hfinal : (C.card : Real) * (2 * x ^ r) ≤ 6 * n / r := by
    apply (le_div_iff₀ hr0).mpr
    nlinarith only [hp', hpn, hcw]
  apply (mul_le_mul_of_nonneg_left (section16_distinct_sampling_probability_bound C r)
    (Nat.cast_nonneg C.card)).trans
  simpa only [x, n, d, Nat.cast_sub hdn] using hfinal

/-- Finite averaging with a separate expected weighted-loss budget for
each event. No independence between the events is required. -/
theorem finite_weighted_event_selection_budgets {Ω I : Type*}
    [Fintype Ω] [Nonempty Ω] [Fintype I]
    (bad : I → Ω → Prop) [∀ i, DecidablePred (bad i)] (weight budget : I → Real)
    (hbudget : ∀ i, ((Finset.univ.filter (bad i)).card : Real) * weight i ≤
      budget i * Fintype.card Ω) :
    ∃ outcome, (∑ i, if bad i outcome then weight i else 0) ≤ ∑ i, budget i := by
  classical
  have hsum : (∑ outcome : Ω, ∑ i, if bad i outcome then weight i else 0) ≤
      ∑ _outcome : Ω, ∑ i, budget i := by
    calc
      _ = ∑ i, ((Finset.univ.filter (bad i)).card : Real) * weight i := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_filter]
        simp
      _ ≤ ∑ i, budget i * Fintype.card Ω := Finset.sum_le_sum (fun i _ => hbudget i)
      _ = _ := by simp [Finset.sum_mul, mul_comm]
  obtain ⟨outcome, _, h⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty hsum
  exact ⟨outcome, h⟩

/-- One sample simultaneously controls all class losses by the number of
classes, regardless of their individual densities. -/
theorem section16_weighted_sample_loss {α I : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype I]
    (C : I → Finset α) (r : Nat) (hr : 0 < r)
    (hC : ∀ i, (C i).card = 0 ∨ 2 ≤ (C i).card) :
    ∃ sample : Fin r → α,
      (∑ i, ((C i).card : Real)) -
        (∑ i, ((section16RetainedClass (C i) sample).card : Real)) ≤
      (Fintype.card I : Real) * (6 * Fintype.card α / r) := by
  classical
  have hΩ : (0 : Real) < Fintype.card (Fin r → α) := by exact_mod_cast Fintype.card_pos
  have hb (i : I) :
      ((Finset.univ.filter (fun sample : Fin r → α => ¬ section16SampleHasDistinctPair (C i) sample)).card : Real) * (C i).card ≤
        (6 * Fintype.card α / r) * Fintype.card (Fin r → α) := by
    rcases hC i with hi | hi
    · simp only [hi, Nat.cast_zero, mul_zero]
      positivity
    · have h := section16_weighted_distinct_failure (C i) r hr hi
      apply (div_le_iff₀ hΩ).mp
      simpa only [mul_div_assoc, mul_comm] using h
  obtain ⟨sample, hs⟩ := finite_weighted_event_selection_budgets
    (fun i (sample : Fin r → α) => ¬ section16SampleHasDistinctPair (C i) sample)
    (fun i => ((C i).card : Real)) (fun _ => 6 * Fintype.card α / r) hb
  refine ⟨sample, ?_⟩
  rw [← Finset.sum_sub_distrib]
  convert hs using 1
  · apply Finset.sum_congr rfl
    intro i _
    by_cases h : section16SampleHasDistinctPair (C i) sample <;> simp [section16RetainedClass, h]
  · simp

/-- Discard only singletons before size-weighted sampling. The same total
loss 2*sigma now needs r*sigma>=6*q, instead of r*sigma^2>=6*q. -/
theorem section16_linear_prune_and_sample {α β : Type*}
    [Fintype α] [DecidableEq α] [Nonempty α] [Fintype β]
    (q r : Nat) (C : β × Fin q → Finset α) (σ : Real) (hq : 0 < q) (_hσ : 0 < σ)
    (hlong : 2 * (q : Real) ≤ σ * Fintype.card α)
    (hr : 6 * (q : Real) ≤ (r : Real) * σ) :
    ∃ (sample : Fin r → α) (D : β × Fin q → Finset α),
      (∀ i, D i ⊆ C i) ∧
      (∀ i, (D i).Nonempty → section16SampleHasDistinctPair (D i) sample) ∧
      (∑ i, ((C i).card : Real)) - (∑ i, ((D i).card : Real)) ≤
        2 * σ * Fintype.card β * Fintype.card α := by
  classical
  let L := fun i => if 2 ≤ (C i).card then C i else ∅
  have hL (i) : L i ⊆ C i := by dsimp [L]; split_ifs <;> simp
  have hLsize (i) : (L i).card = 0 ∨ 2 ≤ (L i).card := by
    dsimp [L]; split_ifs with h <;> simp [h]
  have hr0 : 0 < r := by
    by_contra hz
    have hz' : r = 0 := by omega
    have hq0 : (0 : Real) < q := by exact_mod_cast hq
    simp only [hz', Nat.cast_zero, zero_mul] at hr
    linarith only [hr, hq0]
  obtain ⟨sample, hs⟩ := section16_weighted_sample_loss L r hr0 hLsize
  refine ⟨sample, fun i => section16RetainedClass (L i) sample,
    fun i => (section16RetainedClass_subset _ _).trans (hL i),
    fun i hi => section16RetainedClass_anchors _ _ hi, ?_⟩
  have hloss : (∑ i, ((C i).card : Real)) - (∑ i, ((L i).card : Real)) ≤
      (Fintype.card β : Real) * q := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ _i : β × Fin q, (1 : Real) := by
        apply Finset.sum_le_sum
        intro i _
        dsimp [L]
        split_ifs with h
        · simp
        · simp only [Finset.card_empty, Nat.cast_zero, sub_zero]
          exact_mod_cast (show (C i).card ≤ 1 by omega)
      _ = _ := by simp
  have hrR : (0 : Real) < r := by exact_mod_cast hr0
  have hfrac : 6 * (q : Real) / r ≤ σ := (div_le_iff₀ hrR).mpr (by linarith only [hr])
  have hbudget : (Fintype.card (β × Fin q) : Real) * (6 * Fintype.card α / r) ≤
      σ * Fintype.card β * Fintype.card α := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
    calc
      _ = (6 * (q : Real) / r) * Fintype.card β * Fintype.card α := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfrac (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have hsingle := mul_le_mul_of_nonneg_left hlong (Nat.cast_nonneg (Fintype.card β) : (0 : Real) ≤ Fintype.card β)
  nlinarith only [hs, hbudget, hloss, hsingle]

/-- The new rounded budget never exceeds the previous quadratic budget
throughout the permitted loss range. -/
theorem section16_linear_sample_budget_le_quadratic (q : Nat) {σ : Real}
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) :
    ⌈6 * (q : Real) / σ⌉₊ ≤ ⌈6 * (q : Real) / σ ^ 2⌉₊ := by
  apply Nat.ceil_mono
  exact div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hσ) (by nlinarith only [hσ, hσ1])

end LeanProofs.GowersSzemeredi
