import OAI.Combinatorics.Progressions.Linear.ModularVectorCoefficientRank

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

theorem vectorDesignatedRank_exceptional_probability {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a n s m : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (hns : n + 1 ≤ s) (hBm : Fintype.card B ≤ m)
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ b j, (S b j).card = n + 1)
    (hdisjoint : ∀ b, Pairwise (fun j k => Disjoint (S b j) (S b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hq : max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤ (p : ℝ) ^ a)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card A) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).eventProbability
      (fun c => ∃ w : B → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
        ((p : ℝ) ^ a) ^ (-C) < vectorDesignatedRankFailureProbability (p ^ a) n S Q w c) ≤
      ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  let Row := {w : B → ZMod (p ^ a) // ∃ b, IsUnit (w b)}
  let ρ : Row → (B → A → ZMod (p ^ a)) → ℝ :=
    fun w => vectorDesignatedRankFailureProbability (p ^ a) n S Q w.val
  have hρ (w : Row) (c) : 0 ≤ ρ w c :=
    vectorDesignatedRankFailureProbability_nonneg (p ^ a) n S Q w.val c
  have hmean (w : Row) :
      (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean (ρ w) ≤
        ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A :=
    vectorDesignatedRankFailureProbability_mean_le hp ha hns S Q hcard hdisjoint w.val w.property
  have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ a := by
    exact one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
  have hcount : (Fintype.card Row : ℝ) ≤ ((p : ℝ) ^ a) ^ (m : ℝ) := by
    calc
      _ ≤ (Fintype.card (B → ZMod (p ^ a)) : ℝ) := by
        exact_mod_cast Fintype.card_subtype_le (fun w : B → ZMod (p ^ a) => ∃ b, IsUnit (w b))
      _ = ((p : ℝ) ^ a) ^ (Fintype.card B : ℝ) := by
        simp [ZMod.card, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by exact_mod_cast hBm)
  have hrows : (Fintype.card Row : ℝ) ≤ (s : ℝ) * ((p : ℝ) ^ a) ^ (m : ℝ) := by
    have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
    have hnonneg : 0 ≤ ((p : ℝ) ^ a) ^ (m : ℝ) := by positivity
    nlinarith
  have h := modularRank_exceptional_probability_of_parameters
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))) ρ hρ
    hC (Nat.cast_nonneg m) hq hJ hrows hmean
  simpa only [ρ, Row, Subtype.exists, exists_prop] using h

theorem taggedVectorDesignatedRank_exceptional_probability {T A I : Type*}
    [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] {B : T → Type*}
    [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    {p a s m : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (S : ∀ t, B t → A → Finset I)
    (Q : ∀ t, B t → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hq : max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤ (p : ℝ) ^ a)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card A) :
    (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))).eventProbability
      (fun c => ∃ t, ∃ w : B t → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
        ((p : ℝ) ^ a) ^ (-C) <
          vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t) (Q t) w (c t)) ≤
      ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  let Rows (t : T) := {w : B t → ZMod (p ^ a) // ∃ b, IsUnit (w b)}
  let Row := Σ t, Rows t
  let ρ : Row → (∀ t, B t → A → ZMod (p ^ a)) → ℝ := fun w c =>
    vectorDesignatedRankFailureProbability (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val (c w.1)
  have hρ (w : Row) (c) : 0 ≤ ρ w c :=
    vectorDesignatedRankFailureProbability_nonneg (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val (c w.1)
  have hmean (w : Row) :
      (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))).mean (ρ w) ≤
        ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
    rw [FiniteProbabilityWeights.uniform_mean]
    change (𝔼 c : ∀ t, B t → A → ZMod (p ^ a),
      vectorDesignatedRankFailureProbability (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val (c w.1)) ≤ _
    rw [expect_uniform_coordinate w.1]
    have h := vectorDesignatedRankFailureProbability_mean_le hp ha (hns w.1)
      (S w.1) (Q w.1) (hcard w.1) (hdisjoint w.1) w.2.val w.2.property
    simpa only [FiniteProbabilityWeights.uniform_mean] using h
  have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ a := one_le_pow₀ (by exact_mod_cast hp.one_lt.le)
  have hcount (t : T) : (Fintype.card (Rows t) : ℝ) ≤ ((p : ℝ) ^ a) ^ (m : ℝ) := by
    calc
      _ ≤ (Fintype.card (B t → ZMod (p ^ a)) : ℝ) := by
        exact_mod_cast Fintype.card_subtype_le (fun w : B t → ZMod (p ^ a) => ∃ b, IsUnit (w b))
      _ = ((p : ℝ) ^ a) ^ (Fintype.card (B t) : ℝ) := by
        simp [ZMod.card, Real.rpow_natCast]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by exact_mod_cast hBm t)
  have hrows : (Fintype.card Row : ℝ) ≤ (s : ℝ) * ((p : ℝ) ^ a) ^ (m : ℝ) := by
    change (Fintype.card (Σ t, Rows t) : ℝ) ≤ _
    rw [Fintype.card_sigma, Nat.cast_sum]
    calc
      _ ≤ ∑ _t : T, ((p : ℝ) ^ a) ^ (m : ℝ) := Finset.sum_le_sum (fun t _ => hcount t)
      _ = (Fintype.card T : ℝ) * ((p : ℝ) ^ a) ^ (m : ℝ) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hTs) (by positivity)
  have h := modularRank_exceptional_probability_of_parameters
    (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))) ρ hρ
    hC (Nat.cast_nonneg m) hq hJ hrows hmean
  have hev (c : ∀ t, B t → A → ZMod (p ^ a)) :
      (∃ w : Row, ((p : ℝ) ^ a) ^ (-C) < ρ w c) ↔
        (∃ t, ∃ w : B t → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
          ((p : ℝ) ^ a) ^ (-C) <
            vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t) (Q t) w (c t)) := by
    constructor
    · rintro ⟨⟨t, ⟨w, hw⟩⟩, hh⟩
      exact ⟨t, w, hw, hh⟩
    · rintro ⟨t, w, hw, hh⟩
      exact ⟨⟨t, ⟨w, hw⟩⟩, hh⟩
  simpa only [hev] using h

end Erdos3

end

end OAI
