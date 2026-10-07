/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.ModularHalfExponentExceptions
import OAI.Combinatorics.Progressions.Estimates.ModularUnitGCD
import OAI.Combinatorics.Progressions.Lattices.ModularAffineSpatialGCD
import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankBadProduct
import OAI.Combinatorics.Progressions.Linear.AllocatedModularRankFullProductLaw

namespace OAI

section

namespace Erdos3

theorem modularAffineSpatial_power_ratio_le {p : ℝ} (hp : 1 ≤ p)
    {v a : ℕ} (hva : 2 * v ≤ a) :
    p ^ v / p ^ a ≤ (p ^ a) ^ (-(1 : ℝ) / 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hexp : (v : ℝ) - a ≤ -(a : ℝ) / 2 := by
    have h : (2 : ℝ) * v ≤ a := by exact_mod_cast hva
    linarith
  calc
    p ^ v / p ^ a = p ^ ((v : ℝ) - (a : ℝ)) := by
      rw [Real.rpow_sub hp0, Real.rpow_natCast, Real.rpow_natCast]
    _ ≤ p ^ (-(a : ℝ) / 2) := Real.rpow_le_rpow_of_exponent_le hp hexp
    _ = (p ^ a) ^ (-(1 : ℝ) / 2) := by
      rw [← Real.rpow_natCast_mul hp0.le]
      congr 1
      ring

theorem modularRankSmallBallExponent_le_half {m : ℕ} (hm : 2 ≤ m) :
    modularRankSmallBallExponent m ≤ (1 : ℝ) / 2 := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    modularRankSmallBallExponent m ≤ (2 : ℝ) ^ (-(1 : ℝ)) := by
      unfold modularRankSmallBallExponent
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    _ = (1 : ℝ) / 2 := by norm_num

theorem modularAffineSpatial_sqrt_le_tag {q : ℝ} (hq : 1 ≤ q)
    {m : ℕ} (hm : 2 ≤ m) :
    q ^ (-(1 : ℝ) / 2) ≤ (m : ℝ) * q ^ (-modularRankSmallBallExponent m) := by
  have hp : q ^ (-(1 : ℝ) / 2) ≤ q ^ (-modularRankSmallBallExponent m) :=
    Real.rpow_le_rpow_of_exponent_le hq (by
      simpa only [neg_div] using neg_le_neg (modularRankSmallBallExponent_le_half hm))
  exact hp.trans (le_mul_of_one_le_left (Real.rpow_nonneg (by linarith) _)
    (by exact_mod_cast (show 1 ≤ m by omega)))

theorem modularAffineSpatial_gcd_cost_le_sqrt {stride p a : ℕ}
    (hstride : 0 < stride) (hp : p.Prime)
    (ha : 2 * stride.factorization p ≤ a) :
    (Nat.gcd ((stride : ZMod (p ^ a)).val) (p ^ a) : ℝ) /
        ((p ^ a : ℕ) : ℝ) ≤ ((p ^ a : ℕ) : ℝ) ^ (-(1 : ℝ) / 2) := by
  rw [zmod_natCast_gcd_primePower_eq_pow_min_factorization hstride hp a,
    min_eq_left (show stride.factorization p ≤ a by omega)]
  push_cast
  exact modularAffineSpatial_power_ratio_le (by exact_mod_cast hp.one_lt.le) ha

theorem modularAffineSpatial_gcd_cost_le_tag {stride p a m : ℕ}
    (hstride : 0 < stride) (hp : p.Prime)
    (ha : 2 * stride.factorization p ≤ a) (hm : 2 ≤ m) :
    (Nat.gcd ((stride : ZMod (p ^ a)).val) (p ^ a) : ℝ) /
        ((p ^ a : ℕ) : ℝ) ≤
      (m : ℝ) * ((p ^ a : ℕ) : ℝ) ^ (-modularRankSmallBallExponent m) := by
  apply (modularAffineSpatial_gcd_cost_le_sqrt hstride hp ha).trans
  apply modularAffineSpatial_sqrt_le_tag _ hm
  exact_mod_cast (Nat.one_le_pow a p hp.pos)

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

theorem designatedPolynomial_affine_linearRow_zero_probability_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [decI : DecidableEq I]
    (N : ℕ) [NeZero N] (S : A → Finset I) (selected : A → I)
    (hselected : ∀ i, selected i ∈ S i) (hcard : ∀ i, (S i).card = 1)
    (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (Q : MvPolynomial I (ZMod N)) (offset multiplier : A → ZMod N)
    (u : Fin 0 → I → ZMod N) :
    (𝔼 c : A → ZMod N,
      if polynomialLinearRow (polynomialIterDifference 0
        (Q + ∑ i, (offset i + multiplier i * c i) • ∏ j ∈ S i, X j) u) = 0
        then (1 : ℝ) else 0) ≤
      ∏ i, (Nat.gcd (multiplier i).val N : ℝ) / N := by
  apply uniform_selected_row_zero_probability_le N _ selected
    (fun i => (polynomialIterDifference 0 Q u).coeff
      (Finsupp.single (selected i) 1) + offset i) multiplier
  intro c i
  have h := polynomialIterDifference_disjoint_designated_linearCoeff
    Finset.univ S (fun i => offset i + multiplier i * c i) Q 0 i
    (Finset.mem_univ _) (selected i) (hselected i) (hcard i)
    (fun _ _ _ _ hij => hdisjoint hij) u
  have he (d : DecidableEq I) : @Finset.erase I d (S i) (selected i) = ∅ := by
    let := d
    apply Finset.card_eq_zero.mp
    rw [Finset.card_erase_of_mem (hselected i), hcard]
  simpa only [polynomialLinearRow, squarefreePermanent, he, ite_true, mul_one,
    add_assoc, mul_comm] using h

theorem designatedPolynomial_expected_affine_linearRow_zero_le {A I : Type*}
    [Fintype A] [DecidableEq A] [Fintype I] [DecidableEq I]
    (N : ℕ) [NeZero N] (S : A → Finset I)
    (hcard : ∀ i, (S i).card = 1)
    (hdisjoint : Pairwise (fun i j => Disjoint (S i) (S j)))
    (Q : MvPolynomial I (ZMod N)) (offset multiplier : A → ZMod N) :
    (𝔼 c : A → ZMod N, 𝔼 u : Fin 0 → I → ZMod N,
      if polynomialLinearRow (polynomialIterDifference 0
        (Q + ∑ i, (offset i + multiplier i * c i) • ∏ j ∈ S i, X j) u) = 0
        then (1 : ℝ) else 0) ≤
      ∏ i, (Nat.gcd (multiplier i).val N : ℝ) / N := by
  have hnonempty (i : A) : (S i).Nonempty :=
    Finset.card_pos.mp (by rw [hcard]; omega)
  choose selected hselected using hnonempty
  rw [Finset.expect_comm]
  calc
    _ ≤ 𝔼 _u : Fin 0 → I → ZMod N,
        ∏ i, (Nat.gcd (multiplier i).val N : ℝ) / N := by
      apply Finset.expect_le_expect
      intro u _
      exact designatedPolynomial_affine_linearRow_zero_probability_le N S selected
        hselected hcard hdisjoint Q offset multiplier u
    _ = _ := Fintype.expect_const _

theorem affineCoefficientArray_update {A B R : Type*} [DecidableEq B] [Semiring R]
    (offset : B → A → R) (multiplier : B → R) (c : B → A → R)
    (b₀ : B) (d : A → R) :
    (fun b i => offset b i + multiplier b * Function.update c b₀ d b i) =
      Function.update (fun b i => offset b i + multiplier b * c b i) b₀
        (fun i => offset b₀ i + multiplier b₀ * d i) := by
  funext b i
  by_cases hb : b = b₀
  · subst b
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hb]

theorem vectorDesignatedRankFailureProbability_affine_mean_le {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (b₀ : B)
    (hcard : ∀ i, (S b₀ i).card = 1)
    (hdisjoint : Pairwise (fun i j => Disjoint (S b₀ i) (S b₀ j)))
    (offset : B → A → ZMod N) (multiplier : B → ZMod N) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod N)).mean
      (fun c => vectorDesignatedRankFailureProbability N 0 S Q w
        (fun b i => offset b i + multiplier b * c b i)) ≤
      ((Nat.gcd (w b₀ * multiplier b₀).val N : ℝ) / N) ^ Fintype.card A := by
  have hconditional (c : B → A → ZMod N) :
      (𝔼 d : A → ZMod N, vectorDesignatedRankFailureProbability N 0 S Q w
        (fun b i => offset b i + multiplier b * Function.update c b₀ d b i)) ≤
        ((Nat.gcd (w b₀ * multiplier b₀).val N : ℝ) / N) ^ Fintype.card A := by
    simp_rw [affineCoefficientArray_update]
    unfold vectorDesignatedRankFailureProbability
    simp_rw [designatedVectorComponent_update_row, mul_add, ← mul_assoc]
    have h := designatedPolynomial_expected_affine_linearRow_zero_le N (S b₀)
      hcard hdisjoint
      ((∑ b ∈ Finset.univ.erase b₀, w b • designatedVectorComponent S Q
        (fun b i => offset b i + multiplier b * c b i) b) + w b₀ • Q b₀)
      (fun i => w b₀ * offset b₀ i) (fun _ => w b₀ * multiplier b₀)
    simpa only [Finset.prod_const, Finset.card_univ] using h
  rw [FiniteProbabilityWeights.uniform_mean,
    ← expect_uniform_coordinate_refresh b₀ (fun c : B → A → ZMod N =>
      vectorDesignatedRankFailureProbability N 0 S Q w
        (fun b i => offset b i + multiplier b * c b i))]
  calc
    _ ≤ 𝔼 _c : B → A → ZMod N,
        ((Nat.gcd (w b₀ * multiplier b₀).val N : ℝ) / N) ^ Fintype.card A :=
      Finset.expect_le_expect (fun c _ => hconditional c)
    _ = _ := Fintype.expect_const _

theorem vectorDesignatedRankFailureProbability_affine_mean_le_of_unit {A B I : Type*}
    [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] (N : ℕ) [NeZero N]
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod N))
    (w : B → ZMod N) (b₀ : B) (hunit : IsUnit (w b₀))
    (hcard : ∀ i, (S b₀ i).card = 1)
    (hdisjoint : Pairwise (fun i j => Disjoint (S b₀ i) (S b₀ j)))
    (offset : B → A → ZMod N) (multiplier : B → ZMod N) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod N)).mean
      (fun c => vectorDesignatedRankFailureProbability N 0 S Q w
        (fun b i => offset b i + multiplier b * c b i)) ≤
      ((Nat.gcd (multiplier b₀).val N : ℝ) / N) ^ Fintype.card A := by
  obtain ⟨unit, hunit⟩ := hunit
  have h := vectorDesignatedRankFailureProbability_affine_mean_le N S Q w b₀
    hcard hdisjoint offset multiplier
  rw [← hunit, zmod_gcd_unit_mul] at h
  exact h

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

noncomputable def affineSpatialCoefficients {A B R : Type*} [Semiring R]
    (spatial : B → Prop) (stride : B → ℕ) (offset : B → A → R)
    (c : B → A → R) : B → A → R :=
  fun b i => if spatial b then (stride b : R) * c b i + offset b i else c b i

theorem vectorDesignatedRankFailureProbability_affineSpatial_zero_mean_le
    {A B I : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a : ℕ} {stride : B → ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (spatial : B → Prop)
    (hstride : ∀ b, spatial b → 0 < stride b)
    (hdeep : ∀ b, spatial b → 2 * (stride b).factorization p ≤ a) (offset : B → A → ZMod (p ^ a))
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ b i, (S b i).card = 1)
    (hdisjoint : ∀ b, Pairwise (fun i j => Disjoint (S b i) (S b j)))
    (w : B → ZMod (p ^ a)) (hprimitive : ∃ b, IsUnit (w b)) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (fun c => vectorDesignatedRankFailureProbability (p ^ a) 0 S Q w
        (affineSpatialCoefficients spatial stride offset c)) ≤
      (((p : ℝ) ^ a) ^ (-(1 : ℝ) / 2)) ^ Fintype.card A := by
  obtain ⟨b₀, hb₀⟩ := hprimitive
  let off : B → A → ZMod (p ^ a) := fun b i => if spatial b then offset b i else 0
  let mult : B → ZMod (p ^ a) := fun b => if spatial b then (stride b : ZMod (p ^ a)) else 1
  have he (c : B → A → ZMod (p ^ a)) :
      affineSpatialCoefficients spatial stride offset c =
        fun b i => off b i + mult b * c b i := by
    funext b i
    by_cases hb : spatial b <;> simp [affineSpatialCoefficients, off, mult, hb, add_comm]
  simp_rw [he]
  apply (vectorDesignatedRankFailureProbability_affine_mean_le_of_unit (p ^ a)
    S Q w b₀ hb₀ (hcard b₀) (hdisjoint b₀) off mult).trans
  apply pow_le_pow_left₀ (by positivity)
  by_cases hb : spatial b₀
  · simpa only [mult, ite_eq_left hb, Nat.cast_pow] using
      modularAffineSpatial_gcd_cost_le_sqrt (hstride b₀ hb) hp (hdeep b₀ hb)
  · have h := modularAffineSpatial_gcd_cost_le_sqrt (stride := 1)
      (by norm_num) hp (show 2 * Nat.factorization 1 p ≤ a from
        calc
          2 * Nat.factorization 1 p = 0 := by simp
          _ ≤ a := ha.le)
    simpa only [mult, ite_eq_right hb, Nat.cast_one, Nat.cast_pow] using h

theorem affineSpatialCoefficients_eq_self {A B R : Type*} [Semiring R]
    (spatial : B → Prop) (stride : B → ℕ) (offset : B → A → R)
    (c : B → A → R) (hspatial : ∀ b, ¬ spatial b) :
    affineSpatialCoefficients spatial stride offset c = c := by
  funext b i
  simp only [affineSpatialCoefficients, ite_eq_right (hspatial b)]

theorem vectorDesignatedRankFailureProbability_affineSpatial_mean_le
    {A B I : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    [Fintype I] [DecidableEq I] {p a n s : ℕ} {stride : B → ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (hs : 2 ≤ s) (hns : n + 1 ≤ s)
    (spatial : B → Prop) (hspatial : ∀ b, spatial b → n = 0)
    (hstride : ∀ b, spatial b → 0 < stride b)
    (hdeep : ∀ b, spatial b → 2 * (stride b).factorization p ≤ a)
    (offset : B → A → ZMod (p ^ a))
    (S : B → A → Finset I) (Q : B → MvPolynomial I (ZMod (p ^ a)))
    (hcard : ∀ b i, (S b i).card = n + 1)
    (hdisjoint : ∀ b, Pairwise (fun i j => Disjoint (S b i) (S b j)))
    (w : B → ZMod (p ^ a)) (hprimitive : ∃ b, IsUnit (w b)) :
    (FiniteProbabilityWeights.uniform (B → A → ZMod (p ^ a))).mean
      (fun c => vectorDesignatedRankFailureProbability (p ^ a) n S Q w
        (affineSpatialCoefficients spatial stride offset c)) ≤
      ((s : ℝ) * ((p : ℝ) ^ a) ^ (-modularRankSmallBallExponent s)) ^ Fintype.card A := by
  by_cases hn : n = 0
  · subst n
    apply (vectorDesignatedRankFailureProbability_affineSpatial_zero_mean_le
      hp ha spatial hstride hdeep offset S Q hcard hdisjoint w hprimitive).trans
    apply pow_le_pow_left₀ (by positivity)
    exact modularAffineSpatial_sqrt_le_tag
      (one_le_pow₀ (by exact_mod_cast hp.one_lt.le)) hs
  · have hnone (b : B) : ¬ spatial b := fun hb => hn (hspatial b hb)
    simp_rw [affineSpatialCoefficients_eq_self spatial stride offset _ hnone]
    exact vectorDesignatedRankFailureProbability_mean_le hp ha hns S Q
      hcard hdisjoint w hprimitive

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

theorem taggedVectorDesignatedRank_affineSpatial_exceptional_probability {T A I : Type*}
    [Fintype T] [DecidableEq T] [Fintype A] [DecidableEq A]
    [Fintype I] [DecidableEq I] {B : T → Type*}
    [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    {p a s m : ℕ} [NeZero p] (hp : p.Prime) (ha : 0 < a)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (spatial : ∀ t, B t → Prop)
    (hspatial : ∀ t b, spatial t b → n t = 0)
    (stride : ∀ t, B t → ℕ)
    (hstride : ∀ t b, spatial t b → 0 < stride t b)
    (hdeep : ∀ t b, spatial t b → 2 * (stride t b).factorization p ≤ a)
    (offset : ∀ t, B t → A → ZMod (p ^ a))
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
          vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t) (Q t) w
          (affineSpatialCoefficients (spatial t) (stride t) (offset t) (c t))) ≤
      ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  let Rows (t : T) := {w : B t → ZMod (p ^ a) // ∃ b, IsUnit (w b)}
  let Row := Σ t, Rows t
  let ρ : Row → (∀ t, B t → A → ZMod (p ^ a)) → ℝ := fun w c =>
    vectorDesignatedRankFailureProbability (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val
      (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) (c w.1))
  have hρ (w : Row) (c) : 0 ≤ ρ w c :=
    vectorDesignatedRankFailureProbability_nonneg (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val
      (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) (c w.1))
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
  have h :
      (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))).eventProbability
        (fun c => ∃ w : Row, ((p : ℝ) ^ a) ^ (-C) < ρ w c) ≤
          ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
    by_cases hs : 2 ≤ s
    · apply modularRank_exceptional_probability_of_parameters
        (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))) ρ hρ
        hC (Nat.cast_nonneg m) hq hJ hrows
      intro w
      rw [FiniteProbabilityWeights.uniform_mean]
      change (𝔼 c : ∀ t, B t → A → ZMod (p ^ a),
        vectorDesignatedRankFailureProbability (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val
          (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) (c w.1))) ≤ _
      rw [expect_uniform_coordinate (X := fun t => B t → A → ZMod (p ^ a)) w.1
        (fun d => vectorDesignatedRankFailureProbability (p ^ a) (n w.1)
          (S w.1) (Q w.1) w.2.val
          (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) d))]
      have hh := vectorDesignatedRankFailureProbability_affineSpatial_mean_le
        hp ha hs (hns w.1) (spatial w.1) (hspatial w.1) (hstride w.1) (hdeep w.1) (offset w.1)
        (S w.1) (Q w.1) (hcard w.1) (hdisjoint w.1) w.2.val w.2.property
      simpa only [FiniteProbabilityWeights.uniform_mean] using hh
    · by_cases hs0 : s = 0
      · apply modularRank_exceptional_probability_of_parameters
          (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))) ρ hρ
          hC (Nat.cast_nonneg m) hq hJ hrows
        intro w
        have hh := hns w.1
        omega
      · have hs1 : s = 1 := by omega
        have hJ1 : 2 * (C + m + 10) ≤ (Fintype.card A : ℝ) := by
          have hh := Nat.le_of_ceil_le hJ
          simpa [hs1, modularRankSmallBallExponent] using hh
        have hrows1 : (Fintype.card Row : ℝ) ≤ ((p : ℝ) ^ a) ^ (m : ℝ) := by
          simpa [hs1] using hrows
        apply modularRank_half_exceptional_probability
          (FiniteProbabilityWeights.uniform (∀ t, B t → A → ZMod (p ^ a))) ρ hρ
          hq1 hJ1 hrows1
        intro w
        have hn : n w.1 = 0 := by have hh := hns w.1; omega
        rw [FiniteProbabilityWeights.uniform_mean]
        change (𝔼 c : ∀ t, B t → A → ZMod (p ^ a),
          vectorDesignatedRankFailureProbability (p ^ a) (n w.1) (S w.1) (Q w.1) w.2.val
            (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) (c w.1))) ≤ _
        rw [expect_uniform_coordinate (X := fun t => B t → A → ZMod (p ^ a)) w.1
        (fun d => vectorDesignatedRankFailureProbability (p ^ a) (n w.1)
          (S w.1) (Q w.1) w.2.val
          (affineSpatialCoefficients (spatial w.1) (stride w.1) (offset w.1) d))]
        have hcard1 : ∀ b j, (S w.1 b j).card = 1 := by
          simpa [hn] using hcard w.1
        have hh := vectorDesignatedRankFailureProbability_affineSpatial_zero_mean_le
          hp ha (spatial w.1) (hstride w.1) (hdeep w.1) (offset w.1) (S w.1) (Q w.1)
          hcard1 (hdisjoint w.1) w.2.val w.2.property
        simpa only [FiniteProbabilityWeights.uniform_mean, hn] using hh
  have hev (c : ∀ t, B t → A → ZMod (p ^ a)) :
      (∃ w : Row, ((p : ℝ) ^ a) ^ (-C) < ρ w c) ↔
        (∃ t, ∃ w : B t → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
          ((p : ℝ) ^ a) ^ (-C) <
            vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t) (Q t) w
          (affineSpatialCoefficients (spatial t) (stride t) (offset t) (c t))) := by
    constructor
    · rintro ⟨⟨t, ⟨w, hw⟩⟩, hh⟩
      exact ⟨t, w, hw, hh⟩
    · rintro ⟨t, w, hw, hh⟩
      exact ⟨⟨t, ⟨w, hw⟩⟩, hh⟩
  simpa only [hev] using h

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

theorem scalarCoefficientBad_affineSpatial_probability_eq (n : T → ℕ)
    (S : ∀ t, B t → D → Finset I) (Q : ∀ t, B t → MvPolynomial I ℤ)
    (C : ℝ) (M : ℕ) [NeZero M]
    (spatial : ∀ t, B t → Prop) (stride : ∀ t, B t → ℕ)
    (offset : ∀ t, B t → D → ZMod M) :
    (FiniteProbabilityWeights.uniform ((Σ t, B t × D) → ZMod M)).eventProbability
      (fun x => scalarCoefficientBad n S Q C M
        (fun j => affineSpatialCoefficients (spatial j.1) (stride j.1) (offset j.1)
          (scalarCoefficientTupleEquiv x j.1) j.2.1 j.2.2)) =
    (FiniteProbabilityWeights.uniform (∀ t, B t → D → ZMod M)).eventProbability
      (fun c => ∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
        (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
          (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w
          (affineSpatialCoefficients (spatial t) (stride t) (offset t) (c t))) := by
  let e := scalarCoefficientTupleEquiv (T := T) (B := B) (D := D) (V := ZMod M)
  have h := uniform_mean_surjective_hom e.toAddMonoidHom e.surjective
    (fun c => @ite ℝ (∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
      (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
        (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w
        (affineSpatialCoefficients (spatial t) (stride t) (offset t) (c t)))
      (Classical.propDecidable _) 1 0)
  exact h

theorem scalarCoefficientBad_affineSpatial_probability {p a s m : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (spatial : ∀ t, B t → Prop)
    (hspatial : ∀ t b, spatial t b → n t = 0)
    (stride : ∀ t, B t → ℕ)
    (hstride : ∀ t b, spatial t b → 0 < stride t b)
    (hdeep : ∀ t b, spatial t b → 2 * (stride t b).factorization p ≤ a)
    (offset : ∀ t, B t → D → ZMod (p ^ a))
    (S : ∀ t, B t → D → Finset I) (Q : ∀ t, B t → MvPolynomial I ℤ)
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold s ≤ p ^ a)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card D) :
    (FiniteProbabilityWeights.uniform ((Σ t, B t × D) → ZMod (p ^ a))).eventProbability
      (fun x => scalarCoefficientBad n S Q C (p ^ a)
        (fun j => affineSpatialCoefficients (spatial j.1) (stride j.1) (offset j.1)
          (scalarCoefficientTupleEquiv x j.1) j.2.1 j.2.2)) ≤
      1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  rw [scalarCoefficientBad_affineSpatial_probability_eq]
  have h := taggedVectorDesignatedRank_affineSpatial_exceptional_probability
    hp ha n hns hTs hBm spatial hspatial stride hstride hdeep offset S
    (fun t b => (Q t b).map (Int.castRingHom (ZMod (p ^ a)))) hcard hdisjoint hC
    (modularCoefficientPrimeThreshold_le_primePower hlarge) hJ
  simpa only [Nat.cast_pow, primePower_rpow_neg_ten] using h

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {L : ℕ} {R : Type*}

def allocatedCongruenceIsSpatial (inactive : LayerSamplerAxis I n → Prop)
    (j : Fin m) : AllocatedCongruenceRankOutput X E inactive j → Prop
  | .inl _ => True
  | .inr _ => False

theorem allocatedCongruenceIsSpatial_degree
    (inactive : LayerSamplerAxis I n → Prop) (j : Fin m)
    (o : AllocatedCongruenceRankOutput X E inactive j)
    (ho : allocatedCongruenceIsSpatial inactive j o) : j.val = 0 := by
  cases o with
  | inl x => exact x.property
  | inr o => exact False.elim ho

def allocatedCongruenceAffineCoefficients [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → R)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → R) :
    AllocatedCongruenceCoefficientIndex X E inactive L → R
  | ⟨j,.inl x,l⟩ => offset ⟨j,.inl x,l⟩ + stride x.val * c ⟨j,.inl x,l⟩
  | ⟨j,.inr o,l⟩ => c ⟨j,.inr o,l⟩

theorem allocatedCongruenceAffineCoefficients_spatial [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → R)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → R)
    (j : Fin m) (x : SpatialDegreeOutput X j) (l : Fin L) :
    allocatedCongruenceAffineCoefficients inactive stride offset c ⟨j,.inl x,l⟩ =
      offset ⟨j,.inl x,l⟩ + stride x.val * c ⟨j,.inl x,l⟩ := rfl

theorem allocatedCongruenceAffineCoefficients_nonspatial [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → R)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → R)
    (j : Fin m) (o : E j ⊕ AllocatedCongruenceIntegerAxis inactive j) (l : Fin L) :
    allocatedCongruenceAffineCoefficients inactive stride offset c ⟨j,.inr o,l⟩ =
      c ⟨j,.inr o,l⟩ := rfl

theorem allocatedCongruenceAffineCoefficients_intCast
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℤ)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ) (N : ℕ) :
    (fun j => ((allocatedCongruenceAffineCoefficients (R := ℤ) inactive stride offset c j : ℤ) : ZMod N)) =
      allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod N))
        (fun j => (offset j : ZMod N)) (fun j => (c j : ZMod N)) := by
  funext j
  rcases j with ⟨j,(x | o),l⟩
  · simp only [allocatedCongruenceAffineCoefficients, Int.cast_add, Int.cast_mul]
  · rfl

noncomputable def allocatedMixedAffineSelectedValues
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℤ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {N : ℕ} (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    AllocatedCongruenceCoefficientIndex X E inactive L → ℤ :=
  allocatedCongruenceAffineCoefficients inactive stride offset
    (allocatedMixedSelectedValues inactive x deck)

theorem allocatedMixedAffineSelectedValues_cast
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℤ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {N : ℕ} [NeZero N] (M : ℕ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod M))
      (fun j => (offset j : ZMod M))
      (allocatedMixedCoefficientEquiv inactive L (ZMod M)
        (Sum.elim (fun j => (x j : ZMod M)) (fun j => ZMod.cast (deck j)))) =
      (fun j => (allocatedMixedAffineSelectedValues inactive stride offset x deck j : ZMod M)) := by
  rw [allocatedMixedCoefficientEquiv_cast]
  exact (allocatedCongruenceAffineCoefficients_intCast inactive stride offset _ M).symm

theorem allocatedMixedAffineSelectedValues_natCast
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℕ)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ℤ)
    {N : ℕ} [NeZero N] (M : ℕ)
    (x : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod M))
      (fun j => (offset j : ZMod M))
      (allocatedMixedCoefficientEquiv inactive L (ZMod M)
        (Sum.elim (fun j => (x j : ZMod M)) (fun j => ZMod.cast (deck j)))) =
      (fun j => (allocatedMixedAffineSelectedValues inactive (fun x => (stride x : ℤ))
        offset x deck j : ZMod M)) := by
  simpa only [Int.cast_natCast] using
    allocatedMixedAffineSelectedValues_cast inactive (fun x => (stride x : ℤ)) offset M x deck

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ} {R : Type*}

def allocatedFullSmoothAffine [Semiring R] (stride : X → R)
    (residue : Option (LayerSamplerVariables G I n B) × X → R)
    (z : AllocatedFullSmoothCoefficientIndex G X I n B → R) :
    AllocatedFullSmoothCoefficientIndex G X I n B → R
  | .inl t => residue t + stride t.2 * z (.inl t)
  | .inr t => z (.inr t)

def allocatedSelectedNoiseOffset [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (residue : Option (LayerSamplerVariables G I n B) × X → R) :
    AllocatedCongruenceCoefficientIndex X E inactive L → R
  | ⟨_j,.inl x,l⟩ => residue (some (.inl (spatial l)),x.val)
  | ⟨_j,.inr _,_l⟩ => 0

def allocatedSelectedSmoothAffine [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (stride : X → R) (residue : Option (LayerSamplerVariables G I n B) × X → R)
    (z : AllocatedSmoothRankCoefficientIndex X inactive L → R) :
    AllocatedSmoothRankCoefficientIndex X inactive L → R
  | ⟨j,.inl x,l⟩ => residue (some (.inl (spatial l)),x.val) + stride x.val * z ⟨j,.inl x,l⟩
  | ⟨j,.inr i,l⟩ => z ⟨j,.inr i,l⟩

theorem allocatedFullSmoothAffine_extend [Semiring R]
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (stride : X → R) (residue : Option (LayerSamplerVariables G I n B) × X → R)
    (selected : AllocatedSmoothRankCoefficientIndex X inactive L → R)
    (fixed : AllocatedFullSmoothCoefficientIndex G X I n B → R) :
    allocatedFullSmoothAffine stride residue
      (Function.extend (allocatedSmoothFullEmbedding inactive spatial block) selected fixed) =
      Function.extend (allocatedSmoothFullEmbedding inactive spatial block)
        (allocatedSelectedSmoothAffine inactive spatial stride residue selected)
        (allocatedFullSmoothAffine stride residue fixed) := by
  let F : AllocatedFullSmoothCoefficientIndex G X I n B → R → R :=
    fun t v => match t with
    | .inl t => residue t + stride t.2 * v
    | .inr _ => v
  have hs : (fun a => F (allocatedSmoothFullEmbedding inactive spatial block a) (selected a)) =
      allocatedSelectedSmoothAffine inactive spatial stride residue selected := by
    funext a
    rcases a with ⟨j,(x | i),l⟩ <;> rfl
  have h := map_coordinate_extend (allocatedSmoothFullEmbedding inactive spatial block) F selected fixed
  have hf (z : AllocatedFullSmoothCoefficientIndex G X I n B → R) :
      (fun t => F t (z t)) = allocatedFullSmoothAffine stride residue z := by
    funext t
    rcases t with t | t <;> rfl
  rw [hs, hf, hf] at h
  exact h

theorem allocatedMixedSelectedValues_affine {N : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (stride : X → ℤ) (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (selected : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (deck : AllocatedDeckRankCoefficientIndex E L → ZMod N) :
    allocatedMixedSelectedValues inactive
      (allocatedSelectedSmoothAffine inactive spatial stride residue selected) deck =
      allocatedMixedAffineSelectedValues inactive stride
        (allocatedSelectedNoiseOffset inactive spatial residue) selected deck := by
  funext a
  rcases a with ⟨j,(x | e | i),l⟩ <;> rfl

theorem allocatedMixedFullArray_affine_refresh_selected {N : ℕ}
    (inactive : LayerSamplerAxis I n → Prop) (spatial : Fin L ↪ G)
    (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ (j : Fin m) (a : AllocatedDegreeActiveAxis inactive j), Fin L ↪ B ⟨j,a.val⟩)
    (stride : X → ℤ) (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (selectedSmooth : AllocatedSmoothRankCoefficientIndex X inactive L → ℤ)
    (selectedDeck : AllocatedDeckRankCoefficientIndex E L → ZMod N)
    (smooth : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ)
    (deck : CoefficientDeckScalarIndex (LayerSamplerVariables G I n B) E → ZMod N)
    (continuous : AllocatedFullContinuousCoefficientIndex G I n B → ℤ) :
    allocatedMixedFullArray
      (allocatedFullSmoothAffine stride residue
        (Function.extend (allocatedSmoothFullEmbedding inactive spatial block) selectedSmooth smooth))
      (fun k => ((Function.extend (allocatedDeckFullEmbedding kernel) selectedDeck deck k).val : ℤ)) continuous =
      Function.extend (allocatedCongruenceActualCoefficientEmbedding inactive spatial kernel block)
        (allocatedMixedAffineSelectedValues inactive stride
          (allocatedSelectedNoiseOffset inactive spatial residue) selectedSmooth selectedDeck)
        (allocatedMixedFullArray (allocatedFullSmoothAffine stride residue smooth)
          (fun k => (deck k).val) continuous) := by
  rw [allocatedFullSmoothAffine_extend, allocatedMixedFullArray_refresh_selected,
    allocatedMixedSelectedValues_affine]

theorem allocatedFullSmoothAffine_intCast
    (stride : X → ℤ) (residue : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (z : AllocatedFullSmoothCoefficientIndex G X I n B → ℤ) (N : ℕ) :
    (fun t => ((allocatedFullSmoothAffine (R := ℤ) stride residue z t : ℤ) : ZMod N)) =
      allocatedFullSmoothAffine (fun x => (stride x : ZMod N))
        (fun t => (residue t : ZMod N)) (fun t => (z t : ZMod N)) := by
  funext t
  rcases t with t | t
  · simp only [allocatedFullSmoothAffine, Int.cast_add, Int.cast_mul]
  · rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MvPolynomial
open scoped BigOperators Classical

private theorem affine_uniform_eventProbability_le_instances (Y : Type*) (f g : Fintype Y)
    [Nonempty Y] (A : Y → Prop) (r : ℝ)
    (h : @FiniteProbabilityWeights.eventProbability Y f
      (@FiniteProbabilityWeights.uniform Y f _) A ≤ r) :
    @FiniteProbabilityWeights.eventProbability Y g
      (@FiniteProbabilityWeights.uniform Y g _) A ≤ r := by
  cases Subsingleton.elim f g
  exact h

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} {L : ℕ}

def allocatedCongruenceNaturalStride (inactive : LayerSamplerAxis I n → Prop)
    (stride : X → ℕ) (j : Fin m) : AllocatedCongruenceRankOutput X E inactive j → ℕ
  | .inl x => stride x.val
  | .inr _ => 1

theorem allocatedCongruenceAffineCoefficients_eq_scalar {R : Type*} [CommRing R]
    (inactive : LayerSamplerAxis I n → Prop) (stride : X → ℕ)
    (offset c : AllocatedCongruenceCoefficientIndex X E inactive L → R) :
    allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : R)) offset c =
      fun j => affineSpatialCoefficients (allocatedCongruenceIsSpatial inactive j.1)
        (allocatedCongruenceNaturalStride inactive stride j.1)
        (fun o l => offset ⟨j.1,o,l⟩) (scalarCoefficientTupleEquiv c j.1) j.2.1 j.2.2 := by
  funext j
  rcases j with ⟨j, (x | o), l⟩
  · simp [allocatedCongruenceAffineCoefficients, affineSpatialCoefficients,
      allocatedCongruenceIsSpatial, allocatedCongruenceNaturalStride,
      scalarCoefficientTupleEquiv, add_comm]
  · simp [allocatedCongruenceAffineCoefficients, affineSpatialCoefficients,
      allocatedCongruenceIsSpatial, scalarCoefficientTupleEquiv]

variable [Fintype G] [Fintype X] [∀ j, Fintype (I j)] [∀ j, Fintype (E j)]
    [∀ a, Fintype (B a)]

noncomputable local instance affineCongruenceScalarFintype
    (inactive : LayerSamplerAxis I n → Prop) :
    Fintype (AllocatedCongruenceScalarIndex X E inactive L) := inferInstance

noncomputable local instance affineCongruenceScalarDecidableEq
    (inactive : LayerSamplerAxis I n → Prop) :
    DecidableEq (AllocatedCongruenceScalarIndex X E inactive L) := Classical.decEq _

variable (inactive : LayerSamplerAxis I n → Prop)
    (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (r : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (projection : ∀ j, AllocatedDegreeActiveAxis inactive j →
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℤ)
    (spatial : Fin L ↪ G) (kernel : ∀ j : Fin m, Fin L × Fin (j.val + 1) ↪ G)
    (block : ∀ j, ∀ b : AllocatedDegreeActiveAxis inactive j, Fin L ↪ B ⟨j, b.val⟩)

local notation "rankS" => allocatedCongruenceRankBlockFamily (X := X) (E := E) inactive spatial kernel block
local notation "rankQ" => allocatedCongruenceRankIntegerResidualFamily inactive noise r projection spatial kernel block

theorem allocatedCongruenceModulusBad_affine_probability {p a D : ℕ} [NeZero p]
    (hm : 0 < m) (hp : p.Prime) (ha : 0 < a)
    (hD : Fintype.card X + ∑ j : Fin m, (Fintype.card (E j) + n j) ≤ D)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hdeep : ∀ x, 2 * (stride x).factorization p ≤ a)
    (offset : AllocatedCongruenceCoefficientIndex X E inactive L → ZMod (p ^ a))
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold m ≤ p ^ a)
    (hL : ⌈2 * (C + D + 10) / modularRankSmallBallExponent m⌉₊ ≤ L) :
    (FiniteProbabilityWeights.uniform
      (AllocatedCongruenceCoefficientIndex (I := I) (n := n) X E inactive L → ZMod (p ^ a))).eventProbability
      (fun c => allocatedCongruenceModulusBad inactive noise r projection spatial kernel block C (p ^ a)
        (allocatedCongruenceAffineCoefficients inactive (fun x => (stride x : ZMod (p ^ a))) offset c)) ≤
        1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  have hcount (j : Fin m) : Fintype.card (AllocatedCongruenceRankOutput X E inactive j) ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((allocatedCongruenceRankOutput_sum_card_le (X := X) (E := E) hm inactive).trans hD)
  have hstride' (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j)
      (ho : allocatedCongruenceIsSpatial inactive j o) :
      0 < allocatedCongruenceNaturalStride inactive stride j o := by
    cases o with
    | inl x => exact hstride x.val
    | inr o => exact False.elim ho
  have hdeep' (j : Fin m) (o : AllocatedCongruenceRankOutput X E inactive j)
      (ho : allocatedCongruenceIsSpatial inactive j o) :
      2 * (allocatedCongruenceNaturalStride inactive stride j o).factorization p ≤ a := by
    cases o with
    | inl x => exact hdeep x.val
    | inr o => exact False.elim ho
  have h := scalarCoefficientBad_affineSpatial_probability
    (T := Fin m) (D := Fin L) (I := LayerSamplerLongVariables inactive G B)
    (B := AllocatedCongruenceRankOutput X E inactive) (s := m) (m := D) hp ha
    (fun j => j.val) (fun j => Nat.succ_le_of_lt j.isLt)
    (by simp only [Fintype.card_fin, le_refl]) hcount
    (allocatedCongruenceIsSpatial inactive)
    (allocatedCongruenceIsSpatial_degree inactive)
    (allocatedCongruenceNaturalStride inactive stride) hstride' hdeep'
    (fun j o l => offset ⟨j,o,l⟩) rankS rankQ
    (fun j o => allocatedTaggedRankBlock_card inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    (fun j o => allocatedTaggedRankBlock_disjoint inactive j spatial (kernel j) (block j)
      (allocatedCongruenceOutputEmbedding inactive j o))
    hC hlarge (by simpa only [Fintype.card_fin] using hL)
  have heq : (fun c => allocatedCongruenceModulusBad inactive noise r projection
      spatial kernel block C (p ^ a)
      (allocatedCongruenceAffineCoefficients inactive
        (fun x => (stride x : ZMod (p ^ a))) offset c)) =
      fun c => scalarCoefficientBad (fun j : Fin m => j.val) rankS rankQ C (p ^ a)
        (fun j => affineSpatialCoefficients (allocatedCongruenceIsSpatial inactive j.1)
          (allocatedCongruenceNaturalStride inactive stride j.1)
          (fun o l => offset ⟨j.1,o,l⟩) (scalarCoefficientTupleEquiv c j.1) j.2.1 j.2.2) := by
    funext c
    apply propext
    rw [allocatedCongruenceModulusBad_iff_scalarCoefficientBad,
      allocatedCongruenceAffineCoefficients_eq_scalar]
  rw [heq]
  exact affine_uniform_eventProbability_le_instances _ _ _ _ _ h

end Erdos3.VectorPolynomial

end

end OAI
