import OAI.Combinatorics.Progressions.Estimates.ModularVectorCoefficientExceptions

namespace OAI

section

namespace Erdos3
open scoped BigOperators Classical

noncomputable def modularCoefficientPrimeThreshold (s : ℕ) : ℕ :=
  max 2 ⌈(s : ℝ) ^ (4 / modularRankSmallBallExponent s)⌉₊

theorem modularCoefficientPrimeThreshold_two_le (s : ℕ) :
    2 ≤ modularCoefficientPrimeThreshold s := le_max_left _ _

theorem modularCoefficientPrimeThreshold_real (s : ℕ) :
    max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤
      (modularCoefficientPrimeThreshold s : ℝ) := by
  apply max_le
  · exact_mod_cast modularCoefficientPrimeThreshold_two_le s
  · exact (Nat.le_ceil _).trans
      (Nat.cast_le.mpr (le_max_right 2 ⌈(s : ℝ) ^ (4 / modularRankSmallBallExponent s)⌉₊))

theorem modularCoefficientPrimeThreshold_le_primePower {s p a : ℕ}
    (h : modularCoefficientPrimeThreshold s ≤ p ^ a) :
    max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤ (p : ℝ) ^ a := by
  have hc : (modularCoefficientPrimeThreshold s : ℝ) ≤ (p : ℝ) ^ a := by
    exact_mod_cast h
  exact (modularCoefficientPrimeThreshold_real s).trans hc

theorem primePower_rpow_neg_ten (p a : ℕ) :
    ((p : ℝ) ^ a) ^ (-(10 : ℝ)) = 1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  rw [Real.rpow_neg (by positivity)]
  norm_cast
  rw [one_div]

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical

variable {T D : Type*} {B : T → Type*}

noncomputable def taggedCoefficientReduction {M N : ℕ} (hMN : M ∣ N) :
    (∀ t, B t → D → ZMod N) →+ (∀ t, B t → D → ZMod M) where
  toFun c t b j := ZMod.castHom hMN (ZMod M) (c t b j)
  map_zero' := by ext t b j; simp
  map_add' := by
    intro c d
    ext t b j
    exact map_add (ZMod.castHom hMN (ZMod M)) (c t b j) (d t b j)

theorem taggedCoefficientReduction_surjective {M N : ℕ} (hMN : M ∣ N) :
    Function.Surjective (taggedCoefficientReduction (T := T) (B := B) (D := D) hMN) := by
  intro y
  choose c hc using fun t b j => ZMod.castHom_surjective hMN (y t b j)
  exact ⟨c, funext fun t => funext fun b => funext (hc t b)⟩

theorem uniform_taggedCoefficientReduction_event
    [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D]
    [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    (E : (∀ t, B t → D → ZMod M) → Prop) :
    (FiniteProbabilityWeights.uniform (∀ t, B t → D → ZMod N)).eventProbability
      (fun c => E (taggedCoefficientReduction hMN c)) =
      (FiniteProbabilityWeights.uniform (∀ t, B t → D → ZMod M)).eventProbability E := by
  exact uniform_mean_surjective_hom (taggedCoefficientReduction hMN)
    (taggedCoefficientReduction_surjective hMN) (fun c => if E c then 1 else 0)

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

def topDepthCoefficientBad {p : ℕ} [NeZero p] (depth : ℕ)
    (n : T → ℕ) (S : ∀ t, B t → D → Finset I)
    (Q : ∀ t, B t → MvPolynomial I (ZMod (p ^ depth)))
    (C : ℝ) (a : ℕ) (c : ∀ t, B t → D → ZMod (p ^ depth)) : Prop :=
  ∃ ha : a ≤ depth, ∃ t, ∃ w : B t → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
    ((p : ℝ) ^ a) ^ (-C) <
      vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t)
        (fun b => (Q t b).map (ZMod.castHom (pow_dvd_pow p ha) (ZMod (p ^ a)))) w
        (taggedCoefficientReduction (pow_dvd_pow p ha) c t)

omit [Fintype T] [DecidableEq T] in
theorem topDepthCoefficientBad_iff {p depth a : ℕ} [NeZero p] (ha : a ≤ depth)
    (n : T → ℕ) (S : ∀ t, B t → D → Finset I)
    (Q : ∀ t, B t → MvPolynomial I (ZMod (p ^ depth)))
    (C : ℝ) (c : ∀ t, B t → D → ZMod (p ^ depth)) :
    topDepthCoefficientBad depth n S Q C a c ↔
      ∃ t, ∃ w : B t → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
        ((p : ℝ) ^ a) ^ (-C) <
          vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t)
            (fun b => (Q t b).map (ZMod.castHom (pow_dvd_pow p ha) (ZMod (p ^ a)))) w
            (taggedCoefficientReduction (pow_dvd_pow p ha) c t) := by
  constructor
  · rintro ⟨h, ht⟩
    exact ht
  · exact fun ht => ⟨ha, ht⟩

theorem topDepthCoefficientBad_probability {p depth a s m : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a) (had : a ≤ depth)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (S : ∀ t, B t → D → Finset I)
    (Q : ∀ t, B t → MvPolynomial I (ZMod (p ^ depth)))
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hq : max 2 ((s : ℝ) ^ (4 / modularRankSmallBallExponent s)) ≤ (p : ℝ) ^ a)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card D) :
    (FiniteProbabilityWeights.uniform (∀ t, B t → D → ZMod (p ^ depth))).eventProbability
      (topDepthCoefficientBad depth n S Q C a) ≤ ((p : ℝ) ^ a) ^ (-(10 : ℝ)) := by
  let f := ZMod.castHom (pow_dvd_pow p had) (ZMod (p ^ a))
  let Qlow := fun t b => (Q t b).map f
  let E : (∀ t, B t → D → ZMod (p ^ a)) → Prop := fun c =>
    ∃ t, ∃ w : B t → ZMod (p ^ a), (∃ b, IsUnit (w b)) ∧
      ((p : ℝ) ^ a) ^ (-C) <
        vectorDesignatedRankFailureProbability (p ^ a) (n t) (S t) (Qlow t) w (c t)
  have he : topDepthCoefficientBad depth n S Q C a =
      fun c => E (taggedCoefficientReduction (pow_dvd_pow p had) c) := by
    funext c
    exact propext (topDepthCoefficientBad_iff had n S Q C c)
  rw [he, uniform_taggedCoefficientReduction_event]
  exact taggedVectorDesignatedRank_exceptional_probability hp ha n hns hTs hBm
    S Qlow hcard hdisjoint hC hq hJ

end Erdos3

end

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

def coefficientPrimeArrayBad (P : Finset ℕ) (depth : ℕ → ℕ)
    [∀ p : P, NeZero p.val] (n : T → ℕ) (S : ∀ t, B t → D → Finset I)
    (Q : ∀ p : P, ∀ t, B t → MvPolynomial I (ZMod (p.val ^ depth p.val))) (C : ℝ) :
    ℕ → ℕ → (∀ p : P, ∀ t, B t → D → ZMod (p.val ^ depth p.val)) → Prop :=
  primeArrayBad P (fun p a => topDepthCoefficientBad (depth p.val) n S (Q p) C a)

theorem coefficientPrimeArray_bad_product_probability
    (P : Finset ℕ) (depth : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) {s m R : ℕ} (hR : 0 < R)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (S : ∀ t, B t → D → Finset I)
    (Q : ∀ p : P, ∀ t, B t → MvPolynomial I (ZMod (p.val ^ depth p.val)))
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card D) :
    (FiniteProbabilityWeights.pi (fun p : P =>
      FiniteProbabilityWeights.uniform (∀ t, B t → D → ZMod (p.val ^ depth p.val)))).eventProbability
      (fun c => smallPrimePowerCorrection (modularCoefficientPrimeThreshold s) * R <
        ∏ p ∈ P, p ^ largestTestedBadDepth depth
          (coefficientPrimeArrayBad P depth n S Q C) p c) ≤ 2 / (9 * (R : ℝ) ^ 9) := by
  let maxPower := max 1 (P.sup (fun p => p ^ depth p))
  have hmax : ∀ p ∈ P, p ^ depth p ≤ maxPower := by
    intro p hp
    exact (Finset.le_sup (f := fun p => p ^ depth p) hp).trans (le_max_right _ _)
  apply independent_largestBadPrimeProduct_probability P
    (fun p : P => FiniteProbabilityWeights.uniform (∀ t, B t → D → ZMod (p.val ^ depth p.val)))
    (fun p a => topDepthCoefficientBad (depth p.val) n S (Q p) C a) depth
    hprime (modularCoefficientPrimeThreshold_two_le s) (le_max_left 1 _) hR hmax
  intro p a ha had hlarge
  have h := topDepthCoefficientBad_probability (hprime p.val p.property) ha had n hns hTs hBm
    S (Q p) hcard hdisjoint hC (modularCoefficientPrimeThreshold_le_primePower hlarge) hJ
  simpa only [primePower_rpow_neg_ten] using h

end Erdos3

end

end OAI
