import OAI.Combinatorics.Progressions.Lattices.ModularCoefficientBadPrimeProduct

namespace OAI

section

namespace Erdos3
open MvPolynomial
open scoped BigOperators Classical

def scalarCoefficientTupleEquiv {T D V : Type*} {B : T → Type*} [AddCommGroup V] :
    ((Σ t, B t × D) → V) ≃+ (∀ t, B t → D → V) where
  toFun x t b d := x ⟨t, (b,d)⟩
  invFun c j := c j.1 j.2.1 j.2.2
  left_inv x := by
    funext j
    rcases j with ⟨t,b,d⟩
    rfl
  right_inv c := rfl
  map_add' x y := rfl

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

def scalarCoefficientBad (n : T → ℕ) (S : ∀ t, B t → D → Finset I)
    (Q : ∀ t, B t → MvPolynomial I ℤ) (C : ℝ) (M : ℕ) [NeZero M]
    (x : (Σ t, B t × D) → ZMod M) : Prop :=
  ∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
    (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
      (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w
      (fun b d => x ⟨t,(b,d)⟩)

theorem scalarCoefficientBad_probability_eq (n : T → ℕ)
    (S : ∀ t, B t → D → Finset I) (Q : ∀ t, B t → MvPolynomial I ℤ)
    (C : ℝ) (M : ℕ) [NeZero M] :
    (FiniteProbabilityWeights.uniform ((Σ t, B t × D) → ZMod M)).eventProbability
      (scalarCoefficientBad n S Q C M) =
    (FiniteProbabilityWeights.uniform (∀ t, B t → D → ZMod M)).eventProbability
      (fun c => ∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
        (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
          (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w (c t)) := by
  classical
  let e := scalarCoefficientTupleEquiv (T := T) (B := B) (D := D) (V := ZMod M)
  have h := uniform_mean_surjective_hom e.toAddMonoidHom e.surjective
    (fun c => @ite ℝ (∃ t, ∃ w : B t → ZMod M, (∃ b, IsUnit (w b)) ∧
      (M : ℝ) ^ (-C) < vectorDesignatedRankFailureProbability M (n t) (S t)
        (fun b => (Q t b).map (Int.castRingHom (ZMod M))) w (c t)) (Classical.propDecidable _) 1 0)
  exact h

theorem scalarCoefficientBad_probability {p a s m : ℕ} [NeZero p]
    (hp : p.Prime) (ha : 0 < a)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (S : ∀ t, B t → D → Finset I) (Q : ∀ t, B t → MvPolynomial I ℤ)
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hlarge : modularCoefficientPrimeThreshold s ≤ p ^ a)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card D) :
    (FiniteProbabilityWeights.uniform ((Σ t, B t × D) → ZMod (p ^ a))).eventProbability
      (scalarCoefficientBad n S Q C (p ^ a)) ≤ 1 / ((p ^ a : ℕ) : ℝ) ^ 10 := by
  rw [scalarCoefficientBad_probability_eq]
  have h := taggedVectorDesignatedRank_exceptional_probability hp ha n hns hTs hBm S
    (fun t b => (Q t b).map (Int.castRingHom (ZMod (p ^ a)))) hcard hdisjoint hC
    (modularCoefficientPrimeThreshold_le_primePower hlarge) hJ
  simpa only [Nat.cast_pow, primePower_rpow_neg_ten] using h

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators Classical
open FiniteProbabilityWeights MvPolynomial

private theorem uniform_eventProbability_instances (X : Type*) (f g : Fintype X)
    [Nonempty X] (E : X → Prop) :
    @eventProbability X f (@uniform X f _) E =
      @eventProbability X g (@uniform X g _) E := by
  cases Subsingleton.elim f g
  rfl

variable {T D I : Type*} [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D] [Fintype I] [DecidableEq I]
  {B : T → Type*} [∀ t, Fintype (B t)] [∀ t, DecidableEq (B t)]

def smoothCoefficientRankBad (P : Finset ℕ) [∀ p : P, NeZero p.val]
    (n : T → ℕ) (S : ∀ t, B t → D → Finset I)
    (Q : ∀ t, B t → MvPolynomial I ℤ) (C : ℝ) :
    ℕ → ℕ → ((Σ t, B t × D) → ℤ) → Prop :=
  smoothResiduePrimeBad P (fun p a => scalarCoefficientBad n S Q C (p.val ^ a))

theorem smoothCoefficientRank_bad_product_probability
    (center width : (Σ t, B t × D) → ℝ) (hwidth : ∀ j, 0 < width j)
    (hZ : 0 < shiftedSmoothProductMass center width)
    (P : Finset ℕ) (A : ℕ → ℕ) [∀ p : P, NeZero p.val]
    (hprime : ∀ p ∈ P, p.Prime) {s m Qbound R : ℕ}
    (hQ : 1 ≤ Qbound) (hR : 0 < R) (hdepth : ∀ p ∈ P, p ^ A p ≤ Qbound)
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (S : ∀ t, B t → D → Finset I) (Q : ∀ t, B t → MvPolynomial I ℤ)
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card D)
    (hlarge : ∀ j, 8 * (probabilityProfileLipschitz : ℝ) *
      (max Qbound (R ^ 2) : ℕ) ≤ width j)
    {η : ℝ} (hη : 0 ≤ η)
    (herror : (∑ j, 16 * (probabilityProfileLipschitz : ℝ) *
      (max Qbound (R ^ 2) : ℕ) / width j) ≤ η) :
    (shiftedSmoothProductFiniteWeights center width hwidth hZ).eventProbability
      (fun x => smallPrimePowerCorrection (modularCoefficientPrimeThreshold s) * R <
        ∏ p ∈ P, p ^ largestTestedBadDepth A
          (fun p a x => smoothCoefficientRankBad P n S Q C p a x.val) p x) ≤
      2 / (9 * (R : ℝ) ^ 9) + ((Qbound : ℝ) + (R : ℝ) ^ 2) * η := by
  apply smoothResidue_badPrimeProduct_probability center width hwidth hZ P A
    (fun p a => scalarCoefficientBad n S Q C (p.val ^ a)) hprime
    (modularCoefficientPrimeThreshold_two_le s) hQ hR hdepth
    ?_ hlarge hη herror
  intro p a ha _had hlargep
  convert scalarCoefficientBad_probability (hprime p p.property) ha n hns hTs hBm
    S Q hcard hdisjoint hC hlargep hJ using 1
  exact uniform_eventProbability_instances _ _ _ _

theorem exists_early_smoothCoefficientRank_bad_product_cutoff {s m : ℕ}
    (n : T → ℕ) (hns : ∀ t, n t + 1 ≤ s) (hTs : Fintype.card T ≤ s)
    (hBm : ∀ t, Fintype.card (B t) ≤ m)
    (S : ∀ t, B t → D → Finset I)
    (hcard : ∀ t b j, (S t b j).card = n t + 1)
    (hdisjoint : ∀ t b, Pairwise (fun j k => Disjoint (S t b j) (S t b k)))
    {C : ℝ} (hC : 0 ≤ C)
    (hJ : ⌈2 * (C + m + 10) / modularRankSmallBallExponent s⌉₊ ≤ Fintype.card D)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ R : ℕ, 0 < R ∧ ∀ (Qbound : ℕ) (P : Finset ℕ) (A : ℕ → ℕ)
      [∀ p : P, NeZero p.val] (Q : ∀ t, B t → MvPolynomial I ℤ)
      (center width : (Σ t, B t × D) → ℝ) (hwidth : ∀ j, 0 < width j)
      (hZ : 0 < shiftedSmoothProductMass center width),
      1 ≤ Qbound → (∀ p ∈ P, p.Prime) → (∀ p ∈ P, p ^ A p ≤ Qbound) →
      (∀ j, 8 * (probabilityProfileLipschitz : ℝ) * (max Qbound (R ^ 2) : ℕ) ≤ width j) →
      (∑ j, 16 * (probabilityProfileLipschitz : ℝ) * (max Qbound (R ^ 2) : ℕ) / width j) ≤
        δ / (2 * ((Qbound : ℝ) + (R : ℝ) ^ 2)) →
      (shiftedSmoothProductFiniteWeights center width hwidth hZ).eventProbability
        (fun x => smallPrimePowerCorrection (modularCoefficientPrimeThreshold s) * R <
          ∏ p ∈ P, p ^ largestTestedBadDepth A
            (fun p a x => smoothCoefficientRankBad P n S Q C p a x.val) p x) ≤ δ := by
  obtain ⟨R, hR, hradius⟩ := exists_early_badPrime_radius hδ
  refine ⟨R, hR, ?_⟩
  intro Qbound P A _ Q center width hwidth hZ hQ hprime hdepth hlarge herror
  exact (smoothCoefficientRank_bad_product_probability center width hwidth hZ P A hprime
    hQ hR hdepth n hns hTs hBm S Q hcard hdisjoint hC hJ hlarge
    (hradius Qbound hQ).1.le herror).trans (hradius Qbound hQ).2

end Erdos3

end

end OAI
