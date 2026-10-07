import OAI.Combinatorics.Progressions.Estimates.ModerateSliceTensorApproximation
import OAI.Combinatorics.Progressions.Probability.SmoothModerateBlockLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

structure IntegerFourierAxis where
  Source : Type
  Coordinate : Type
  [sourceFinite : Fintype Source]
  [coordinateFinite : Fintype Coordinate]
  scale : ℕ
  [scaleNeZero : NeZero scale]
  radius : ℕ
  period : ℕ
  [periodNeZero : NeZero period]
  scale_le_period : scale ≤ period
  law : FiniteProbabilityWeights Source
  image : (Coordinate → ℤ) → Source → Coordinate → ℤ
  countConstant : ℝ
  countExponent : ℕ
  coefficientCap : ℝ
  denominatorBound : ℝ → ℝ
  residualBound : ℝ → ℝ
  approximation : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ S : Finset (Coordinate → Fin period),
      (S.card : ℝ) ≤ countConstant / ε ^ countExponent ∧
      (∀ center, (∑ k, ‖integerGridCoefficient law (image center) period k‖) ≤
        coefficientCap) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ denominatorBound ε ∧
        ∃ (a : Coordinate → ℤ) (ξ : Coordinate → ℝ),
          (∀ j, |ξ j| ≤ residualBound ε) ∧
          ∀ j, ((k j).val : ℝ) / period = (a j : ℝ) / d + ξ j / scale) ∧
      ∀ center z, centeredFundamentalBox radius scale center z →
        ‖(((scale : ℝ) ^ Fintype.card Coordinate * finiteImageMass law (image center) z : ℝ) : ℂ) -
          integerGridApproximation law (image center) scale period S z‖ ≤ ε

attribute [local instance] IntegerFourierAxis.sourceFinite IntegerFourierAxis.coordinateFinite
  IntegerFourierAxis.scaleNeZero IntegerFourierAxis.periodNeZero

namespace IntegerFourierAxis

noncomputable def ofEstimate {X J : Type} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : (J → ℤ) → X → J → ℤ) (K Q M : ℕ) [NeZero K] [NeZero M]
    (hKM : K ≤ M)
    (countConstant : ℝ) (countExponent : ℕ) (coefficientCap : ℝ)
    (denominatorBound residualBound : ℝ → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ S : Finset (J → Fin M),
        (S.card : ℝ) ≤ countConstant / ε ^ countExponent ∧
        (∀ center, (∑ k, ‖integerGridCoefficient p (Y center) M k‖) ≤ coefficientCap) ∧
        (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ denominatorBound ε ∧
          ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ residualBound ε) ∧
            ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / d + ξ j / K) ∧
        ∀ center z, centeredFundamentalBox Q K center z →
          ‖(((K : ℝ) ^ Fintype.card J * finiteImageMass p (Y center) z : ℝ) : ℂ) -
            integerGridApproximation p (Y center) K M S z‖ ≤ ε) : IntegerFourierAxis :=
  { Source := X, Coordinate := J, scale := K, radius := Q, period := M,
    scale_le_period := hKM, law := p, image := Y,
    countConstant := countConstant, countExponent := countExponent, coefficientCap := coefficientCap,
    denominatorBound := denominatorBound, residualBound := residualBound, approximation := h }

end IntegerFourierAxis

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerGridCoefficient_norm_le_one {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) [NeZero M] (k : J → Fin M) :
    ‖integerGridCoefficient p Y M k‖ ≤ 1 := by
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by
    simp only [rectangularGridCharacter_norm, p.mean_const])

theorem integerGridCoefficient_full_cap {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M B : ℕ) [NeZero M] (hMB : M ≤ B) :
    (∑ k, ‖integerGridCoefficient p Y M k‖) ≤ (B : ℝ) ^ Fintype.card J := by
  calc
    _ ≤ ∑ _k : J → Fin M, (1 : ℝ) :=
      Finset.sum_le_sum (fun k _ => integerGridCoefficient_norm_le_one p Y M k)
    _ = (M : ℝ) ^ Fintype.card J := by simp
    _ ≤ (B : ℝ) ^ Fintype.card J := by exact_mod_cast Nat.pow_le_pow_left hMB (Fintype.card J)

theorem short_side_scale_bound {K L T p : ℕ} {E : ℝ} (hE : 0 ≤ E) (hL : L ≤ T)
    (hpower : (K : ℝ) ≤ E * (L : ℝ) ^ p) : K ≤ ⌈E * (T : ℝ) ^ p⌉₊ := by
  have hp : (L : ℝ) ^ p ≤ (T : ℝ) ^ p := by exact_mod_cast Nat.pow_le_pow_left hL p
  have he := hpower.trans (mul_le_mul_of_nonneg_left hp hE)
  exact_mod_cast he.trans (Nat.le_ceil _)

noncomputable def boundedIntegerFourierAxis {X J : Type} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : (J → ℤ) → X → J → ℤ) (K Q B : ℕ) [NeZero K]
    (hB : (2 * Q + 1) * K ≤ B)
    (hY : ∀ center x, p.weight x ≠ 0 → ∀ j, |(Y center x j : ℝ) - center j| ≤ (Q : ℝ) * K) :
    IntegerFourierAxis := by
  letI : DecidableEq J := Classical.decEq J
  let M := (2 * Q + 1) * K
  have hK : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  exact {
    Source := X
    Coordinate := J
    scale := K
    radius := Q
    period := M
    scale_le_period := Nat.le_mul_of_pos_left K (by omega)
    law := p
    image := Y
    countConstant := (B : ℝ) ^ Fintype.card J
    countExponent := 0
    coefficientCap := (B : ℝ) ^ Fintype.card J
    denominatorBound := fun _ => B
    residualBound := fun _ => 0
    approximation := by
      intro ε hε _hε1
      refine ⟨Finset.univ, ?_, ?_, ?_, ?_⟩
      · simp only [pow_zero, div_one, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
        exact_mod_cast Nat.pow_le_pow_left hB (Fintype.card J)
      · intro center
        exact integerGridCoefficient_full_cap p (Y center) M B hB
      · intro k _
        refine ⟨M, Nat.mul_pos (by omega) hK, by exact_mod_cast hB,
          (fun j => (k j).val), (fun _ => 0), (fun _ => by norm_num), ?_⟩
        intro j
        simp only [M, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
          Int.cast_natCast, zero_div, add_zero]
      · intro center z hz
        have he := integerGridDensity_fourier p (Y center) K M z
        rw [integerGridDensity_eq_imageMass_on_centered_box p (Y center) center z
          hK le_rfl (hY center) hz] at he
        change (((K : ℝ) ^ Fintype.card J * finiteImageMass p (Y center) z : ℝ) : ℂ) =
          integerGridApproximation p (Y center) K M Finset.univ z at he
        rw [he, sub_self, norm_zero]
        exact hε.le }

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

structure IntegerFourierBudget where
  radius : ℕ
  countConstant : ℝ
  countExponent : ℕ
  coefficientCap : ℝ
  denominatorBound : ℝ → ℝ
  residualBound : ℝ → ℝ

def IntegerFourierBudget.Controls (B : IntegerFourierBudget)
    {X J : Type*} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : (J → ℤ) → X → J → ℤ)
    (K M : ℕ) [NeZero M] : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
    ∃ S : Finset (J → Fin M),
      (S.card : ℝ) ≤ B.countConstant / ε ^ B.countExponent ∧
      (∀ center, (∑ k, ‖integerGridCoefficient p (Y center) M k‖) ≤ B.coefficientCap) ∧
      (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ B.denominatorBound ε ∧
        ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ B.residualBound ε) ∧
          ∀ j, ((k j).val : ℝ) / M = (a j : ℝ) / d + ξ j / K) ∧
      ∀ center z, centeredFundamentalBox B.radius K center z →
        ‖(((K : ℝ) ^ Fintype.card J * finiteImageMass p (Y center) z : ℝ) : ℂ) -
          integerGridApproximation p (Y center) K M S z‖ ≤ ε

namespace IntegerFourierAxis

attribute [local instance] sourceFinite coordinateFinite scaleNeZero periodNeZero

def budget (a : IntegerFourierAxis) : IntegerFourierBudget where
  radius := a.radius
  countConstant := a.countConstant
  countExponent := a.countExponent
  coefficientCap := a.coefficientCap
  denominatorBound := a.denominatorBound
  residualBound := a.residualBound

theorem budget_controls (a : IntegerFourierAxis) :
    a.budget.Controls a.law a.image a.scale a.period := a.approximation

end IntegerFourierAxis

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def weightedSliceFourierAxis {b n q K : ℕ} [NeZero b] [NeZero K]
    (s : Fin b → Fin (n + 1) → NormalizedScalarCubeSource (Fin q)) (root : Fin b → Fin (n + 1) → ℤ)
    (A W T : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (M : ℕ)
    (hM : ∀ a j, (s a j).modulusBound ≤ M) (hW : ∀ a j, (s a j).weightBound ≤ W)
    (hT : ∀ a j, (s a j).weightLipschitz ≤ T) {O F D E : ℝ}
    (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hroot : ∀ a j, |(root a j : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, ((s a j).length : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) : IntegerFourierAxis := by
  let U := affinePrimitiveEnvelope (Fin q) A W T M 1
  let Q := affineTorusRadius (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  let R := affineTorusFactor (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  let ζ := fun ε => uniformBlockRetainedBias n J.card (p * J.card) U ((R : ℝ) * D)
    (((R : ℝ) * E) ^ J.card) ε
  refine IntegerFourierAxis.ofEstimate (weightedSliceIntegerSource s root)
    (weightedSliceIntegerSum s root J) K Q (R * K)
    (Nat.le_mul_of_pos_left K (affineTorusFactor_pos _ _ _ _ _))
    (uniformSpectrumSizeConstant n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card))
    (max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card)))
    (uniformSpectrumAbsoluteCap n J.card (p * J.card) U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card))
    (fun ε => uniformCharacterDenominatorBound n J.card (p * J.card) U
      ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) (ζ ε))
    (fun ε => 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) /
      (ζ ε) ^ majorArcCoverExponent n J.card) ?_
  intro ε hε hε1
  have he := weightedSlice_geometric_approximation s root A W T hA M
    hM hW hT hO hD hE hε hε1 hroot hupper hlower p hpower J hJ hB
  dsimp only at he
  obtain ⟨S, hS, hcap, hchar, happ⟩ := he
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro center
    apply le_trans ?_ (hcap center)
    apply le_of_eq
    apply Finset.sum_congr
    · ext k
      simp only [Finset.mem_univ]
    · intro k _
      rfl
  · intro k hk
    obtain ⟨d, hd, hdb, a, ξ, hξ, heq⟩ := hchar k hk
    refine ⟨d, hd, hdb, a, ξ, hξ, ?_⟩
    intro j
    simpa only [Nat.cast_mul]
      using heq j
  · intro center z hz
    simpa only [R, integerGridApproximation, Fintype.card_coe] using happ center z hz

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def largeScaleFourierAxis {X J : Type} [Fintype X] [Fintype J]
    (p : FiniteProbabilityWeights X) (Y : (J → ℤ) → X → J → ℤ)
    (K Q Kmax : ℕ) [NeZero K] (Ccount Ccap : ℝ) (exponent : ℕ)
    (denom residual : ℝ → ℝ)
    (hsupport : ∀ center x, p.weight x ≠ 0 → ∀ j, |(Y center x j : ℝ) - center j| ≤ (Q : ℝ) * K)
    (hlarge : Kmax < K → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∃ S : Finset (J → Fin ((2 * Q + 1) * K)),
        (S.card : ℝ) ≤ Ccount / ε ^ exponent ∧
        (∀ center, (∑ k, ‖integerGridCoefficient p (Y center) ((2 * Q + 1) * K) k‖) ≤ Ccap) ∧
        (∀ k ∈ S, ∃ d : ℕ, 0 < d ∧ (d : ℝ) ≤ denom ε ∧
          ∃ (a : J → ℤ) (ξ : J → ℝ), (∀ j, |ξ j| ≤ residual ε) ∧
            ∀ j, ((k j).val : ℝ) / ((2 * Q + 1) * K : ℕ) = (a j : ℝ) / d + ξ j / K) ∧
        ∀ center z, centeredFundamentalBox Q K center z →
          ‖(((K : ℝ) ^ Fintype.card J * finiteImageMass p (Y center) z : ℝ) : ℂ) -
            integerGridApproximation p (Y center) K ((2 * Q + 1) * K) S z‖ ≤ ε) : IntegerFourierAxis := by
  let R := 2 * Q + 1
  let Cshort : ℝ := ((R * Kmax : ℕ) : ℝ) ^ Fintype.card J
  refine IntegerFourierAxis.ofEstimate p Y K Q (R * K) (Nat.le_mul_of_pos_left K (by omega))
    (max Ccount Cshort) exponent (max Ccap Cshort)
    (fun ε => max (denom ε) (R * Kmax : ℕ)) (fun ε => max (residual ε) 0) ?_
  intro ε hε hε1
  by_cases hK : Kmax < K
  · obtain ⟨S, hS, hcap, hchar, happ⟩ := hlarge hK ε hε hε1
    refine ⟨S, hS.trans (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg hε.le _)),
      (fun center => (hcap center).trans (le_max_left _ _)), ?_, happ⟩
    intro k hk
    obtain ⟨d, hd, hdb, a, ξ, hξ, heq⟩ := hchar k hk
    exact ⟨d, hd, hdb.trans (le_max_left _ _), a, ξ, (fun j => (hξ j).trans (le_max_left _ _)), heq⟩
  · have hbound : K ≤ Kmax := Nat.le_of_not_gt hK
    have hperiod : R * K ≤ R * Kmax := Nat.mul_le_mul_left R hbound
    have hcard : ((Finset.univ : Finset (J → Fin (R * K))).card : ℝ) ≤ Cshort := by
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Cshort]
      exact_mod_cast Nat.pow_le_pow_left hperiod (Fintype.card J)
    refine ⟨Finset.univ, ?_, ?_, ?_, ?_⟩
    · apply (le_div_iff₀ (pow_pos hε exponent)).mpr
      calc
        _ ≤ ((Finset.univ : Finset (J → Fin (R * K))).card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hε.le hε1) (Nat.cast_nonneg _)
        _ = _ := mul_one _
        _ ≤ max Ccount Cshort := hcard.trans (le_max_right _ _)
    · intro center
      exact (integerGridCoefficient_full_cap p (Y center) (R * K) (R * Kmax) hperiod).trans (le_max_right _ _)
    · intro k _
      refine ⟨R * K, Nat.mul_pos (by omega) (NeZero.pos K),
        (by exact_mod_cast hperiod : ((R * K : ℕ) : ℝ) ≤ ((R * Kmax : ℕ) : ℝ)).trans (le_max_right _ _),
        (fun j => (k j).val), (fun _ => 0), (fun _ => ?_), ?_⟩
      · simpa only [abs_zero] using (le_max_right (residual ε) 0)
      · intro j
        simp only [Int.cast_natCast, zero_div, add_zero]
    · intro center z hz
      have he := integerGridDensity_fourier p (Y center) K (R * K) z
      rw [integerGridDensity_eq_imageMass_on_centered_box p (Y center) center z
        (NeZero.pos K) le_rfl (hsupport center) hz] at he
      change (((K : ℝ) ^ Fintype.card J * finiteImageMass p (Y center) z : ℝ) : ℂ) =
        integerGridApproximation p (Y center) K (R * K) Finset.univ z at he
      rw [he, sub_self, norm_zero]
      exact hε.le

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def boundedCubeSliceFourierAxis {b g q K : ℕ} {C : Type} [Fintype C] [NeZero K]
    (s : Fin b → Fin g → FiniteCubeSlice q) (w : CubeSliceBlockDomain s C → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (coeff : C → Fin b → ℤ) (H : Fin b → ℝ)
    {O F : ℝ} (hO : 0 ≤ O) (hcoeff : ∀ c a, |(coeff c a : ℝ)| ≤ H a)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hvolume : ∀ a, H a * ∏ j, ((s a j).length : ℝ) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (Kmax : ℕ) (hKmax : K ≤ Kmax) : IntegerFourierAxis := by
  let Q := ⌈blockJetScaleBound q g b ((O + 1) ^ g * F)⌉₊
  refine boundedIntegerFourierAxis (cubeSliceBlockWeights s w hw hmass) (cubeSliceBlockSum s coeff J)
    K Q ((2 * Q + 1) * Kmax) (Nat.mul_le_mul_left _ hKmax) ?_
  intro center x _ S
  exact (cubeSliceBlockSum_scale_bound s coeff H hO hcoeff hroot hvolume J hJ center x S).trans
    (mul_le_mul_of_nonneg_right (Nat.le_ceil _) (Nat.cast_nonneg K))

noncomputable def shortCubeSliceFourierAxis {b g q K : ℕ} {C : Type} [Fintype C] [NeZero K]
    (s : Fin b → Fin g → FiniteCubeSlice q) (w : CubeSliceBlockDomain s C → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hmass : 0 < ∑ x, w x) (coeff : C → Fin b → ℤ) (H : Fin b → ℝ)
    {O F E : ℝ} (hO : 0 ≤ O) (hE : 0 ≤ E) (hcoeff : ∀ c a, |(coeff c a : ℝ)| ≤ H a)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hvolume : ∀ a, H a * ∏ j, ((s a j).length : ℝ) ≤ F * K)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ g)
    (a : Fin b) (j : Fin g) (p T : ℕ) (hshort : (s a j).length ≤ T)
    (hpower : (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p) : IntegerFourierAxis :=
  boundedCubeSliceFourierAxis s w hw hmass coeff H hO hcoeff hroot hvolume J hJ
    ⌈E * (T : ℝ) ^ p⌉₊ (short_side_scale_bound hE hshort hpower)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

noncomputable def smoothCubeFourierAxis {b n q M K : ℕ} [NeZero b] [NeZero K] {B T : ℝ≥0}
    (s : Fin b → Fin (n + 1) → SmoothCubeSlice q M B T)
    (hmass : ∀ a j, 0 < ∑ x, (s a j).sliceWeight x) (hB : 0 < B)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {O F D E : ℝ}
    (hO : 0 ≤ O) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hroot : ∀ a j, |((s a j).root : ℝ)| ≤ O * (s a j).length)
    (hupper : ∀ a, (∏ j, ((s a j).length : ℝ)) ≤ F * K)
    (hlower : ∀ a, (K : ℝ) ≤ D * ∏ j, ((s a j).length : ℝ))
    (p : ℕ) (hpower : ∀ a j, (K : ℝ) ≤ E * ((s a j).length : ℝ) ^ p)
    (J : Finset (Finset (Fin q))) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hblocks : uniformSpectrumBlockCount n J.card (p * J.card) ≤ b) : IntegerFourierAxis := by
  let U := affinePrimitiveEnvelope (Fin q) A (2 * B) (2 * T) M 1
  let Q := affineTorusRadius (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  let R := affineTorusFactor (Fintype.card (Fin q)) (n + 1) (Fintype.card (Fin b)) (O + 1) F
  let Kmax := ⌈E * (scalarCubeNormalizationThreshold (Fin q) M B T : ℝ) ^ p⌉₊
  let Cshort : ℝ := ((R * Kmax : ℕ) : ℝ) ^ J.card
  let Ccount := uniformSpectrumSizeConstant n J.card (p * J.card)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card)
  let Ccap := uniformSpectrumAbsoluteCap n J.card (p * J.card)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card)
  let exponent := max (majorArcSpectrumExponent n J.card) (majorArcLengthExponent n * (p * J.card))
  let ζ := fun ε => uniformBlockRetainedBias n J.card (p * J.card)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) ε
  let denom := fun ε => uniformCharacterDenominatorBound n J.card (p * J.card)
    U ((R : ℝ) * D) (((R : ℝ) * E) ^ J.card) (ζ ε)
  let residual := fun ε => 2 * majorArcCoverConstant n J.card U ((R : ℝ) * D) /
    (ζ ε) ^ majorArcCoverExponent n J.card
  refine IntegerFourierAxis.ofEstimate (smoothCubeBlockSource s hmass) (smoothCubeBlockSum s J)
    K Q (R * K) (Nat.le_mul_of_pos_left K (affineTorusFactor_pos _ _ _ _ _))
    (max Ccount Cshort) exponent (max Ccap Cshort)
    (fun ε => max (denom ε) (R * Kmax : ℕ)) (fun ε => max (residual ε) 0) ?_
  intro ε hε hε1
  by_cases hlong : ∀ a j, scalarCubeNormalizationThreshold (Fin q) M B T ≤ (s a j).length
  · have he := weightedSlice_geometric_approximation
      (fun a j => (s a j).normalized hB (hlong a j)) (fun a j => (s a j).root)
      A (2 * B) (2 * T) hA M (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => le_rfl)
      hO hD hE hε hε1 hroot hupper hlower p hpower J hJ hblocks
    dsimp only at he
    rw [smoothCubeBlockSource_normalized s hmass hB hlong, smoothCubeBlockSum_normalized s hB hlong] at he
    obtain ⟨S, hS, hcap, hchar, happ⟩ := he
    refine ⟨S, hS.trans (div_le_div_of_nonneg_right (le_max_left _ _) (pow_nonneg hε.le _)), ?_, ?_, ?_⟩
    · intro center
      apply le_trans ?_ (le_max_left Ccap Cshort)
      apply le_trans ?_ (hcap center)
      apply le_of_eq
      apply Finset.sum_congr
      · ext k
        simp only [Finset.mem_univ]
      · intro k _
        rfl
    · intro k hk
      obtain ⟨d, hd, hdb, a, ξ, hξ, heq⟩ := hchar k hk
      refine ⟨d, hd, hdb.trans (le_max_left _ _), a, ξ,
        (fun j => (hξ j).trans (le_max_left _ _)), ?_⟩
      intro j
      simpa only [Nat.cast_mul] using heq j
    · intro center z hz
      have hh := happ center z hz
      simp only [R, integerGridApproximation, Fintype.card_coe, finiteImageMass] at hh ⊢
      convert hh using 1
      apply congrArg norm
      apply congrArg₂ (fun x y : ℂ => x - y)
      · apply congrArg Complex.ofReal
        apply congrArg (fun t : ℝ => (K : ℝ) ^ J.card * t)
        unfold FiniteProbabilityWeights.mean
        apply Finset.sum_congr
        · apply Finset.ext
          intro x
          exact ⟨fun _ => Finset.mem_univ x, fun _ => Finset.mem_univ x⟩
        · intro x _
          rfl
      · apply congrArg (fun t : ℂ => ((K : ℂ) / (R * K : ℕ)) ^ J.card * t)
        apply Finset.sum_congr rfl
        intro k _
        rfl
  · push Not at hlong
    obtain ⟨a, j, hshort⟩ := hlong
    have hK : K ≤ Kmax := short_side_scale_bound hE hshort.le (hpower a j)
    have hperiod : R * K ≤ R * Kmax := Nat.mul_le_mul_left R hK
    have hSshort : ((Finset.univ : Finset (J → Fin (R * K))).card : ℝ) ≤ Cshort := by
      simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe, Nat.cast_pow, Cshort]
      exact_mod_cast Nat.pow_le_pow_left hperiod J.card
    refine ⟨Finset.univ, ?_, ?_, ?_, ?_⟩
    · apply (le_div_iff₀ (pow_pos hε exponent)).mpr
      calc
        _ ≤ ((Finset.univ : Finset (J → Fin (R * K))).card : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hε.le hε1) (Nat.cast_nonneg _)
        _ = _ := mul_one _
        _ ≤ max Ccount Cshort := hSshort.trans (le_max_right _ _)
    · intro center
      apply le_trans ?_ (le_max_right Ccap Cshort)
      simpa only [Fintype.card_coe, Cshort] using
        integerGridCoefficient_full_cap (smoothCubeBlockSource s hmass) (smoothCubeBlockSum s J center)
          (R * K) (R * Kmax) hperiod
    · intro k _
      refine ⟨R * K, Nat.mul_pos (affineTorusFactor_pos _ _ _ _ _) (NeZero.pos K),
        (by exact_mod_cast hperiod : ((R * K : ℕ) : ℝ) ≤ ((R * Kmax : ℕ) : ℝ)).trans (le_max_right _ _),
        (fun j => (k j).val), (fun _ => 0), (fun _ => ?_), ?_⟩
      · simpa only [abs_zero] using (le_max_right (residual ε) 0)
      · intro j
        simp only [Int.cast_natCast, zero_div, add_zero]
    · intro center z hz
      have he := integerGridDensity_fourier (smoothCubeBlockSource s hmass) (smoothCubeBlockSum s J center)
        K (R * K) z
      have hgrid := integerGridDensity_eq_imageMass_on_centered_box (smoothCubeBlockSource s hmass)
        (smoothCubeBlockSum s J center) center z (NeZero.pos K) le_rfl
        (fun x _ Z => by
          simpa only [Q, Fintype.card_fin] using smoothCubeBlockSum_support s hO hroot hupper J hJ center x Z) hz
      change integerGridDensity (smoothCubeBlockSource s hmass) (smoothCubeBlockSum s J center) K (R * K) z =
        (K : ℝ) ^ Fintype.card J * finiteImageMass (smoothCubeBlockSource s hmass)
          (smoothCubeBlockSum s J center) z at hgrid
      rw [hgrid] at he
      change (((K : ℝ) ^ Fintype.card J * finiteImageMass (smoothCubeBlockSource s hmass)
        (smoothCubeBlockSum s J center) z : ℝ) : ℂ) =
          integerGridApproximation (smoothCubeBlockSource s hmass) (smoothCubeBlockSum s J center)
            K (R * K) Finset.univ z at he
      rw [he]
      apply le_trans ?_ hε.le
      apply le_of_eq
      apply norm_eq_zero.mpr
      apply sub_eq_zero.mpr
      unfold integerGridApproximation
      apply congrArg (fun t : ℂ => ((K : ℂ) / (R * K : ℕ)) ^ Fintype.card J * t)
      apply Finset.sum_congr
      · apply Finset.ext
        intro k
        exact ⟨fun _ => Finset.mem_univ k, fun _ => Finset.mem_univ k⟩
      · intro k _
        rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem integerGridCoefficient_eq_of_complexMean {X Y J : Type*}
    [Fintype X] [Fintype Y] [Fintype J]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → J → ℤ) (G : Y → J → ℤ)
    (h : ∀ f : (J → ℤ) → ℂ, p.complexMean (fun x => f (F x)) = q.complexMean (fun y => f (G y)))
    (M : ℕ) [NeZero M] (k : J → Fin M) :
    integerGridCoefficient p F M k = integerGridCoefficient q G M k := h (rectangularGridCharacter M k)

theorem integerGridApproximation_eq_of_complexMean {X Y J : Type*}
    [Fintype X] [Fintype Y] [Fintype J]
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : X → J → ℤ) (G : Y → J → ℤ)
    (h : ∀ f : (J → ℤ) → ℂ, p.complexMean (fun x => f (F x)) = q.complexMean (fun y => f (G y)))
    (K M : ℕ) [NeZero M] (S : Finset (J → Fin M)) (z : J → ℤ) :
    integerGridApproximation p F K M S z = integerGridApproximation q G K M S z := by
  unfold integerGridApproximation
  simp_rw [integerGridCoefficient_eq_of_complexMean p q F G h M]

theorem IntegerFourierBudget.controls_of_complexMean {X Y J : Type*}
    [Fintype X] [Fintype Y] [Fintype J] (B : IntegerFourierBudget)
    (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (F : (J → ℤ) → X → J → ℤ) (G : (J → ℤ) → Y → J → ℤ)
    (K M : ℕ) [NeZero M]
    (h : ∀ center (f : (J → ℤ) → ℂ),
      p.complexMean (fun x => f (F center x)) = q.complexMean (fun y => f (G center y)))
    (hmodel : B.Controls p F K M) : B.Controls q G K M := by
  intro ε hε hε1
  obtain ⟨S, hcount, hcap, hchar, happ⟩ := hmodel ε hε hε1
  refine ⟨S, hcount, ?_, hchar, ?_⟩
  · intro center
    have hc := hcap center
    simp_rw [integerGridCoefficient_eq_of_complexMean p q (F center) (G center) (h center) M] at hc
    exact hc
  · intro center z hz
    have ha := happ center z hz
    rw [finiteImageMass_eq_of_complexMean p q (F center) (G center) (h center) z,
      integerGridApproximation_eq_of_complexMean p q (F center) (G center) (h center) K M S z] at ha
    exact ha

end Erdos3

end

end OAI
