import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIncompleteName

/-!
# Additivity of the actual improper Euler integral at a positive rational time

The two incomplete programs use the very same cutoff and observation
precision. The original compact split therefore transfers their sum to
the original whole improper name, and then to the original Gamma name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIncompleteName (lowerF upperF data lower_at upper_at original_regular_names)
open GaussianEulerIncompleteCofinalRate (source)
open GaussianEulerIncompleteCutoffParts (lowerData upperData piece_sources)
open GaussianEulerIntegralGammaIdentification (improper_source original_Euler_integral_is_Gamma)
open GaussianEulerImproperName (nameF name_regular)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerCutoffCauchyComparison (observation)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (crossEquivalent cross_at cross_symm cross_trans)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev sumF : PR 2 := addF lowerF upperF
def sumData (z R B A a b : PTm n) : PTm n := addData (data z R B A a b) (data z R B A a b)

@[simp] theorem subst_sumData {m : ℕ} (σ : Fin n → PTm m) (z R B A a b : PTm n) :
    Syn.subst σ (sumData z R B A a b) =
      sumData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ A) (Syn.subst σ a) (Syn.subst σ b) := by simp [sumData]

theorem original_diagonal_sum (t z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF t (GaussianEulerImproperName.data z R B A))
      (ap2 sumF t (sumData z R B A a b)) (num 10) (unit t) := by
  let k := GaussianEulerIncompleteCutoff.clock t a b
  let q := GaussianEulerCutoffCauchyComparison.clock t
  let C := GaussianEulerCompactAdditivity.nameF
  let L := lowerData z R B k A a b
  let U := upperData z R B k A a b
  let v := data z R B A a b
  let V := unit t
  let I := ap2 nameF t (GaussianEulerImproperName.data z R B A)
  let X := observation q z R B k A
  let Y := ap2 (addF C C) q (addData L U)
  let Z := qadd (ap2 C q L) (ap2 C q U)
  let S := ap2 sumF t (sumData z R B A a b)
  have hV := unit_positive (Γ := Γ) t
  have hk := GaussianEulerIncompleteCutoff.clock_later (Γ := Γ) t a b
  have hq : Γ ⊢[PRAAx] le (succ t) q :=
    le_of_eq_add (d := num 3) (by dsimp only [q, GaussianEulerCutoffCauchyComparison.clock]; ipra_ring)
  have hVq := GaussianExponentialReference.unit_monotone (le_trans (le_succ_self t) hq)
  have source : Γ ⊢[PRAAx] GaussianEulerIncompleteCutoff.source z R B A a b :=
    .andI h.andE₁.andE₁.andE₂.andE₁ (.andI h.andE₁.andE₁.andE₁ h.andE₂)
  have eqSplit := (GaussianEulerIncompleteCutoff.original_partition t k z R B A a b source (le_refl _)).andE₁
  have upperDataEq := GaussianGammaCompactCutoffSplit.euler_data_congr z R B
    (b+GaussianEulerIncompleteCutoff.lowerWidth k A R a b) (GaussianEulerIncompleteCutoff.upperWidth k A R a b)
    (GaussianEulerIncompleteCutoff.denominator k A R b) (GaussianGammaIntegralCutoffs.top k A R)
    (GaussianEulerIncompleteCutoff.splitPoint k A R a) (GaussianEulerIncompleteCutoff.upperWidth k A R a b)
    (GaussianEulerIncompleteCutoff.denominator k A R b) (GaussianGammaIntegralCutoffs.top k A R)
    eqSplit (.eqRefl _) (.eqRefl _) (.eqRefl _)
  have rawSplit := GaussianEulerIncompleteCutoff.original_compact_split t k z R B A a b source (le_refl _)
  have split := GaussianGammaCompactCutoffAlignment.cross_data_congr _ _ _ _ _ _ (.eqRefl _)
    (GaussianGammaCompactCutoffSplit.add_data_congr L L _ U (.eqRefl _) upperDataEq) rawSplit
  have first : Γ ⊢[PRAAx] distanceBounded I X two V :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hV hV) hV
      (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianEulerLaterCutoffObservation.later_cutoff_observations t q t z R B A k (improper_source _ _ _ _ h.andE₁) hk hq)
  have second : Γ ⊢[PRAAx] distanceBounded X Y two V :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive q) (unit_positive q)) hV
      (by ipra_le 𝔞(two*unit q)*sl hVq) (cross_at _ _ _ _ q q split)
  have pieces := piece_sources t k z R B A a b source (le_refl _)
  have low := GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ pieces.andE₁
  have high := GaussianEulerCompactAdditivity.name_regular _ _ _ _ _ _ _ pieces.andE₂
  have third : Γ ⊢[PRAAx] distanceBounded Y Z (num 3) V :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive q) hV
      (by unfold GaussianNameRingLaws.three; ipra_le 𝔞(num 3)*sl hVq)
      (GaussianNameRingLaws.add_sample_error C C L U q low high)
  have reg := original_regular_names z R B A a b h
  have raw := GaussianNameRingLaws.add_sample_error lowerF upperF v v t reg.andE₁ reg.andE₂
  have same := GaussianRationalSyntheticDivision.qadd_congr (Γ := Γ) (lower_at t z R B A a b) (upper_at t z R B A a b)
  have last : Γ ⊢[PRAAx] distanceBounded Z S (num 3) V :=
    distance_symmetric _ _ _ _ hV
      (distance_congr (.eqRefl _) same (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _) raw)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same I X S two (two+(num 3+num 3)) V hV first
      (distance_triangle_same X Y S two (num 3+num 3) V hV second
        (distance_triangle_same Y Z S (num 3) (num 3) V hV third last)))

theorem original_improper_sum (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) :
    Γ ⊢[PRAAx] crossEquivalent nameF sumF (GaussianEulerImproperName.data z R B A) (sumData z R B A a b) := by
  have reg := original_regular_names z R B A a b h
  have sumReg := GaussianNameArithmetic.add_fast lowerF upperF _ _ reg.andE₁ reg.andE₂
  apply GaussianNameRingLaws.equivalent_of_envelope nameF sumF
    (GaussianEulerImproperName.data z R B A) (sumData z R B A a b) (num 10)
    (name_regular z R B A (improper_source _ _ _ _ h.andE₁)) sumReg
  unfold GaussianValueNormalizerExtensionality.rawDiagonal
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) := by
    simpa only [Fm.shift, Syn.shift, GaussianEulerIncompleteCofinalRate.subst_source] using h.shift
  simp only [Syn.shift, GaussianEulerImproperName.subst_data, subst_sumData, LeanProofs.IPRA.PTm.subst_num]
  exact original_diagonal_sum (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A) (Syn.shift a) (Syn.shift b) hs

theorem original_Gamma_is_incomplete_sum (z R B A a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A a b) :
    Γ ⊢[PRAAx] crossEquivalent gammaF sumF (gammaData z R B A) (sumData z R B A a b) :=
  cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (original_Euler_integral_is_Gamma z R B A h.andE₁))
    (original_improper_sum z R B A a b h)

theorem actual_original_Gamma_is_incomplete_sum_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        crossEquivalent gammaF sumF (gammaData (var 0) (var 1) (var 2) (var 3))
          (sumData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (original_Gamma_is_incomplete_sum _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteSum
