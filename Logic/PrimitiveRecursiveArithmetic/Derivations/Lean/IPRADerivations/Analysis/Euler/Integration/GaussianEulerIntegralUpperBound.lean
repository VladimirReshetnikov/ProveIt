import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.EtaToOne.GaussianEulerEtaToOneBound
import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.Bounds.GaussianEulerUnitToTopCompactBound
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegralUpperTransfer

/-!
# The original Euler integral and Gamma are bounded by A + D_R

At each original cutoff, compact additivity splits at time one. The bound
on the low panel uses its own containing top guard; a common refinement
compares that observation to the one used by the split. The two panel
bounds then give an upper bound on each actual original compact sampler.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegralUpperBound

open_ipra
open GaussianEulerCompactAdditivity (intervalSource data nameF)
open GaussianEulerIntegralUpperTransfer (compactObservation compactUpper paperConstant)
open GaussianEulerEtaToOneBound (width)
open GaussianGammaIntegralCutoffs (height etaDen top tailCoefficient)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalSlackRemoval (slack slack_removal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private def upperWidth (k A R : PTm n) : PTm n := etaDen k A R*monus (top k A R) one

private theorem split_geometry (k A R : PTm n) : Γ ⊢[PRAAx]
    (one+width k A R ≐ etaDen k A R) ⋏
      (etaDen k A R+upperWidth k A R ≐ etaDen k A R*top k A R) ⋏
      (width k A R+upperWidth k A R ≐ GaussianGammaCompactQuadratureBoundary.width k A R) ⋏
      le one (upperWidth k A R) := by
  let E := etaDen k A R
  let T := top k A R
  let C := upperWidth k A R
  have hE : Γ ⊢[PRAAx] le one E := GaussianGammaIntegralCutoffs.eta_den_positive k A R
  have hT : Γ ⊢[PRAAx] le one T := GaussianGammaIntegralCutoffs.top_positive k A R
  have left : Γ ⊢[PRAAx] one+width k A R ≐ E := (eq_add_of_le hE).eqSymm
  have topSplit : Γ ⊢[PRAAx] one+monus T one ≐ T := (eq_add_of_le hT).eqSymm
  have right : Γ ⊢[PRAAx] E+C ≐ E*T :=
    (show Γ ⊢[PRAAx] E+C ≐ E*(one+monus T one) by dsimp only [C,upperWidth]; ipra_ring).eqTrans
      (congrMul (.eqRefl E) topSplit)
  have whole : Γ ⊢[PRAAx] width k A R+C ≐ GaussianGammaCompactQuadratureBoundary.width k A R := by
    apply add_left_cancel (a := one)
    exact (show Γ ⊢[PRAAx] one+(width k A R+C) ≐ (one+width k A R)+C by ipra_ring).eqTrans
      ((congrAdd left (.eqRefl C)).eqTrans (right.eqTrans (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k A R).eqSymm))
  have hTwo : Γ ⊢[PRAAx] le two T :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] one*two ≐ two) (LeanProofs.IPRA.mul_comm _ _)
      (LeanProofs.IPRA.mul_le_mul_right two (GaussianGammaIntegralCutoffs.height_positive k A R))
  have hRest : Γ ⊢[PRAAx] le one (monus T one) := by
    apply LeanProofs.IPRA.le_of_add_le_add_right (c := one)
    exact le_congr (by ipra_ring : Γ ⊢[PRAAx] two ≐ one+one)
      (topSplit.eqSymm.eqTrans (LeanProofs.IPRA.add_comm _ _)) hTwo
  exact .andI left (.andI right (.andI whole (positive_product _ _ hE hRest)))

private theorem observation_congr (s z R B a a' C C' E T : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hC : Γ ⊢[PRAAx] C ≐ C') : Γ ⊢[PRAAx]
    ap2 nameF s (data z R B a C E T) ≐ ap2 nameF s (data z R B a' C' E T) := by
  apply congrAp2 nameF (.eqRefl s)
  unfold data GaussianCompactRiemannName.data GaussianCompactRiemannName.sampleData
  have pair_congr {u u' v v' : PTm n} (hu : Γ ⊢[PRAAx] u ≐ u') (hv : Γ ⊢[PRAAx] v ≐ v') :
      Γ ⊢[PRAAx] pairT u v ≐ pairT u' v' :=
    congrAdd (congrMul (congrAdd hu hv) (congrAdd hu hv)) hu
  exact pair_congr ha (pair_congr hC (.eqRefl _))

private theorem lower_panel_bound (s z R B k A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A)
    (hTop : Γ ⊢[PRAAx] intervalSource z R B one (width k A R) (etaDen k A R) (top k A R)) : Γ ⊢[PRAAx]
    bounded (ap2 nameF s (data z R B one (width k A R) (etaDen k A R) (top k A R)))
      (A*unit s+num 3) (unit s) := by
  let U := unit s
  let V := unit (s+num 6)
  have hU := unit_positive (Γ := Γ) s
  have guard := GaussianEulerUnitToTopCompactBound.original_guard_distance s z R B one (width k A R) (etaDen k A R)
    (top k A R) one hTop (GaussianEulerEtaToOneBound.interval_source z R B k A h)
  have cost : Γ ⊢[PRAAx] le (num 6*U) (two*V) :=
    le_congr (by ipra_ring : Γ ⊢[PRAAx] (num 3*U)*two ≐ num 6*U) (LeanProofs.IPRA.mul_comm _ _)
      (LeanProofs.IPRA.mul_le_mul_right two (GaussianCompactRiemannName.dyadic_six_lower s))
  have near := distance_radius_mono _ _ _ _ _ _ (unit_positive _) hU cost guard
  have norm := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hU hU near
    (GaussianEulerEtaToOneBound.original_observation_bound s z R B k A h)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ hU hU) hU
    (le_congr (by ipra_ring) (.eqRefl _) (le_refl _)) norm

private theorem split_sum_bound (s z R B k A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    bounded (ap2 (GaussianNameArithmetic.addF nameF nameF) s
      (GaussianEulerCompactAdditivity.addedData z R B one (width k A R) (upperWidth k A R) (etaDen k A R) (top k A R)))
      (paperConstant A R*unit s+num 4) (unit s) := by
  let E := etaDen k A R
  let T := top k A R
  let L := width k A R
  let C := upperWidth k A R
  let x := data z R B one L E T
  let y := data z R B (one+L) C E T
  let u := GaussianFastValueCut.exponent two s
  let U := unit s
  let V := unit u
  have geometry := split_geometry (Γ := Γ) k A R
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have hT := GaussianGammaIntegralCutoffs.top_positive (Γ := Γ) k A R
  have common : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E :=
    .andI h.andE₂.andE₁.andE₁ (.andI hE h.andE₂.andE₁.andE₂)
  have lowerEnd : Γ ⊢[PRAAx] E*one ≐ one+L :=
    (show Γ ⊢[PRAAx] E*one ≐ E by ipra_ring).eqTrans geometry.andE₁.eqSymm
  have hLow : Γ ⊢[PRAAx] intervalSource z R B one L E T :=
    .andI common (.andI (le_refl _) (le_congr lowerEnd (.eqRefl _)
      (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl E) hT)))
  have hHigh : Γ ⊢[PRAAx] intervalSource z R B E C E T :=
    .andI common (.andI hE (le_congr (.eqRefl _) geometry.andE₂.andE₁ (le_refl _)))
  have low := lower_panel_bound u z R B k A h hLow
  have high := bound_congr (observation_congr u z R B E (one+L) C C E T geometry.andE₁.eqSymm (.eqRefl C))
    (.eqRefl _) (.eqRefl _) (GaussianEulerUnitToTopCompactBound.original_observation_bound u z R B C E T hHigh geometry.andE₂.andE₂.andE₂)
  have hv := unit_positive (Γ := Γ) u
  have hu := unit_positive (Γ := Γ) s
  have both := bounded_sum (ap2 nameF u x) (ap2 nameF u y) _ _ _ _ hv hv low high
  have budget : Γ ⊢[PRAAx] bounded (GaussianNameArithmetic.addRaw nameF nameF u x y)
      (paperConstant A R*V+num 4) V :=
    bounded_radius_mono _ _ _ _ _ (positive_product _ _ hv hv) hv
      (le_congr (by dsimp only [paperConstant,V]; ipra_ring) (.eqRefl _) (le_refl _)) both
  have recoded := (GaussianFastValueCut.recode_bound_iff _ _ _ hv).iffMpr budget
  have queried := bound_congr (GaussianNameArithmetic.add_at nameF nameF x y s).eqSymm (.eqRefl _) (.eqRefl _) recoded
  have clock : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone (le_add_right s _)
  exact bounded_radius_mono _ _ _ _ _ hv hu (by ipra_le 4*sl clock) queried

private theorem original_compact_slack (p s k z R B A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    slack (compactObservation p k z R B A) (paperConstant A R*unit p+one) (unit p) (num 5) s := by
  let E := etaDen k A R
  let T := top k A R
  let C := upperWidth k A R
  let L := width k A R
  have geom := split_geometry (Γ := Γ) k A R
  have hE := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have common : Γ ⊢[PRAAx] GaussianEulerExponentCompactBounds.source z R B E :=
    .andI h.andE₂.andE₁.andE₁ (.andI hE h.andE₂.andE₁.andE₂)
  have endpoint : Γ ⊢[PRAAx] one+(L+C) ≐ E*T :=
    (congrAdd (.eqRefl one) geom.andE₂.andE₂.andE₁).eqTrans (GaussianGammaCompactQuadratureBoundary.exact_right_endpoint k A R)
  have split : Γ ⊢[PRAAx] GaussianEulerCompactAdditivity.source z R B one L C E T :=
    .andI (.andI common (.andI (le_refl one) (le_congr (.eqRefl _) endpoint (le_refl _))))
      (.andI (GaussianEulerEtaToOneBound.width_positive k A R h.andE₁) geom.andE₂.andE₂.andE₂)
  have near := distance_congr (observation_congr p z R B one one (L+C) _ E T (.eqRefl one) geom.andE₂.andE₂.andE₁)
    (.eqRefl _) (.eqRefl _) (.eqRefl _) (GaussianEulerCompactAdditivity.observations p s z R B one L C E T split)
  have den := positive_product _ _ (unit_positive (Γ := Γ) p) (unit_positive s)
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ den (unit_positive s)
    near (split_sum_bound s z R B k A h)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ den (unit_positive s)) den
    (le_congr (by unfold unit; ipra_ring) (.eqRefl _) (le_refl _)) raw

theorem original_compact_bound (p k z R B A : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    bounded (compactObservation p k z R B A) (paperConstant A R*unit p+one) (unit p) :=
  slack_removal_at _ _ _ (num 5) (unit_positive p) (original_compact_slack p _ k z R B A h)

theorem compact_upper (z R B A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    compactUpper z R B A (paperConstant A R) := by
  refine .allI (.allI ?_)
  simpa only [compactUpper,GaussianEulerIntegralUpperTransfer.subst_paperConstant,Syn.shift] using
    original_compact_bound (var 0) (var 1) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift A)) (by simpa [Fm.shift,Syn.shift] using h.shift.shift)

theorem original_improper_bound (p z R B A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    bounded (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data z R B A))
      (paperConstant A R*unit p+one) (unit p) :=
  GaussianEulerIntegralUpperTransfer.original_improper_A_D_R p z R B A (compact_upper z R B A h)

theorem original_gamma_bound (p z R B A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerIntegralGammaIdentification.source z R B A) : Γ ⊢[PRAAx]
    bounded (ap2 GaussianGammaReciprocalInverse.gammaF p (GaussianGammaReciprocalInverse.gammaData z R B A))
      (paperConstant A R*unit p+one) (unit p) :=
  GaussianEulerIntegralUpperTransfer.original_gamma_A_D_R p z R B A h (compact_upper z R B A h.andE₁)

theorem original_Euler_integral_A_D_R_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianEulerLowerPowerCoefficients.source (var 1) (var 2) (var 3) (var 4) ⟶
      bounded (ap2 GaussianEulerImproperName.nameF (var 0) (GaussianEulerImproperName.data (var 1) (var 2) (var 3) (var 4)))
        (paperConstant (var 4) (var 2)*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 5 (.impI (original_improper_bound _ _ _ _ _ Prf.hyp0))

theorem original_Gamma_A_D_R_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (GaussianEulerIntegralGammaIdentification.source (var 1) (var 2) (var 3) (var 4) ⟶
      bounded (ap2 GaussianGammaReciprocalInverse.gammaF (var 0)
        (GaussianGammaReciprocalInverse.gammaData (var 1) (var 2) (var 3) (var 4)))
        (paperConstant (var 4) (var 2)*unit (var 0)+one) (unit (var 0))) :=
  closeUniv 5 (.impI (original_gamma_bound _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegralUpperBound
