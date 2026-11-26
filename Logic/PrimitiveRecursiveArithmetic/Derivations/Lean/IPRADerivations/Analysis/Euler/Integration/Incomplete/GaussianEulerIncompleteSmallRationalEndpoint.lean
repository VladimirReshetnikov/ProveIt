import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteLowerPrefixGeometry
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteLowerPrefixSigned
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteRealCompactNonnegative
import IPRADerivations.Analysis.Euler.VerticalBounds.GaussianEulerVerticalCompactInterval
import IPRADerivations.Analysis.Euler.Integration.Incomplete.GaussianEulerIncompleteDyadicEndpoint

/-!
# Uniform zero-endpoint estimates for original incomplete Gamma names

Every positive coded rational split at most the original dyadic cutoff
has the same root-rate bound as the dyadic split itself. Compare the real
projection over a finite prefix to the real whole lower tail. Vertical
domination then bounds the original complex prefix at its own clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteSmallRationalEndpoint

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerVerticalNativeProjection (argument)
open GaussianEulerIncompleteLowerPrefixGeometry (firstData restData wholeData originalData start firstWidth)
open GaussianEulerIncompleteLowerPrefixSigned (extend_bound prefix_bound)
open GaussianEulerCompactAdditivity (nameF name_regular)
open GaussianEulerIncompleteName (lowerF upperF data original_regular_names)
open GaussianGammaIntegralCutoffs (etaDen height top)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerCutoffCauchyComparison (combined)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product qzero qadd)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNameEquivalence (cross_at cross_symm cross_trans)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator)
open GaussianRationalSlackRemoval (precision slack slack_removal_at)
open GaussianNamedPositiveExponentialOrder (scalar_coordinate_distance)
open RationalGaussianEmbedding (scalarZero)
open RationalValueBounds (upper upper_congr upper_mono upper_of_radius)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "Prefix" => GaussianEulerIncompleteLowerPrefixGeometry.source

def source (z R B A k a b : PTm n) : Fm PTm n :=
  GaussianEulerIncompleteCofinalRate.source z R B A a b ⋏ le (a*etaDen k A R) b

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B A k a b : PTm n) :
    (source z R B A k a b).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ A) (Syn.subst σ k) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [source,GaussianEulerIncompleteCofinalRate.source,etaDen,height,GaussianGammaIntegralCutoffs.tailCoefficient]

private theorem fst_zero : Γ ⊢[PRAAx] fstT (qzero : PTm n) ≐ scalarZero :=
  (congrFst RationalGaussianEmbedding.embed_zero.eqSymm).eqTrans
    ((fst_pair _ _).eqTrans RationalGaussianEmbedding.scalar_recode_zero)

private theorem same_query (x y t : PTm n) (h : Γ ⊢[PRAAx] distanceBounded x y (unit t+unit t) (unit t*unit t)) :
    Γ ⊢[PRAAx] upper (fstT x) (fstT y) two (unit t) := by
  have u := unit_positive (Γ := Γ) t
  have dist := distance_radius_mono x y _ _ two (unit t) (positive_product _ _ u u) u
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) h
  exact upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ u dist)

private theorem real_prefix_scaled (t z R B A k j a b : PTm n)
    (h : Γ ⊢[PRAAx] Prefix t (argument z) R B A k j a b) : Γ ⊢[PRAAx]
    upper (fstT (ap2 nameF t (firstData (argument z) R B A k j a b))) (fstT qzero)
      (A*unit t+num 7*unit (height k A R)) (unit (height k A R)*unit t) := by
  let r := argument z
  let X := firstData r R B A k j a b
  let Y := restData r R B A k j a b
  let W := wholeData r R B A k j a b
  let V := GaussianGammaCompactCutoffSplit.lowerData r R B k j A
  let H := unit (height k A R)
  let U := unit t
  have hH := unit_positive (Γ := Γ) (height k A R)
  have hU := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one (H*U) := positive_product _ _ hH hU
  have sources := GaussianEulerIncompleteLowerPrefixGeometry.interval_sources t r R B A k j a b h
  have whole := GaussianEulerIncompleteLowerPrefixGeometry.original_whole_alignment t r R B A k j a b h
  have tail : Γ ⊢[PRAAx] bounded (ap2 nameF t V) (A*U+H) (H*U) :=
    GaussianEulerNamedLowerTail.lower_observation_bound t r R B k j A
      (.andI h.andE₁.andE₁.andE₂.andE₁ h.andE₁.andE₁) h.andE₂.andE₂.andE₂.andE₂.andE₁
  refine .orE (lt_or_eq_of_le h.andE₂.andE₂.andE₂.andE₁) ?_ ?_
  · have add := GaussianEulerIncompleteLowerPrefixGeometry.original_strict_additivity t r R B A k j a b h.wk Prf.hyp0
    have align := cross_trans _ _ _ _ W V (cross_symm _ _ _ _ add) whole.wk
    have nonnegative := GaussianEulerIncompleteRealCompactNonnegative.original_compact_nonnegative
      (Γ := lt (a*etaDen k A R) b :: Γ) t r R B _ _ _ _
      (.andI sources.wk.andE₂.andE₁ (GaussianEulerVerticalNativeProjection.imaginary_zero z))
    exact prefix_bound nameF t X Y V A H hH.wk
      (name_regular r R B _ _ _ _ sources.wk.andE₁) (name_regular r R B _ _ _ _ sources.wk.andE₂.andE₁)
      (GaussianCompactRiemannName.name_canonical GaussianEulerIntegrandName.evaluatorF t _ _ _ _ _ _)
      (upper_congr fst_zero.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) nonnegative) tail.wk align
  · have eq := GaussianEulerIncompleteLowerPrefixGeometry.whole_eq_first
      (Γ := (a*etaDen k A R ≐ b) :: Γ) r R B A k j a b Prf.hyp0
    have align := GaussianGammaCompactCutoffAlignment.cross_data_congr nameF nameF W X V V eq (.eqRefl _) whole.wk
    have first := same_query (ap2 nameF t X) (ap2 nameF t V) t (cross_at _ _ _ _ t t align)
    have last := upper_of_radius (Γ := (a*etaDen k A R ≐ b) :: Γ) _ _ _ _ (scalar_coordinate_distance _ _ _ _ hD.wk
      ((GaussianReconstructionRoots.distance_zero_iff _ _ _ hD.wk).iffMpr tail.wk))
    have small := extend_bound _ _ A H U two one hH.wk hU.wk first
      (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) last)
    exact upper_mono _ _ _ _ _ _ hD.wk small
      (le_of_eq_add (d := num 4*H*(H*U)) (by dsimp only [H,U]; ipra_ring))

theorem original_compact_prefix_bound (t z R B A k j a b : PTm n)
    (h : Γ ⊢[PRAAx] Prefix t z R B A k j a b) : Γ ⊢[PRAAx]
    bounded (ap2 nameF t (originalData z R B A j a b))
      (A*unit t+num 10*unit (height k A R)) (unit (height k A R)*unit t) := by
  let r := argument z
  let U := unit t
  let H := unit (height k A R)
  let C := GaussianEulerIncompleteCutoff.lowerWidth j A R a b
  let E := GaussianEulerIncompleteCutoff.denominator j A R b
  let T := top j A R
  let X := ap2 nameF t (originalData z R B A j a b)
  let Y := ap2 nameF t (originalData r R B A j a b)
  let c := GaussianEulerVerticalCompactInterval.correction t C E T
  have hH := unit_positive (Γ := Γ) (height k A R)
  have hU := unit_positive (Γ := Γ) t
  have hD : Γ ⊢[PRAAx] le one (H*U) := positive_product _ _ hH hU
  have hr : Γ ⊢[PRAAx] Prefix t r R B A k j a b :=
    .andI (.andI (GaussianEulerVerticalNativeProjection.lower_source _ _ _ _ h.andE₁.andE₁) h.andE₁.andE₂) h.andE₂
  have equal := GaussianEulerIncompleteLowerPrefixGeometry.original_first_alignment t r R B A k j a b hr
  have reversed := cross_symm _ _ _ _ equal
  have first := same_query Y (ap2 nameF t (firstData r R B A k j a b)) t (cross_at _ _ _ _ t t reversed)
  have realBound : Γ ⊢[PRAAx] upper (fstT Y) (fstT qzero) (A*U+num 9*H) (H*U) :=
    upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (extend_bound _ _ A H U two (num 7) hH hU first (real_prefix_scaled t z R B A k j a b hr))
  have native := (GaussianEulerIncompleteCutoffParts.piece_sources t j z R B A a b
    (GaussianEulerIncompleteLowerPrefixGeometry.cutoff_source t z R B A k j a b h)
    h.andE₂.andE₂.andE₂.andE₂.andE₂).andE₁
  have hC : Γ ⊢[PRAAx] le C (E*T) := le_trans (le_add_left _ _) native.andE₂.andE₂
  have correction := GaussianEulerVerticalCompactInterval.correction_coordinate t C E T native.andE₁.andE₂.andE₁ hC
  have joined := RationalUpperAddition.add_upper _ _ _ _ _ _ _ _ realBound correction
  have zeroSum : Γ ⊢[PRAAx] RationalArithmetic.add (fstT qzero) (fstT qzero) ≐ scalarZero :=
    (RationalGaussianRealPart.real_add qzero qzero).eqSymm.eqTrans
      ((congrFst (GaussianRationalSyntheticDivision.qzero_add _ GaussianRationalSyntheticDivision.qzero_canonical)).eqTrans fst_zero)
  have realSum := upper_congr (RationalGaussianRealPart.real_add Y c).eqSymm zeroSum (.eqRefl _) (.eqRefl _) joined
  have exactBound : Γ ⊢[PRAAx] upper (fstT (qadd Y c)) scalarZero (A*U+num 10*H) (H*U) :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hD hU) realSum
      (le_congr (.eqRefl _) (by dsimp only [U,H]; ipra_ring) (le_refl _))
  have lower := GaussianPositiveRadiusFiniteSum.enlarge_radius X (qadd Y c) scalarZero zero one _ _
    (GaussianEulerVerticalCompactInterval.original_bound t z R B b C E T native)
    (le_refl one) hD (RationalGaussianEmbedding.scalar_zero_represents one) exactBound
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ (le_refl one) hD) hD (le_congr (.eqRefl _) (by ipra_ring) (le_refl _)) lower

private theorem lower_slack (p t z R B A k a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A k a b) :
    Γ ⊢[PRAAx] slack (ap2 lowerF p (data z R B A a b))
      (A*unit p+unit (height k A R)) (unit (height k A R)*unit p) (num 12) t := by
  let P := unit p
  let U := unit t
  let H := unit (height k A R)
  let C := GaussianEulerIncompleteCutoff.clock t a b
  let j := k+C
  let J := unit (height j A R)
  let K := combined A R
  let D := H*P*U
  let V := ap2 lowerF p (data z R B A a b)
  let X := ap2 nameF t (originalData z R B A j a b)
  have hP := unit_positive (Γ := Γ) p
  have hU := unit_positive (Γ := Γ) t
  have hH := unit_positive (Γ := Γ) (height k A R)
  have hJ := unit_positive (Γ := Γ) (height j A R)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hH hP) hU
  have hj : Γ ⊢[PRAAx] le C j := le_add_left _ _
  have later := le_trans (GaussianEulerIncompleteCutoff.clock_later (Γ := Γ) t a b) hj
  have budget := GaussianEulerIncompleteCofinalRate.cutoff_budget t j A R later
  have lc : Γ ⊢[PRAAx] le t (GaussianEulerCutoffCauchyComparison.clock t) := le_add_right _ _
  have tail : Γ ⊢[PRAAx] le (K*U) J :=
    le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl K) (GaussianExponentialReference.unit_monotone lc)) budget
  have rates := GaussianEulerIncompleteFixedCutoff.original_cutoff_rates t j z R B A a b (.andI h.andE₁ hj)
  have first : Γ ⊢[PRAAx] distanceBounded V X ((U+two*P)*H) D :=
    distance_radius_mono _ _ _ _ _ _ (GaussianNamedInverseRate.denominator_positive J p t hJ) hD
      (by dsimp only [D,P,U,K,H,J,rateNumerator,rateDenominator]
          ipra_le (𝔞(unit (height k A R))*𝔞(unit p)*𝔞(unit p)*𝔞(unit t))*sl tail)
      (rate_at _ _ _ _ _ _ p t rates.andE₁)
  have prefixSource : Γ ⊢[PRAAx] Prefix t z R B A k j a b :=
    .andI h.andE₁.andE₁ (.andI h.andE₁.andE₂.andE₁
      (.andI h.andE₁.andE₂.andE₂ (.andI h.andE₂ (.andI (le_add_right _ _) hj))))
  have td : Γ ⊢[PRAAx] le one (H*U) := positive_product _ _ hH hU
  have last : Γ ⊢[PRAAx] distanceBounded X qzero ((A*U+num 10*H)*P) D :=
    distance_radius_mono _ _ _ _ _ _ td hD
      (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      ((GaussianReconstructionRoots.distance_zero_iff _ _ _ td).iffMpr (original_compact_prefix_bound t z R B A k j a b prefixSource))
  have total := distance_triangle_same V X qzero _ _ D hD first last
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hD).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [P,U,H,unit]; ipra_ring) (.eqRefl _) total)

theorem original_lower_small_rational_bound (p z R B A k a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A k a b) :
    Γ ⊢[PRAAx] bounded (ap2 lowerF p (data z R B A a b))
      (A*unit p+unit (height k A R)) (unit (height k A R)*unit p) := by
  let V := ap2 lowerF p (data z R B A a b)
  let N := A*unit p+unit (height k A R)
  let D := unit (height k A R)*unit p
  let t := precision V N D (num 12)
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive _) (unit_positive _)
  exact slack_removal_at V N D (num 12) hD (lower_slack p t z R B A k a b h)

theorem original_upper_small_rational_rate (z R B A k a b : PTm n) (h : Γ ⊢[PRAAx] source z R B A k a b) :
    Γ ⊢[PRAAx] independentRate upperF gammaF (data z R B A a b) (gammaData z R B A) A (unit (height k A R)) := by
  apply GaussianNamedLipschitzRate.independent_rate upperF gammaF (data z R B A a b) (gammaData z R B A)
    A (unit (height k A R)) (num 6) (unit_positive _) (original_regular_names z R B A a b h.andE₁).andE₂
    (GaussianEulerIntegralGammaIdentification.original_gamma_regular z R B A h.andE₁.andE₁)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift A)
      (Syn.shift k) (Syn.shift a) (Syn.shift b) := by simpa only [Fm.shift,Syn.shift,subst_source] using h.shift
  have lower := original_lower_small_rational_bound (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B)
    (Syn.shift A) (Syn.shift k) (Syn.shift a) (Syn.shift b) hs
  simpa [GaussianNamedLipschitzRate.diagonalEnvelope, Syn.shift, height, GaussianGammaIntegralCutoffs.tailCoefficient] using
    GaussianEulerIncompleteDyadicEndpoint.original_upper_diagonal_of_lower (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B)
      (Syn.shift A) (Syn.shift a) (Syn.shift b) (unit (height (Syn.shift k) (Syn.shift A) (Syn.shift R)))
      hs.andE₁ (unit_positive _) lower

theorem actual_original_lower_incomplete_small_rational_bound_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶ bounded
        (ap2 lowerF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 6) (var 7)))
        (var 4*unit (var 0)+unit (height (var 5) (var 4) (var 2))) (unit (height (var 5) (var 4) (var 2))*unit (var 0))) :=
  closeUniv 8 (.impI (original_lower_small_rational_bound _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_upper_incomplete_small_rational_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) ⟶ independentRate upperF gammaF
        (data (var 0) (var 1) (var 2) (var 3) (var 5) (var 6)) (gammaData (var 0) (var 1) (var 2) (var 3))
        (var 3) (unit (height (var 4) (var 3) (var 1)))) :=
  closeUniv 7 (.impI (original_upper_small_rational_rate _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteSmallRationalEndpoint
