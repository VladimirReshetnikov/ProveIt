import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.EtaToOne.GaussianEulerEtaToOneQuadratureBound
import IPRADerivations.Analysis.Euler.CompactExhaustion.Tails.GaussianEulerNamedLowerTail

/-!
# The actual original eta-to-one Euler compact name has radius A

The literal transformed root quadrature is compared to the unchanged
compact name. Its leading weighted radius is at most A and its mesh
and observation residuals vanish on the genuine cofinal schedule.
One finite rational gap leaves A plus the requested observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerEtaToOneBound

open_ipra
open GaussianEulerEtaToOneRootGrid (rootDen time timeDen totalWidth)
open GaussianEulerEtaToOneRowBound (stepScale)
open GaussianEulerLowerCofinalQuadrature (rootMesh transformed)
open GaussianEulerLowerTailFiniteBudget (residual oldNumerator oldDenominator)
open GaussianGammaIntegralCutoffs (height etaDen)
open GaussianEulerIntegrandName (evaluatorF fixedData)
open GaussianEulerCompactModulus (lipschitz)
open GaussianCompactRiemannName (sampledModulus sampled_modulus_congr quadrature quadrature_congr precision)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_symmetric)
open GaussianRationalSlackRemoval (slack slack_removal_at)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def width (k A R : PTm n) : PTm n := monus (etaDen k A R) one
def data (z R B k A : PTm n) : PTm n := GaussianEulerCompactAdditivity.data z R B one (width k A R) (etaDen k A R) one
def point (s z R B k A : PTm n) : PTm n := ap2 GaussianEulerCompactAdditivity.nameF s (data z R B k A)
def result (s z R B k A : PTm n) : Fm PTm n := bounded (point s z R B k A) (A*unit s+one) (unit s)
ipra_subst width [etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst data [etaDen, height, GaussianGammaIntegralCutoffs.tailCoefficient]
ipra_subst point
ipra_subst result

theorem width_positive (k A R : PTm n) (hA : Γ ⊢[PRAAx] le one A) : Γ ⊢[PRAAx] le one (width k A R) := by
  have hp := positive_product (Γ := Γ) A (height k A R) hA (GaussianGammaIntegralCutoffs.height_positive k A R)
  have hg : Γ ⊢[PRAAx] le two (etaDen k A R) := le_congr (pw_one two) (.eqRefl _) (GaussianExponentialReference.unit_monotone hp)
  have split := natEq (eq_add_of_le (GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R))
  unfold width
  ipra_le sl hg using linear_combination -split

theorem interval_source (z R B k A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    GaussianEulerCompactAdditivity.intervalSource z R B one (width k A R) (etaDen k A R) one := by
  have he := GaussianGammaIntegralCutoffs.eta_den_positive (Γ := Γ) k A R
  have endpoint : Γ ⊢[PRAAx] one+width k A R ≐ etaDen k A R := (eq_add_of_le he).eqSymm
  exact .andI (.andI h.andE₂.andE₁.andE₁ (.andI he h.andE₂.andE₁.andE₂))
    (.andI (le_refl one) (le_congr endpoint.eqSymm (by ipra_ring : Γ ⊢[PRAAx] etaDen k A R ≐ etaDen k A R*one) (le_refl _)))

theorem finite_source (z R B H k e : PTm n) (hH : Γ ⊢[PRAAx] le one H)
    (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ e)) : Γ ⊢[PRAAx]
    GaussianEulerEtaToOneQuadratureBound.source z R B H k e (lipschitz R (etaDen k (succ e) R) one) := by
  let A := succ e
  let E := etaDen k A R
  let C := width k A R
  let L := lipschitz R E one
  let K := pw H A
  let x := fixedData z B
  have old := GaussianEulerCompactAdditivity.compact_input z R B one C E one (interval_source z R B k A h)
  have hK := GaussianPolynomialPerturbation.power_positive (Γ := Γ) H A hH
  have hW : Γ ⊢[PRAAx] le one (totalWidth H k A R) := le_congr (.eqRefl _)
    (GaussianEulerEtaToOneRootGrid.exact_width H k A R).eqSymm (positive_product _ _ (width_positive k A R h.andE₁) hK)
  have mod := GaussianCompactIntervalRescaling.rescaled_modulus evaluatorF K one C E L x hK old.andE₂.andE₂.andE₂
  have ha : Γ ⊢[PRAAx] K*one ≐ time zero H k A R := (by ipra_ring : Γ ⊢[PRAAx] K*one ≐ K).eqTrans (GaussianEulerEtaToOneRootGrid.first_time H k A R).eqSymm
  have hc : Γ ⊢[PRAAx] K*C ≐ totalWidth H k A R := (mul_comm _ _).eqTrans (GaussianEulerEtaToOneRootGrid.exact_width H k A R).eqSymm
  have he : Γ ⊢[PRAAx] K*E ≐ timeDen H k A R := (mul_comm _ _).eqTrans (GaussianEulerEtaToOneRootGrid.exact_denominator H k A R).eqSymm
  exact .andI hH (.andI hW (.andI h (sampled_modulus_congr ha hc he (.eqRefl _) (.eqRefl _) mod)))

theorem finite_radius_conversion (x s t H k e R L : PTm n)
    (hH : Γ ⊢[PRAAx] le (unit t) H) (hP : Γ ⊢[PRAAx] le (unit t) (unit s))
    (hx : Γ ⊢[PRAAx] bounded x (oldNumerator H (rootDen H k (succ e) R) (stepScale k e R) L (unit s))
      (oldDenominator (rootDen H k (succ e) R) (unit s))) : Γ ⊢[PRAAx]
    bounded x (succ e*unit t+residual (stepScale k e R) L) (unit t) := by
  let D := rootDen H k (succ e) R
  let S := stepScale k e R
  have hHD : Γ ⊢[PRAAx] le H D := GaussianEulerLowerTailFiniteBudget.root_denominator_ge H k e R
  have hD := le_trans (le_trans (unit_positive t) hH) hHD
  have smaller := mul_le_mul_right (succ e*H)
    (GaussianMonicResidualRadius.monus_le_left (Γ := Γ) (GaussianEulerLowerTailRootGrid.rootRatio zero (height k (succ e) R)) one)
  have leading : Γ ⊢[PRAAx] le (H*S*one) (succ e*D) := le_congr
    (by dsimp only [S,stepScale,GaussianEulerEtaToOneRowBound.rootStep,GaussianEulerLowerTailPartition.rootStep]; ipra_ring)
    ((by ipra_ring : Γ ⊢[PRAAx] GaussianEulerLowerTailRootGrid.rootRatio zero (height k (succ e) R)*(succ e*H) ≐ succ e*(GaussianEulerLowerTailRootGrid.rootRatio zero (height k (succ e) R)*H)).eqTrans
      (congrMul (.eqRefl _) (congrMul (GaussianEulerEtaToOneRootGrid.exact_ratio k (succ e) R) (.eqRefl H)))) smaller
  have mesh : Γ ⊢[PRAAx] le (H*unit t) (D*D) := AnalyticNumberTheory.PhiLower.le_mul_mono hHD (le_trans hH hHD)
  have obs : Γ ⊢[PRAAx] le (H*unit t) (D*unit s) := AnalyticNumberTheory.PhiLower.le_mul_mono hHD hP
  have raw := GaussianEulerLowerTailFiniteBudget.point_radius_conversion x H D S L (unit s) (succ e) one (unit t)
    hD (unit_positive s) (le_refl one) (unit_positive t) leading mesh obs hx
  exact bound_congr (.eqRefl _) (by unfold GaussianEulerLowerTailFiniteBudget.nativeNumerator; ipra_ring)
    (by unfold GaussianEulerLowerTailFiniteBudget.nativeDenominator; ipra_ring) raw

theorem cofinal_bound (t z R B k e : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ e)) : Γ ⊢[PRAAx]
    bounded (transformed evaluatorF t (succ e) (width k (succ e) R) (etaDen k (succ e) R)
      (lipschitz R (etaDen k (succ e) R) one) one (fixedData z B))
      (succ e*unit t+residual (stepScale k e R) (lipschitz R (etaDen k (succ e) R) one)) (unit t) := by
  let A := succ e
  let C := width k A R
  let E := etaDen k A R
  let L := lipschitz R E one
  let H := rootMesh t L one
  let s := precision t one
  let y := GaussianEulerEtaToOneQuadratureBound.originalQuadrature s z R B H k e
  let b := transformed evaluatorF t A C E L one (fixedData z B)
  have hH := GaussianEulerLowerCofinalQuadrature.root_mesh_positive (Γ := Γ) t L one
  have raw := GaussianEulerEtaToOneQuadratureBound.original_finite_bound s z R B H k e L (finite_source z R B H k e hH h)
  have hHT : Γ ⊢[PRAAx] le (unit t) H := le_congr (one_mul _) (mul_comm _ _)
    (mul_le_mul_right (unit t) (GaussianCompactRiemannName.mesh_positive t L one))
  have hP : Γ ⊢[PRAAx] le (unit t) (unit s) := GaussianExponentialReference.unit_monotone (le_trans (le_add_right t one) (le_add_right _ _))
  have norm := finite_radius_conversion y s t H k e R L hHT hP
    (bound_congr (.eqRefl _) (by unfold oldNumerator GaussianEulerLowerBlockWeight.numerator; ipra_ring) (.eqRefl _) raw)
  have eq : Γ ⊢[PRAAx] y ≐ b := quadrature_congr evaluatorF (.eqRefl s)
    (GaussianEulerEtaToOneRootGrid.exact_width H k A R) (GaussianEulerEtaToOneRootGrid.first_time H k A R)
    (GaussianEulerEtaToOneRootGrid.exact_width H k A R) (GaussianEulerEtaToOneRootGrid.exact_denominator H k A R)
    (.eqRefl _)
  exact bound_congr eq (.eqRefl _) (.eqRefl _) norm

theorem cofinal_observations (t s z R B k A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (transformed evaluatorF t A (width k A R) (etaDen k A R) (lipschitz R (etaDen k A R) one) one (fixedData z B))
      (point s z R B k A) (two*unit s+unit t) (unit t*unit s) := by
  have old := GaussianEulerCompactAdditivity.compact_input z R B one (width k A R) (etaDen k A R) one (interval_source z R B k A h)
  have actual := GaussianEulerLowerCofinalQuadrature.observations evaluatorF t s A (width k A R) (etaDen k A R)
    (lipschitz R (etaDen k A R) one) one (fixedData z B) (.andI h.andE₁ (.andI (width_positive k A R h.andE₁) old))
  exact distance_congr (.eqRefl _) (GaussianCompactRiemannName.name_at _ _ _ _ _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) actual

theorem original_slack (s t z R B k e : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ e)) : Γ ⊢[PRAAx]
    slack (point s z R B k (succ e)) (succ e*unit s+one) (unit s)
      (residual (stepScale k e R) (lipschitz R (etaDen k (succ e) R) one)+two) t := by
  have hd := cofinal_observations t s z R B k (succ e) h
  have den := positive_product (Γ := Γ) _ _ (unit_positive t) (unit_positive s)
  have bound := cofinal_bound t z R B k e h
  have shaped := bound_congr (.eqRefl _)
    (by ipra_ring : Γ ⊢[PRAAx] succ e*unit t+residual (stepScale k e R) (lipschitz R (etaDen k (succ e) R) one) ≐
      succ e*unit t+residual (stepScale k e R) (lipschitz R (etaDen k (succ e) R) one)*one)
    (by ipra_ring : Γ ⊢[PRAAx] unit t ≐ one*unit t) bound
  have raw := GaussianEulerNamedLowerTail.compared_bound_to_slack _ _ (succ e) one _ s t (le_refl one)
    (distance_symmetric _ _ _ _ den hd) shaped
  exact bound_congr (.eqRefl _) (by unfold unit; ipra_ring) (by unfold unit; ipra_ring) raw

theorem successor_bound (s z R B k e : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ e)) : Γ ⊢[PRAAx]
    result s z R B k (succ e) := by
  let K := residual (stepScale k e R) (lipschitz R (etaDen k (succ e) R) one)+two
  let t := GaussianRationalSlackRemoval.precision (point s z R B k (succ e)) (succ e*unit s+one) (unit s) K
  exact slack_removal_at _ _ _ K (unit_positive s) (original_slack s t z R B k e h)

theorem original_observation_bound (s z R B k A : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B A) : Γ ⊢[PRAAx]
    result s z R B k A := by
  let e := monus A one
  let φ := GaussianEulerLowerPowerCoefficients.source (Syn.shift z) (Syn.shift R) (Syn.shift B) (var 0) ⟶
    result (Syn.shift s) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift k) (var 0)
  have eq : Γ ⊢[PRAAx] succ e ≐ A := (GaussianCompactRiemannName.positive_as_successor A h.andE₁).eqSymm
  have rule : Γ ⊢[PRAAx] GaussianEulerLowerPowerCoefficients.source z R B (succ e) ⟶ result s z R B k (succ e) :=
    .impI (successor_bound s z R B k e Prf.hyp0)
  have moved := Prf.eqSubst1 φ eq (by simpa [φ] using rule)
  exact .impE (by simpa [φ] using moved) h

theorem actual_original_eta_to_one_compact_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianEulerLowerPowerCoefficients.source (var 1) (var 2) (var 3) (var 5) ⟶ result (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)) :=
  closeUniv 6 (.impI (original_observation_bound _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerEtaToOneBound
