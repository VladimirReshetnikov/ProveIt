import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianEulerPowerShiftRate
import IPRADerivations.Analysis.Exponential.Estimates.GaussianExponentialLinearRemainder
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaFoldedApproximantBalance

/-!
# The original Euler power after a linear exponent displacement

The original power at the later time is compared to the product of
the earlier original power and the original radius-one exponential
of its exact linear increment. The compact radius controls the
exponential amplification, and the radius changes retain their
actual cofinal equivalences.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPowerExponentialShift

open_ipra
open GaussianEulerPowerShiftRate (source radius shiftedF shiftedData numerator)
open GaussianEulerPowerExponentIncrement (linear linear_bound)
open GaussianEulerIntegrandName (powerExponentF powerExponentData powerRadius powerF powerData)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianRationalHorner (qadd qmul_canonical positive_product)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_refl cross_diagonal_at)
open GaussianRadiusExponentialName (boundedSamples)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def relativeF : PR 2 := GaussianRadiusExponentialName.nameF constantF
def relativeData (z B a c : PTm n) : PTm n := GaussianRadiusExponentialName.data one (linear z B a c)
def productF : PR 2 := multiplyF powerF relativeF
def productData (z B a b c : PTm n) : PTm n := multiplyData powerF relativeF (powerData z B a b) (relativeData z B a c)
def coefficient (R E T c : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (radius R E T)*numerator R c

ipra_subst relativeData
ipra_subst productData
ipra_subst coefficient

theorem relative_input (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF one (linear z B a c) := by
  refine .andI (constant_regular _) (.allI ?_)
  have hb : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift (linear z B a c)) one one :=
    by simpa [Fm.shift,Syn.shift] using (GaussianEulerPowerShiftRate.unit_bound z R B E T a b c h).shift
  simpa only [boundedSamples,Syn.shift,one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using
    bound_congr (constant_at (var 0) (Syn.shift (linear z B a c))).eqSymm (.eqRefl one) (.eqRefl one) hb

theorem product_cross (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] crossEquivalent productF (GaussianRadiusExponentialName.nameF shiftedF)
      (productData z B a b c) (GaussianRadiusExponentialName.data (radius R E T) (shiftedData z B a b c)) := by
  have old := GaussianEulerIntegrandName.power_input z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁.andE₁)
  have rel := relative_input z R B E T a b c h
  have sh := GaussianEulerPowerShiftRate.shifted_input z R B E T a b c h
  exact GaussianGammaFoldedApproximantBalance.exponential_product_equivalent powerExponentF constantF shiftedF
    (powerRadius z B a b) one (radius R E T) (powerExponentData z B a b) (linear z B a c)
    (shiftedData z B a b c) old rel sh (cross_refl _ _ sh.andE₁)

theorem original_product_envelope (p z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] distanceBounded (ap2 powerF p (powerData z B (a+c) b))
      (ap2 productF p (productData z B a b c))
      (diagonalNumerator (coefficient R E T c) (a*a) (num 6) p) (diagonalDenominator (a*a) p) := by
  let P := unit p
  let D := (a*a)*P
  let C := coefficient R E T c
  let X := powerData z B (a+c) b
  let F := GaussianRadiusExponentialName.nameF shiftedF
  let Y := GaussianRadiusExponentialName.data (radius R E T) (powerExponentData z B (a+c) b)
  let Z := GaussianRadiusExponentialName.data (radius R E T) (shiftedData z B a b c)
  let W := productData z B a b c
  have ha := h.andE₂.andE₁.andE₁.andE₁
  have haa := positive_product a a ha ha
  have hp := unit_positive (Γ := Γ) p
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ haa hp
  have old := GaussianEulerIntegrandName.power_input z B (a+c) b
    (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  have late := GaussianEulerPowerShiftRate.later_input z R B E T a b c h
  have near := GaussianExponentialRadiusIndependence.same_input_cross powerExponentF
    (powerRadius z B (a+c) b) (radius R E T) (powerExponentData z B (a+c) b) old late
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 powerF p X) (ap2 powerF p Y) two P :=
    cross_diagonal_at p near
  have third : Γ ⊢[PRAAx] distanceBounded (ap2 F p Z) (ap2 productF p W) two P :=
    cross_diagonal_at p (cross_symm _ _ _ _ (product_cross z R B E T a b c h))
  have middle := GaussianRadiusExponentialLipschitzRate.observations powerExponentF shiftedF (radius R E T)
    (powerExponentData z B (a+c) b) (shiftedData z B a b c) (numerator R c) (a*a) p p
    (GaussianEulerPowerShiftRate.original_exponential_comparison_input z R B E T a b c h)
  have oneStep := distance_radius_mono _ _ _ _ (two*(a*a)) D hp hd
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) first
  have twoStep := distance_radius_mono _ _ _ _ (C*P+two*(a*a)) D
    (GaussianNamedInverseRate.denominator_positive (a*a) p p haa) hd
    (le_of_eq_add (d := zero) (by dsimp only [P,D,C,coefficient,rateNumerator,rateDenominator]; ipra_ring)) middle
  have threeStep := distance_radius_mono _ _ _ _ (two*(a*a)) D hp hd
    (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring)) third
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [P,C,diagonalNumerator]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd oneStep twoStep) threeStep)

theorem original_power_product_rate (z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] independentRate powerF productF (powerData z B (a+c) b) (productData z B a b c)
      (coefficient R E T c) (a*a) := by
  have earlier := GaussianEulerIntegrandName.power_regular z B a b (.andI h.andE₁.andE₁ h.andE₂.andE₁.andE₁)
  have later := GaussianEulerIntegrandName.power_regular z B (a+c) b (.andI h.andE₁.andE₁ h.andE₂.andE₂.andE₁.andE₁)
  have rel := GaussianRadiusExponentialName.name_regular constantF one (linear z B a c) (relative_input z R B E T a b c h)
  have ha := h.andE₂.andE₁.andE₁.andE₁
  apply GaussianNamedLipschitzRate.independent_rate _ _ _ _ _ _ (num 6) (positive_product _ _ ha ha) later
    (multiply_fast _ _ _ _ earlier rel)
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E)
      (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift c) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa [diagonalEnvelope,Syn.shift,productF,productData,relativeF,relativeData] using original_product_envelope (var 0) (Syn.shift z) (Syn.shift R)
    (Syn.shift B) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) (Syn.shift c) hs

theorem relative_linear_remainder (p z R B E T a b c : PTm n) (h : Γ ⊢[PRAAx] source z R B E T a b c) :
    Γ ⊢[PRAAx] distanceBounded (ap2 relativeF p (relativeData z B a c)) (qadd qone (linear z B a c))
      (((R+one)*c)*((R+one)*c)) (a*a) :=
  GaussianExponentialLinearRemainder.original_constant_exponential_linear_remainder (linear z B a c) ((R+one)*c) a p
    h.andE₂.andE₁.andE₁.andE₁ h.andE₂.andE₂.andE₂
    (linear_bound z R B a c h.andE₁.andE₁ h.andE₁.andE₂.andE₂ h.andE₂.andE₁.andE₁.andE₁)
    (qmul_canonical _ _)

theorem original_Euler_power_actual_linear_shift_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      independentRate powerF productF (powerData (var 0) (var 2) (var 5+var 7) (var 6))
        (productData (var 0) (var 2) (var 5) (var 6) (var 7))
        (coefficient (var 1) (var 3) (var 4) (var 7)) (var 5*var 5)) :=
  closeUniv 8 (.impI (original_power_product_rate _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerPowerExponentialShift
