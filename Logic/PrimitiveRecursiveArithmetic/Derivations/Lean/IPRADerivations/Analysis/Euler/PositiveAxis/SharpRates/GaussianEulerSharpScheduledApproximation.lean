import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpScheduleBudget
import IPRADerivations.Analysis.Gamma.Integrals.GaussianEulerSharpGammaRate

/-!
# Actual finite Euler observations at the documented sharp degree

Keep the literal degree and choose only the independent decay query.
The evaluated arithmetic constant is at most 5*2^-(p+4). Both the
original improper Euler name and original Gamma name retain arbitrary
independent output precisions. At output query p+2 the actual distance
is at most 2^-p, using only the original native input guards.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSharpScheduledApproximation

open_ipra
open GaussianEulerSharpDegreeSchedule (degree degree_positive)
open GaussianEulerSharpScheduleBudget (decayClock mainNumerator mainDenominator main_budget degree_covers_radius)
open GaussianEulerSharpFiniteRate (finitePoint improperPoint)
open GaussianEulerSharpGammaRate (gammaPoint)
open GaussianEulerSharpResidualAssembly (boundNumerator boundDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

abbrev source (z R B A : PTm n) : Fm PTm n := GaussianEulerIntegralGammaIdentification.source z R B A
def numerator (p q v : PTm n) : PTm n := num 5*(unit q*unit v)+unit (p+num 4)*(unit q+unit v)
def denominator (p q v : PTm n) : PTm n := unit (p+num 4)*(unit q*unit v)

theorem degree_source (p z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    GaussianBetaSharpCofinalSchedule.source z R B A (degree p R) :=
  .andI h.andE₁ (.andI h.andE₂ (degree_covers_radius p R))

theorem denominator_positive (p q v : PTm n) : Γ ⊢[PRAAx] le one (denominator p q v) :=
  positive_product _ _ (unit_positive _) (positive_product _ _ (unit_positive q) (unit_positive v))

theorem numerical_rate (p q v X Y a b : PTm n) (hY : Γ ⊢[PRAAx] le one Y)
    (hX : Γ ⊢[PRAAx] le (X*unit (p+num 4)) (num 5*Y))
    (h : Γ ⊢[PRAAx] distanceBounded a b (boundNumerator X Y (unit q) (unit v)) (boundDenominator Y (unit q) (unit v))) : Γ ⊢[PRAAx]
    distanceBounded a b (numerator p q v) (denominator p q v) := by
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ hY (positive_product _ _ (unit_positive q) (unit_positive v))) (denominator_positive p q v) _ h
  dsimp only [boundNumerator,boundDenominator,numerator,denominator]
  ipra_le (𝔞(unit q)*𝔞(unit v)*𝔞(unit q)*𝔞(unit v))*sl hX

/-- The original finite Euler and improper observations keep their
independent requested precisions, at the unchanged documented degree. -/
theorem original_improper_observations (p q v z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z R B A (degree p R)) (improperPoint v z R B A) (numerator p q v) (denominator p q v) :=
  numerical_rate p q v (mainNumerator p R) (mainDenominator p R) _ _
    (positive_product _ _ (degree_positive p R) (GaussianBetaContiguousUpperTailBudget.fixed_denominator_positive _ _))
    (main_budget p R) (GaussianEulerSharpFiniteRate.original_sharp_bound q v (decayClock p R) z R B A (degree p R) (degree_source p z R B A h))

theorem original_gamma_observations (p q v z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint q z R B A (degree p R)) (gammaPoint v z R B A) (numerator p q v) (denominator p q v) :=
  numerical_rate p q v (mainNumerator p R) (mainDenominator p R) _ _
    (positive_product _ _ (degree_positive p R) (GaussianBetaContiguousUpperTailBudget.fixed_denominator_positive _ _))
    (main_budget p R) (GaussianEulerSharpGammaRate.original_finite_euler_to_gamma q v (decayClock p R) z R B A (degree p R) (degree_source p z R B A h))

theorem two_bit_identity (p : PTm n) : Γ ⊢[PRAAx] unit (p+num 2) ≐ num 4*unit p :=
  (pw_add two p (num 2)).eqTrans ((congrMul (.eqRefl _) ((pw_succ two one).eqTrans
    (congrMul (pw_one two) (.eqRefl two)))).eqTrans (by dsimp only [unit]; ipra_ring))
theorem four_bit_identity (p : PTm n) : Γ ⊢[PRAAx] unit (p+num 4) ≐ num 16*unit p :=
  (congrAp2 powF (by ipra_ring : Γ ⊢[PRAAx] p+num 4 ≐ (p+num 2)+num 2) (.eqRefl two)).eqTrans
    ((two_bit_identity (p+num 2)).eqTrans ((congrMul (.eqRefl _) (two_bit_identity p)).eqTrans (by ipra_ring)))

theorem evaluated_precision_budget (p : PTm n) : Γ ⊢[PRAAx]
    le (numerator p (p+num 2) (p+num 2)*unit p) (one*denominator p (p+num 2) (p+num 2)) := by
  apply le_of_eq_add (d := num 48*unit p*unit p*unit p)
  apply deriveNat
  have twoBits := natEq (two_bit_identity (Γ := Γ) p)
  have fourBits := natEq (four_bit_identity (Γ := Γ) p)
  dsimp only [numerator,denominator]
  ipra_simps
  rw [twoBits,fourBits]
  ring

theorem original_improper_evaluated (p z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint (p+num 2) z R B A (degree p R)) (improperPoint (p+num 2) z R B A) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (denominator_positive p (p+num 2) (p+num 2)) (unit_positive p)
    (evaluated_precision_budget p) (original_improper_observations p (p+num 2) (p+num 2) z R B A h)

theorem original_gamma_evaluated (p z R B A : PTm n) (h : Γ ⊢[PRAAx] source z R B A) : Γ ⊢[PRAAx]
    distanceBounded (finitePoint (p+num 2) z R B A (degree p R)) (gammaPoint (p+num 2) z R B A) one (unit p) :=
  distance_radius_mono _ _ _ _ _ _ (denominator_positive p (p+num 2) (p+num 2)) (unit_positive p)
    (evaluated_precision_budget p) (original_gamma_observations p (p+num 2) (p+num 2) z R B A h)

theorem literal_sharp_Euler_degree_actual_improper_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶
      distanceBounded (finitePoint ((var 0)+num 2) (var 1) (var 2) (var 3) (var 4) (degree (var 0) (var 2)))
        (improperPoint ((var 0)+num 2) (var 1) (var 2) (var 3) (var 4)) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_improper_evaluated _ _ _ _ _ Prf.hyp0))
theorem literal_sharp_Euler_degree_actual_Gamma_observation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 1) (var 2) (var 3) (var 4) ⟶
      distanceBounded (finitePoint ((var 0)+num 2) (var 1) (var 2) (var 3) (var 4) (degree (var 0) (var 2)))
        (gammaPoint ((var 0)+num 2) (var 1) (var 2) (var 3) (var 4)) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_gamma_evaluated _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerSharpScheduledApproximation
