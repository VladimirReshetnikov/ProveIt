import IPRADerivations.Analysis.Gamma.Taylor.DegreeTails.GaussianGammaUnitCoefficientMass
import IPRADerivations.Analysis.Gamma.Taylor.CoefficientEstimates.GaussianGammaFiniteCoefficientStability
import IPRADerivations.Analysis.Gamma.FunctionalEquations.Recurrence.Coefficients.GaussianGammaRecurrenceWeightName
import IPRADerivations.Foundations.FiniteQueryDemand

/-!
# Computed bounds for the original Gamma recurrence observations

Every original fixed coefficient sample at a positive radius has the
unchanged original full-polynomial unit coefficient-mass bound, uniformly
in all internal source queries and coefficient degrees. A real finite
maximum of the genuine full weight name bounds supplies one bound for
every weight degree through e. No coefficient/weight magnitude bound is
an input except the original positive numerical radius guard.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceCoefficientBounds

open_ipra
open GaussianRationalMetric (bounded)
open GaussianRationalLowCoefficientConvolution (exponent_inside)
open GaussianGammaFiniteCoefficientPolynomial (polynomial totalDegree)
open GaussianGammaFiniteCoefficientStability (fixedCoefficient)
open GaussianGammaRecurrenceWeights (weight)
open GaussianGammaRecurrenceWeightName (nameF data)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_fixed_sample_bound (q R j : PTm n) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    bounded (fixedCoefficient q R j) (GaussianGammaUnitCoefficientMass.budget R) one := by
  have inside : Γ ⊢[PRAAx] le j (totalDegree R j j) :=
    le_trans (GaussianGammaFiniteCoefficientStability.output_degree_bound j j j (le_refl j)) (le_add_left _ _)
  have range : Γ ⊢[PRAAx] lt (monus (totalDegree R j j) j) (length (polynomial q R j j)) :=
    lt_congr (.eqRefl _) (GaussianGammaFiniteCoefficientPolynomial.polynomial_length q R j j).eqSymm
      ((succ_monus_succ _ _).eqTrans (GaussianRationalMonicReconstruction.monus_le_left _ _))
  exact GaussianRationalReciprocal.bound_congr (exponent_inside _ _ _ inside).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianCoefficientNormEntries.bounded_coefficient_entry _ _ _ _ (le_refl one)
      (GaussianGammaUnitCoefficientMass.original_coefficient_mass q R j j hR) range)

def fullBound (m : PTm n) : PTm n := GaussianNameBounds.U nameF (data zero m)
def boundBody : PTm 2 := fullBound (var 0)
def uniformWeightBound (e : PTm n) : PTm n := one+
  LeanProofs.IPRA.Foundations.FiniteQueryDemand.finiteMaximum boundBody (succ e) zero
ipra_subst fullBound
ipra_subst uniformWeightBound

theorem bound_body_at (m : PTm n) : Γ ⊢[PRAAx] inst2 boundBody m zero ≐ fullBound m := by
  simp only [boundBody,inst2,subst_fullBound,Syn.subst_var,Matrix.cons_val_zero]
  exact .eqRefl _

theorem uniform_weight_positive (e : PTm n) : Γ ⊢[PRAAx] le one (uniformWeightBound e) := le_add_right _ _

theorem full_bound_below_maximum (e m : PTm n) (hm : Γ ⊢[PRAAx] le m e) : Γ ⊢[PRAAx]
    le (fullBound m) (uniformWeightBound e) := by
  have actual : Γ ⊢[PRAAx] le (inst2 boundBody m zero)
      (LeanProofs.IPRA.Foundations.FiniteQueryDemand.finiteMaximum boundBody (succ e) zero) :=
    LeanProofs.IPRA.Foundations.FiniteQueryDemand.finiteMaximum_at boundBody ((succ_monus_succ _ _).eqTrans hm)
  exact le_trans (le_congr (bound_body_at m) (.eqRefl _) actual) (le_add_left _ _)

theorem original_full_weight_sample_bound (p e m : PTm n) (hm : Γ ⊢[PRAAx] le m e) : Γ ⊢[PRAAx]
    bounded (weight p zero m) (uniformWeightBound e) one :=
  GaussianCoefficientNameBounds.bounded_radius_mono_one (full_bound_below_maximum e m hm)
    (GaussianGammaRecurrenceWeightName.sample_bound p zero m)

theorem original_Gamma_fixed_coefficient_sample_mass_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ bounded (fixedCoefficient (var 0) (var 1) (var 2))
      (GaussianGammaUnitCoefficientMass.budget (var 1)) one) := closeUniv 3 (.impI (original_fixed_sample_bound _ _ _ Prf.hyp0))

theorem original_Gamma_full_recurrence_weight_computed_uniform_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (var 2) (var 1) ⟶ bounded (weight (var 0) zero (var 2)) (uniformWeightBound (var 1)) one) :=
  closeUniv 3 (.impI (original_full_weight_sample_bound _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaRecurrenceCoefficientBounds
