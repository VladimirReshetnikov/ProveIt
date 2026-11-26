import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalL1
import IPRADerivations.Analysis.Polynomials.RootFinding.Adequacy.GaussianRootSchedule

/-!
# Actual squared comparisons for a balanced dyadic radius

The coefficient list uses the existing descending Horner order. Its
coefficient of W^i is entry N-i, so index zero denotes the constant term.
The original rational Gaussian components retain their independent decoded
denominators. The finite scan uses only natural squared-norm comparisons;
its exponent j denotes the actual positive radius 2^j/2^E.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax

open_ipra
open LeanProofs.IPRA.Analysis.GaussianRationalL1 (rawGaussian rawDen raw_den_positive raw_represents)
open LeanProofs.IPRA.Analysis.ComplexLogarithmRemainder (normSq)
open LeanProofs.IPRA.Analysis.GaussianRationalHorner (positive_product)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry subst_entry)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def unit (t : PTm n) : PTm n := pw two t
def three : PTm n := succ two
def coefficient (C N i : PTm n) : PTm n := entry C (PTm.monus N i)
def numerator (C N i : PTm n) : PTm n := normSq (rawGaussian (coefficient C N i))
def denominator (C N i : PTm n) : PTm n := rawDen (coefficient C N i)*rawDen (coefficient C N i)
def score (C N _E j i : PTm n) : PTm n := numerator C N i*denominator C N zero*unit (two*j*i)
def cap (C N E i : PTm n) : PTm n := numerator C N zero*denominator C N i*unit (two*E*i)
def fitAt (C N E j i : PTm n) : Fm PTm n := le (score C N E j i) (cap C N E i)
def nonconstant (C N : PTm n) : Fm PTm n := .ex
  (le one (var 0) ⋏ (le (var 0) (Syn.shift N) ⋏ le one (numerator (Syn.shift C) (Syn.shift N) (var 0))))
def input (C N : PTm n) : Fm PTm n :=
  Foundations.SequenceComposition.length C ≐ succ N ⋏
    (le one N ⋏ (le one (numerator C N zero) ⋏ nonconstant C N))

ipra_subst unit
ipra_subst three
ipra_subst coefficient
ipra_subst numerator
ipra_subst denominator
ipra_subst score
ipra_subst cap
ipra_subst fitAt
ipra_subst nonconstant [Syn.subst_shift, Syn.shift_subst]
ipra_subst input

theorem unit_positive (t : PTm n) : Γ ⊢[PRAAx] le one (unit t) :=
  GaussianFactorBudget.power_positive two t (le_succ_self one)

theorem denominator_positive (C N i : PTm n) : Γ ⊢[PRAAx] le one (denominator C N i) :=
  positive_product _ _ (raw_den_positive _) (raw_den_positive _)

theorem coefficient_norm_represents (C N i : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (GaussianRationalMetric.qnormSq (coefficient C N i))
      (ZT.ofNat (numerator C N i)) (denominator C N i) :=
  GaussianRationalMetric.qnormSq_represents _ _ _ (raw_den_positive _) (raw_represents _)

theorem coefficient_norm_representation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (denominator (var 0) (var 1) (var 2)) ⋏
      RationalArithmetic.represents (GaussianRationalMetric.qnormSq (coefficient (var 0) (var 1) (var 2)))
        (ZT.ofNat (numerator (var 0) (var 1) (var 2))) (denominator (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.andI (denominator_positive _ _ _) (coefficient_norm_represents _ _ _))

end LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax
