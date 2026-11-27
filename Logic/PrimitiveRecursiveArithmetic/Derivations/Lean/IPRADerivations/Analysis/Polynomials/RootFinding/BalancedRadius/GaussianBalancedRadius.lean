import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusSearch
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusValues
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusZero

/-!
# Actual balanced radius with both residual branches

This is the balanced starting-radius part of FTA_iPRA lem:descent. The
zero-constant branch returns radius zero. Otherwise the actual bounded
scan returns the largest fitting dyadic exponent and an actual coefficient
whose doubled-radius test fails. All coefficient radius certificates and
the strict squared balanced witness are derived for the original rational
codes. No height, successful scan or output bound is an input premise.

Translation, selection of a dominant plateau, rational direction and the
full local contraction remain separate proof obligations.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianBalancedRadius

open_ipra
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusSyntax (unit unit_positive coefficient nonconstant)
open LeanProofs.IPRA.Analysis.GaussianBalancedRadiusHeight (E)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction)
open LeanProofs.IPRA.Analysis.GaussianRationalMetric (qnormSq)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inputContract (C N : PTm n) : Fm PTm n :=
  Foundations.SequenceComposition.length C ≐ succ N ⋏ (le one N ⋏ nonconstant C N)
def radiusNumerator (C N : PTm n) : PTm n :=
  sg (GaussianBalancedRadiusSyntax.numerator C N zero)*unit (GaussianBalancedRadiusSearch.radiusIndex C N)
def radiusDenominator (C N : PTm n) : PTm n := unit (E C N)
def radius (C N : PTm n) : PTm n := fraction (radiusNumerator C N) (radiusDenominator C N)
def term (C N i : PTm n) : PTm n :=
  GaussianBalancedRadiusZero.term C N (radiusNumerator C N) (radiusDenominator C N) i

ipra_subst inputContract
ipra_subst radiusNumerator
ipra_subst radiusDenominator
ipra_subst radius
ipra_subst term

theorem denominator_positive (C N : PTm n) : Γ ⊢[PRAAx] le one (radiusDenominator C N) := unit_positive _

theorem numerator_zero (C N : PTm n) (h : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.numerator C N zero ≐ zero) :
    Γ ⊢[PRAAx] radiusNumerator C N ≐ zero :=
  (congrMul ((congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans sg_zero) (.eqRefl _)).eqTrans (zero_mul _)

theorem numerator_positive (C N : PTm n) (h : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero)) :
    Γ ⊢[PRAAx] radiusNumerator C N ≐ unit (GaussianBalancedRadiusSearch.radiusIndex C N) := by
  have sign : Γ ⊢[PRAAx] sg (GaussianBalancedRadiusSyntax.numerator C N zero) ≐ one :=
    (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (RationalIntegerNormalization.positive_form h))).eqTrans (sg_succ _)
  exact (congrMul sign (.eqRefl _)).eqTrans (one_mul _)

theorem radius_zero (C N : PTm n) (h : Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.numerator C N zero ≐ zero) :
    Γ ⊢[PRAAx] radius C N ≐ fraction zero one :=
  (RationalNonnegativePowers.fraction_congr (numerator_zero C N h) (.eqRefl _)).eqTrans
    (GaussianBalancedRadiusZero.fraction_zero _ (denominator_positive C N))

theorem radius_nonnegative (C N : PTm n) : Γ ⊢[PRAAx] rationalLE (fraction zero one) (radius C N) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (RationalNonnegativePowers.power_one _ _)
    (RationalNonnegativePowers.power_nonnegative _ _ one (denominator_positive C N))

theorem radius_canonical (C N : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (radius C N) :=
  RationalNormalForm.normalize_well_formed _ _ (denominator_positive C N)

theorem radius_represents (C N : PTm n) : Γ ⊢[PRAAx]
    RationalArithmetic.represents (radius C N) (ZT.ofNat (radiusNumerator C N)) (radiusDenominator C N) :=
  GaussianEuclideanDistanceName.fraction_represents _ _ (denominator_positive C N)

theorem positive_radius (C N : PTm n)
    (h0 : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero)) : Γ ⊢[PRAAx]
    radius C N ≐ GaussianBalancedRadiusValues.radius (E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) :=
  RationalNonnegativePowers.fraction_congr (numerator_positive C N h0) (.eqRefl _)

theorem positive_input (C N : PTm n) (h : Γ ⊢[PRAAx] inputContract C N)
    (h0 : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero)) :
    Γ ⊢[PRAAx] GaussianBalancedRadiusSyntax.input C N :=
  .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h)) (.andI h0 (Prf.andE₂ (Prf.andE₂ h))))

theorem positive_term (C N i : PTm n)
    (h0 : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero)) : Γ ⊢[PRAAx]
    term C N i ≐ GaussianBalancedRadiusValues.scaledNorm C N (E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) i :=
  GaussianBalancedRadiusZero.term_congr C N i (numerator_positive C N h0) (.eqRefl _)

theorem coefficient_bound (C N i : PTm n) (h : Γ ⊢[PRAAx] inputContract C N)
    (hi : Γ ⊢[PRAAx] le one i) (hiN : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx]
    rationalLE (term C N i) (qnormSq (coefficient C N zero)) := by
  refine .orE (zero_or_succ (GaussianBalancedRadiusSyntax.numerator C N zero)) ?_ ?_
  · exact GaussianBalancedRadiusZero.zero_term_bound C N _ _ i (denominator_positive C N) hi.wk
      (numerator_zero C N Prf.hyp0)
  · have hp : (GaussianBalancedRadiusSyntax.numerator C N zero ≐ succ (PTm.pred (GaussianBalancedRadiusSyntax.numerator C N zero)))::Γ
        ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero) :=
      Order.zero_lt_of_eq_succ Prf.hyp0
    have source := GaussianBalancedRadiusSearch.search_correct C N (positive_input C N h.wk hp)
    have fit := GaussianBalancedRadiusSearch.fits_degree_at C N (E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) i
      (Prf.andE₁ (Prf.andE₂ source)) hi.wk hiN.wk
    exact RationalArgmin.rationalLE_congr (positive_term C N i hp).eqSymm (.eqRefl _)
      ((GaussianBalancedRadiusValues.fit_iff C N (E C N) (GaussianBalancedRadiusSearch.radiusIndex C N) i).iffMp fit)

def allCoefficients (C N : PTm n) : Fm PTm n := .all
  (le one (var 0) ⟶ le (var 0) (Syn.shift N) ⟶
    rationalLE (term (Syn.shift C) (Syn.shift N) (var 0)) (qnormSq (coefficient (Syn.shift C) (Syn.shift N) zero)))
ipra_subst allCoefficients [Syn.subst_shift, Syn.shift_subst]

theorem all_coefficient_bounds (C N : PTm n) (h : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx] allCoefficients C N := by
  refine .allI (.impI (.impI ?_))
  have hs : Γ.map Fm.shift ⊢[PRAAx] inputContract (Syn.shift C) (Syn.shift N) := by
    simpa only [Fm.shift,subst_inputContract,Syn.shift] using h.shift
  exact coefficient_bound (Syn.shift C) (Syn.shift N) (var 0) hs.wk.wk Prf.hyp1 Prf.hyp0

def balancedBranch (C N : PTm n) : Fm PTm n :=
  GaussianBalancedRadiusSearch.certificate C N (GaussianBalancedRadiusSearch.radiusIndex C N)
    (GaussianBalancedRadiusSearch.witness C N) ⋏
    neg (rationalLE (RationalArithmetic.multiply (fraction (pw (two*two) N) one)
      (term C N (GaussianBalancedRadiusSearch.witness C N))) (qnormSq (coefficient C N zero)))

ipra_subst balancedBranch

theorem positive_balanced_branch (C N : PTm n) (h : Γ ⊢[PRAAx] inputContract C N)
    (h0 : Γ ⊢[PRAAx] le one (GaussianBalancedRadiusSyntax.numerator C N zero)) :
    Γ ⊢[PRAAx] balancedBranch C N := by
  have source := GaussianBalancedRadiusSearch.search_correct C N (positive_input C N h h0)
  have facts := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ source))
  have hiN := Prf.andE₁ (Prf.andE₂ facts)
  have failure := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ facts))
  have actual := GaussianBalancedRadiusValues.balanced_not_le C N (E C N)
    (GaussianBalancedRadiusSearch.radiusIndex C N) (GaussianBalancedRadiusSearch.witness C N) hiN failure
  refine .andI source (.impI ?_)
  exact .impE actual.wk (RationalArgmin.rationalLE_congr
    (RationalAlgebra.multiply_congr (.eqRefl _) (positive_term C N (GaussianBalancedRadiusSearch.witness C N) h0.wk))
    (.eqRefl _) Prf.hyp0)

def certificate (C N : PTm n) : Fm PTm n := RationalNormalForm.wellFormed (radius C N) ⋏
  (rationalLE (fraction zero one) (radius C N) ⋏
  (RationalArithmetic.represents (radius C N) (ZT.ofNat (radiusNumerator C N)) (radiusDenominator C N) ⋏
  (allCoefficients C N ⋏
  ((GaussianBalancedRadiusSyntax.numerator C N zero ≐ zero ⟶ radius C N ≐ fraction zero one) ⋏
   (le one (GaussianBalancedRadiusSyntax.numerator C N zero) ⟶ balancedBranch C N)))))

ipra_subst certificate

theorem balanced_radius (C N : PTm n) (h : Γ ⊢[PRAAx] inputContract C N) : Γ ⊢[PRAAx] certificate C N :=
  .andI (radius_canonical C N) (.andI (radius_nonnegative C N) (.andI (radius_represents C N)
    (.andI (all_coefficient_bounds C N h)
      (.andI (.impI (radius_zero C N Prf.hyp0)) (.impI (positive_balanced_branch C N h.wk Prf.hyp0))))))

def output (C N : PTm n) : PTm n := pairT (radius C N) (pairT (radiusNumerator C N)
  (pairT (radiusDenominator C N) (pairT (GaussianBalancedRadiusSearch.radiusIndex C N)
    (pairT (GaussianBalancedRadiusSearch.witness C N) (E C N)))))
def outputF : PR 2 := PTm.toPR (output (var 0) (var 1))
ipra_subst output

theorem program_at (C N : PTm n) : Γ ⊢[PRAAx] ap2 outputF C N ≐ output C N := by
  simpa [outputF,ap2] using toPR_eq (Γ := Γ) (output (var 0) (var 1) : PTm 2) ![C,N]

theorem returned_radius (C N : PTm n) : Γ ⊢[PRAAx] fstT (ap2 outputF C N) ≐ radius C N :=
  (program_at C N).fstE

theorem returned_numerator (C N : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (ap2 outputF C N)) ≐ radiusNumerator C N :=
  (program_at C N).sndE.fstE

theorem returned_denominator (C N : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (ap2 outputF C N))) ≐ radiusDenominator C N :=
  (program_at C N).sndE.sndE.fstE

theorem returned_index (C N : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (ap2 outputF C N)))) ≐ GaussianBalancedRadiusSearch.radiusIndex C N :=
  (program_at C N).sndE.sndE.sndE.fstE

theorem returned_witness (C N : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (sndT (sndT (ap2 outputF C N))))) ≐ GaussianBalancedRadiusSearch.witness C N :=
  (program_at C N).sndE.sndE.sndE.sndE.fstE

theorem returned_exponent (C N : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (sndT (sndT (ap2 outputF C N))))) ≐ E C N :=
  (program_at C N).sndE.sndE.sndE.sndE.sndE

theorem balanced_radius_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (inputContract (var 0) (var 1) ⟶ certificate (var 0) (var 1)) :=
  closeUniv 2 (.impI (balanced_radius _ _ Prf.hyp0))

theorem balanced_radius_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((ap2 outputF (var 0) (var 1) ≐ output (var 0) (var 1)) ⋏
      fstT (ap2 outputF (var 0) (var 1)) ≐ radius (var 0) (var 1)) :=
  closeUniv 2 (.andI (program_at _ _) (returned_radius _ _))

end LeanProofs.IPRA.Analysis.GaussianBalancedRadius
