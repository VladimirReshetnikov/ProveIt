import IPRADerivations.Analysis.Polynomials.GaussianPolynomialForwardDifferenceGridError
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalInverseQuadraticAlgebra
import IPRADerivations.Analysis.Names.Rates.GaussianNamedDifferenceQuotient

/-!
# Normalize the forward difference at an apart Gaussian step

The inverse power is computed from the actual rational step and has
the explicit norm bound given by its certified lower margin. Exact
cancellation identifies the normalized polynomial grid with its
factorially scaled leading coefficient. Arbitrary nearby grids carry
the corresponding amplified observation error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)
open LeanProofs.IPRA.Analysis.Products (fact)
open GaussianNameReciprocal (lower)
open GaussianPolynomialForwardDifferenceGrid (samples value leading_coefficient)
open GaussianPolynomialForwardDifferenceGridError (rowBound terminal_bound)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (qmul qzero)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_congr natScale_product)
open GaussianRationalPowerAlgebra (qmul_commutative power_product)
open GaussianRationalReciprocal (power reciprocal power_canonical)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianReciprocalHorner (qmul_associative qmul_one_right)
open GaussianTranslatedNonconstant (recode recode_canonical)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def inversePower (h N : PTm n) : PTm n := power (reciprocal h) N
def normalized (V N h : PTm n) : PTm n := qmul (inversePower h N) (value V N)

@[simp] theorem subst_inversePower {l : ℕ} (σ : Fin n → PTm l) (h N : PTm n) :
    Syn.subst σ (inversePower h N) = inversePower (Syn.subst σ h) (Syn.subst σ N) := by simp [inversePower]

@[simp] theorem subst_normalized {l : ℕ} (σ : Fin n → PTm l) (V N h : PTm n) :
    Syn.subst σ (normalized V N h) = normalized (Syn.subst σ V) (Syn.subst σ N) (Syn.subst σ h) := by
  simp [normalized,value]

theorem inverse_power_product (h N R : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R) :
    Γ ⊢[PRAAx] qmul (inversePower h N) (power h N) ≐ qone := by
  have hInv := (qmul_commutative (reciprocal h) h).eqTrans
    (GaussianRationalReciprocal.reciprocal_identity h (GaussianNameReciprocal.lower_norm_positive h R hR hh))
  exact (power_product (reciprocal h) h N).eqSymm.eqTrans
    ((congrAp2 GaussianRationalReciprocal.powerF (.eqRefl N) hInv).eqTrans
      (GaussianRationalRoundedPower.qone_power N))

theorem same_inverse (h N R : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R) :
    Γ ⊢[PRAAx] inversePower h N ≐ reciprocal (power h N) := by
  let a := inversePower h N
  let b := power h N
  let c := reciprocal b
  have ab := inverse_power_product h N R hR hh
  have near : Γ ⊢[PRAAx] neg (b ≐ qzero) := by
    refine .impI ?_
    exact .impE GaussianRationalCurveFibers.gaussian_one_nonzero
      (ab.wk.eqSymm.eqTrans ((qmul_congr (.eqRefl a) Prf.hyp0).eqTrans
        (GaussianRationalSyntheticDivision.qmul_zero_right a)))
  have norm := GaussianRationalFiniteRoots.norm_positive_of_nonzero b (power_canonical h N) near
  have bc := GaussianRationalReciprocal.reciprocal_identity b norm
  have cc := GaussianRationalReciprocal.reciprocal_canonical (Γ := Γ) b
  exact (qmul_one_right a (power_canonical _ _)).eqSymm.eqTrans
    ((qmul_congr (.eqRefl _) bc.eqSymm).eqTrans
      ((qmul_associative a b c).eqSymm.eqTrans
        ((qmul_congr ab (.eqRefl _)).eqTrans ((qmul_commutative qone c).eqTrans (qmul_one_right c cc)))))

theorem inverse_power_bound (h N R : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R) :
    Γ ⊢[PRAAx] bounded (inversePower h N) (pw R N) one :=
  GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (GaussianPolynomialPerturbation.one_power N)
    (GaussianRationalReciprocal.bounded_power _ _ _ _ (le_refl one)
      (GaussianNameReciprocal.inverse_bound h R hR hh))

theorem coefficient (C N x h R : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R) :
    Γ ⊢[PRAAx] normalized (samples C (succ N) x h) N h ≐ natScale (fact N) (entry C zero) := by
  let a := entry C zero
  let b := power h N
  let S := inversePower h N
  have cancel : Γ ⊢[PRAAx] qmul S (qmul a b) ≐ recode a :=
    (qmul_congr (.eqRefl _) ((qmul_commutative a b).eqTrans
      (GaussianRationalSyntheticCoefficientValues.qmul_recode_right b a).eqSymm)).eqTrans
      (GaussianRationalInverseQuadraticAlgebra.cancel_nested_product S b (recode a) (recode_canonical a)
        (inverse_power_product h N R hR hh))
  have forget : Γ ⊢[PRAAx] natScale (fact N) (recode a) ≐ natScale (fact N) a :=
    (GaussianRationalNaturalScale.natScale_as_product _ _).eqTrans
      ((GaussianRationalSyntheticCoefficientValues.qmul_recode_right _ _).eqTrans
        (GaussianRationalNaturalScale.natScale_as_product _ _).eqSymm)
  exact (qmul_congr (.eqRefl _) (leading_coefficient C N x h hC)).eqTrans
    ((natScale_product (fact N) S (qmul a b)).eqTrans ((natScale_congr (.eqRefl _) cancel).eqTrans forget))

theorem normalized_error (V W N h R A B : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R)
    (hB : Γ ⊢[PRAAx] le one B) (hrow : Γ ⊢[PRAAx] rowBound V W (succ N) A B) :
    Γ ⊢[PRAAx] distanceBounded (normalized V N h) (normalized W N h) (pw R N*(pw two N*A)) B :=
  GaussianNamedDifferenceQuotient.scale_distance _ _ _ _ _ _ hB (inverse_power_bound h N R hR hh)
    (terminal_bound V W N A B hB hrow)

theorem coefficient_error (V C N x h R A B : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hR : Γ ⊢[PRAAx] le one R) (hh : Γ ⊢[PRAAx] lower h R) (hB : Γ ⊢[PRAAx] le one B)
    (hrow : Γ ⊢[PRAAx] rowBound V (samples C (succ N) x h) (succ N) A B) :
    Γ ⊢[PRAAx] distanceBounded (normalized V N h) (natScale (fact N) (entry C zero)) (pw R N*(pw two N*A)) B :=
  distance_congr (.eqRefl _) (coefficient C N x h R hC hR hh) (.eqRefl _) (.eqRefl _)
    (normalized_error V (samples C (succ N) x h) N h R A B hR hh hB hrow)

/-- A fractional lower margin keeps the full constraint on the step scale. -/
theorem fractional_coefficient_error (V C N x h L D A B : PTm n) (hC : Γ ⊢[PRAAx] length C ≐ succ N)
    (hL : Γ ⊢[PRAAx] le one L) (hD : Γ ⊢[PRAAx] le one D) (hh : Γ ⊢[PRAAx] GaussianRationalLowerBounds.lower h L D)
    (hB : Γ ⊢[PRAAx] le one B) (hrow : Γ ⊢[PRAAx] rowBound V (samples C (succ N) x h) (succ N) A B) :
    Γ ⊢[PRAAx] distanceBounded (normalized V N h) (natScale (fact N) (entry C zero))
      (pw D N*(pw two N*A)) (pw L N*B) := by
  let W := samples C (succ N) x h
  let S := inversePower h N
  have hs : Γ ⊢[PRAAx] bounded S (pw D N) (pw L N) :=
    GaussianRationalReciprocal.bounded_power _ _ _ _ hL (GaussianRationalLowerBounds.inverse_bound _ _ _ hL hD hh)
  have raw := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _
    (GaussianPolynomialPerturbation.power_positive L N hL) hB hs (terminal_bound V W N A B hB hrow)
  have move := GaussianRationalReciprocal.bound_congr
    (GaussianRationalRoundedPower.multiplication_difference S (value V N) (value W N)).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  exact distance_congr (.eqRefl _)
    (coefficient C N x h D hC hD (GaussianRationalLowerBounds.name_lower _ _ _ hL hD hh))
    (.eqRefl _) (.eqRefl _) move

theorem actual_Gaussian_normalized_forward_difference_coefficient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (let C := var 0
     let N := var 1
     let x := var 2
     let h := var 3
     let R := var 4
     (length C ≐ succ N ⋏ (le one R ⋏ lower h R)) ⟶
       normalized (samples C (succ N) x h) N h ≐ natScale (fact N) (entry C zero)) :=
  closeUniv 5 (.impI (coefficient _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_Gaussian_normalized_forward_difference_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let V := var 0
     let C := var 1
     let N := var 2
     let x := var 3
     let h := var 4
     let R := var 5
     let A := var 6
     let B := var 7
     ((length C ≐ succ N ⋏ (le one R ⋏ lower h R)) ⋏
       (le one B ⋏ rowBound V (samples C (succ N) x h) (succ N) A B)) ⟶
       distanceBounded (normalized V N h) (natScale (fact N) (entry C zero)) (pw R N*(pw two N*A)) B) :=
  closeUniv 8 (.impI (coefficient_error _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂.andE₁
    Prf.hyp0.andE₁.andE₂.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianPolynomialForwardDifferenceNormalization
