import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianShrinkingGridCoefficientSensitivity
import IPRADerivations.Analysis.Polynomials.Taylor.GaussianShrinkingPolynomialTail
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder

/-!
# Original full-polynomial values recover a coefficient with O(1/H) tail

Only the original full polynomial evaluations at j/H are supplied.
The actual coefficient norm bounds discharge all prefix observations
through the exact shrinking-disk tails. At degree d the remaining
coefficient error is the computed grid gain times a finite O(1/H) term.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianShrinkingGridValueRecovery

open_ipra
open GaussianRationalHorner (evaluate qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalTravelScaling (radius)
open GaussianRationalFiniteGridIdentity (gridPoint)
open GaussianRationalPowerExpansion (partialSum)
open GaussianLagrangeCoefficientSensitivity (gain)
open GaussianEuclideanDistanceName (fraction)
open GaussianCoefficientL1 (coefficientNorm)
open GaussianRationalL1 (qL1)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def query (H s : PTm n) : PTm n := qmul (radius one H) (gridPoint s)
def valuesClose (C D d H A B : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift d) ⟶ distanceBounded
    (evaluate (Syn.shift C) (query (Syn.shift H) (var 0))) (evaluate (Syn.shift D) (query (Syn.shift H) (var 0)))
      (Syn.shift A) (Syn.shift B*pw (Syn.shift H) (Syn.shift d)))
def errorNumerator (d H U V A B : PTm n) : PTm n := two*(A*H+(U+V)*pw d (succ d)*B)
def errorDenominator (d H B : PTm n) : PTm n := B*pw H (succ d)

ipra_subst query
ipra_subst valuesClose [Syn.subst_shift, Syn.shift_subst]
ipra_subst errorNumerator
ipra_subst errorDenominator

theorem denominator_positive (d H B : PTm n) (hH : Γ ⊢[PRAAx] le one H) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    le one (errorDenominator d H B) :=
  GaussianRationalHorner.positive_product _ _ hB (GaussianFactorBudget.power_positive _ _ hH)

theorem query_bound (d H s : PTm n) (hH : Γ ⊢[PRAAx] le one H) (hs : Γ ⊢[PRAAx] le s d) : Γ ⊢[PRAAx]
    bounded (query H s) d H := by
  have point : Γ ⊢[PRAAx] bounded (query H s) s H :=
    bound_congr (.eqRefl _) (by ipra_ring) (by ipra_ring)
      (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hH (le_refl one)
        (GaussianDominantPairAlgebra.radius_bounded one H hH) (GaussianDominantPairAlgebra.radius_bounded s one (le_refl one)))
  exact GaussianCoefficientNameBounds.bounded_radius_mono_same hH hs point

theorem values_at (C D d H A B s : PTm n) (h : Γ ⊢[PRAAx] valuesClose C D d H A B)
    (hs : Γ ⊢[PRAAx] le s d) : Γ ⊢[PRAAx]
    distanceBounded (evaluate C (query H s)) (evaluate D (query H s)) A (B*pw H d) := by
  have gate : Γ ⊢[PRAAx] le s d ⟶ distanceBounded (evaluate C (query H s)) (evaluate D (query H s)) A (B*pw H d) := by
    simpa [valuesClose] using h.allE s
  exact .impE gate hs

theorem prefix_error (C D N M d H U V A B s : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ M)
    (hdN : Γ ⊢[PRAAx] le d N) (hdM : Γ ⊢[PRAAx] le d M)
    (hH : Γ ⊢[PRAAx] le one H) (hdH : Γ ⊢[PRAAx] le d H) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (fraction U one))
    (hd : Γ ⊢[PRAAx] rationalLE (coefficientNorm D) (fraction V one))
    (h : Γ ⊢[PRAAx] valuesClose C D d H A B) (hs : Γ ⊢[PRAAx] le s d) : Γ ⊢[PRAAx]
    rationalLE (qL1 (qsub (partialSum C N (query H s) (succ d)) (partialSum D M (query H s) (succ d))))
      (fraction (errorNumerator d H U V A B) (errorDenominator d H B)) := by
  let W := pw H (succ d)
  let T := pw d (succ d)
  have hW : Γ ⊢[PRAAx] le one W := GaussianFactorBudget.power_positive H (succ d) hH
  have hE := denominator_positive d H B hH hB
  have tailC := GaussianShrinkingPolynomialTail.finite_coefficient_tail C N d (query H s) U one d H hC hdN
    (le_refl one) hH hdH hc (query_bound d H s hH hs)
  have tailD := GaussianShrinkingPolynomialTail.finite_coefficient_tail D M d (query H s) V one d H hD hdM
    (le_refl one) hH hdH hd (query_bound d H s hH hs)
  have firstClear : Γ ⊢[PRAAx] (U*T)*errorDenominator d H B ≐ (U*T*B)*(one*W) := by
    unfold errorDenominator W
    ipra_ring
  have first : Γ ⊢[PRAAx] distanceBounded (partialSum C N (query H s) (succ d)) (evaluate C (query H s))
      (U*T*B) (errorDenominator d H B) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ (U*T) (one*W) (U*T*B) (errorDenominator d H B)
      (GaussianRationalHorner.positive_product _ _ (le_refl one) hW) hE
      (le_congr firstClear.eqSymm (.eqRefl _) (le_refl _))
      (GaussianRationalDistanceOrder.distance_symmetric _ _ _ _
        (GaussianRationalHorner.positive_product _ _ (le_refl one) hW) tailC)
  have middleClear : Γ ⊢[PRAAx] A*errorDenominator d H B ≐ (A*H)*(B*pw H d) :=
    (congrMul (.eqRefl A) (congrMul (.eqRefl B) (pw_succ H d))).eqTrans (by ipra_ring)
  have middle : Γ ⊢[PRAAx] distanceBounded (evaluate C (query H s)) (evaluate D (query H s))
      (A*H) (errorDenominator d H B) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _
      (GaussianRationalHorner.positive_product _ _ hB (GaussianFactorBudget.power_positive H d hH)) hE
      (le_congr middleClear.eqSymm (.eqRefl _) (le_refl _)) (values_at C D d H A B s h hs)
  have lastClear : Γ ⊢[PRAAx] (V*T)*errorDenominator d H B ≐ (V*T*B)*(one*W) := by
    unfold errorDenominator W
    ipra_ring
  have last : Γ ⊢[PRAAx] distanceBounded (evaluate D (query H s)) (partialSum D M (query H s) (succ d))
      (V*T*B) (errorDenominator d H B) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ (V*T) (one*W) (V*T*B) (errorDenominator d H B)
      (GaussianRationalHorner.positive_product _ _ (le_refl one) hW) hE
      (le_congr lastClear.eqSymm (.eqRefl _) (le_refl _)) tailD
  have combined := GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hE
    (GaussianRationalDistanceOrder.distance_triangle_same _ _ _ _ _ _ hE first middle) last
  exact RationalArgmin.rationalLE_congr (.eqRefl _)
    (RationalNonnegativePowers.fraction_congr (by unfold errorNumerator T; ipra_ring) (.eqRefl _))
      (GaussianRationalL1Algebra.qL1_of_bounded _ _ _ hE combined)

theorem original_coefficient_error (C D N M d H U V A B : PTm n)
    (hC : Γ ⊢[PRAAx] length C ≐ succ N) (hD : Γ ⊢[PRAAx] length D ≐ succ M)
    (hdN : Γ ⊢[PRAAx] le d N) (hdM : Γ ⊢[PRAAx] le d M)
    (hH : Γ ⊢[PRAAx] le one H) (hdH : Γ ⊢[PRAAx] le d H) (hB : Γ ⊢[PRAAx] le one B)
    (hc : Γ ⊢[PRAAx] rationalLE (coefficientNorm C) (fraction U one))
    (hd : Γ ⊢[PRAAx] rationalLE (coefficientNorm D) (fraction V one))
    (h : Γ ⊢[PRAAx] valuesClose C D d H A B) : Γ ⊢[PRAAx]
    distanceBounded (entry C (monus N d)) (entry D (monus M d))
      (gain d d*errorNumerator d H U V A B) (B*H) := by
  have cs : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift C) ≐ succ (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hC.shift
  have ds : Γ.map Fm.shift ⊢[PRAAx] length (Syn.shift D) ≐ succ (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hD.shift
  have ns : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift d) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hdN.shift
  have ms : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift d) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hdM.shift
  have hhs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift H) := by simpa [Fm.shift,Syn.shift] using hH.shift
  have dhs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift d) (Syn.shift H) := by simpa [Fm.shift,Syn.shift] using hdH.shift
  have bs : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using hB.shift
  have ucs : Γ.map Fm.shift ⊢[PRAAx] rationalLE (coefficientNorm (Syn.shift C)) (fraction (Syn.shift U) one) := by simpa [Fm.shift,Syn.shift] using hc.shift
  have vds : Γ.map Fm.shift ⊢[PRAAx] rationalLE (coefficientNorm (Syn.shift D)) (fraction (Syn.shift V) one) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] valuesClose (Syn.shift C) (Syn.shift D) (Syn.shift d) (Syn.shift H) (Syn.shift A) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  have prefixErrors : Γ ⊢[PRAAx] GaussianShrinkingGridCoefficientSensitivity.observationsClose C D N M d H
      (fraction (errorNumerator d H U V A B) (errorDenominator d H B)) := by
    refine .allI (.impI ?_)
    simpa only [Syn.shift,GaussianShrinkingGridCoefficientSensitivity.observation,query,subst_query,subst_errorNumerator,
      subst_errorDenominator,GaussianEuclideanDistanceName.subst_fraction] using
      prefix_error (Syn.shift C) (Syn.shift D) (Syn.shift N) (Syn.shift M) (Syn.shift d) (Syn.shift H)
        (Syn.shift U) (Syn.shift V) (Syn.shift A) (Syn.shift B) (var 0) cs.wk ds.wk ns.wk ms.wk
          hhs.wk dhs.wk bs.wk ucs.wk vds.wk es.wk Prf.hyp0
  have scaled := GaussianShrinkingGridCoefficientSensitivity.original_coefficient_error C D N M d H d
    (errorNumerator d H U V A B) (errorDenominator d H B) hdN hdM (le_refl d) hH
      (denominator_positive d H B hH hB) prefixErrors
  have denominator : Γ ⊢[PRAAx] errorDenominator d H B ≐ (B*H)*pw H d :=
    (congrMul (.eqRefl B) (pw_succ H d)).eqTrans (by ipra_ring)
  exact GaussianMonicResidualRadius.bounded_cancel _ _ _ (pw H d)
    (GaussianRationalHorner.positive_product _ _ hB hH) (GaussianFactorBudget.power_positive H d hH)
      (bound_congr (.eqRefl _) (by ipra_ring) denominator scaled)

def input (C D N M d H U V A B : PTm n) : Fm PTm n :=
  (length C ≐ succ N) ⋏ ((length D ≐ succ M) ⋏ (le d N ⋏ (le d M ⋏ (le one H ⋏ (le d H ⋏ (le one B ⋏
    (rationalLE (coefficientNorm C) (fraction U one) ⋏ (rationalLE (coefficientNorm D) (fraction V one) ⋏
      valuesClose C D d H A B))))))))
ipra_subst input

theorem from_input (C D N M d H U V A B : PTm n) (h : Γ ⊢[PRAAx] input C D N M d H U V A B) : Γ ⊢[PRAAx]
    distanceBounded (entry C (monus N d)) (entry D (monus M d))
      (gain d d*errorNumerator d H U V A B) (B*H) :=
  original_coefficient_error C D N M d H U V A B h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
    h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂

theorem actual_full_polynomial_shrinking_grid_coefficient_recovery_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      distanceBounded (entry (var 0) (monus (var 2) (var 4))) (entry (var 1) (monus (var 3) (var 4)))
        (gain (var 4) (var 4)*errorNumerator (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)) (var 9*var 5)) :=
  closeUniv 10 (.impI (from_input _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianShrinkingGridValueRecovery
