import IPRADerivations.Analysis.Polynomials.Interpolation.GaussianLagrangeCoefficientSensitivity
import IPRADerivations.Analysis.Polynomials.Products.Convolution.GaussianPolynomialLowPrefix
import IPRADerivations.Analysis.RationalArithmetic.Directions.GaussianRationalTravelScaling
import IPRADerivations.Analysis.Polynomials.Coefficients.Norms.GaussianCoefficientNormEntries

/-!
# Actual coefficient extraction from a shrinking finite grid

The original finite low power prefixes are observed at j/H. Their
original coefficient error is bounded by H^e times the computed natural
grid gain. Actual dilation and the proved reciprocal-power round trip
perform the scaling; no division or extraction identity is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianShrinkingGridCoefficientSensitivity

open_ipra
open GaussianRationalHorner (evaluate qmul)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianRationalReciprocal (power)
open GaussianRationalTravelScaling (radius inverse)
open GaussianRationalPolynomialDilation (dilated)
open GaussianRationalFiniteGridIdentity (gridPoint)
open GaussianRationalPowerExpansion (partialSum)
open GaussianLagrangeCoefficientSensitivity (gain observationsClose)
open GaussianEuclideanDistanceName (fraction)
open GaussianRationalL1 (qL1)
open GaussianRationalSyntheticBounds (natCode)
open RationalArgmin (rationalLE)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def polynomial (C N d H : PTm n) : PTm n := dilated (GaussianPolynomialLowPrefix.polynomial C N d) d (radius one H)
def observation (C N d H s : PTm n) : PTm n := partialSum C N (qmul (radius one H) (gridPoint s)) (succ d)
def observationsClose (C D N M d H E : PTm n) : Fm PTm n := .all
  (le (var 0) (Syn.shift d) ⟶ rationalLE
    (qL1 (qsub (observation (Syn.shift C) (Syn.shift N) (Syn.shift d) (Syn.shift H) (var 0))
      (observation (Syn.shift D) (Syn.shift M) (Syn.shift d) (Syn.shift H) (var 0)))) (Syn.shift E))

ipra_subst polynomial
ipra_subst observation
ipra_subst observationsClose [Syn.subst_shift, Syn.shift_subst]

theorem original_evaluation (C N d H s : PTm n) (hd : Γ ⊢[PRAAx] le d N) : Γ ⊢[PRAAx]
    GaussianLagrangeInterpolation.observation (polynomial C N d H) s ≐ observation C N d H s :=
  (GaussianRationalPolynomialDilation.dilation_evaluation _ _ _ _ (GaussianPolynomialLowPrefix.polynomial_length C N d)).eqTrans
    (GaussianPolynomialLowPrefix.original_evaluation _ _ _ _ hd)

theorem grid_errors (C D N M d H E : PTm n) (hN : Γ ⊢[PRAAx] le d N) (hM : Γ ⊢[PRAAx] le d M)
    (h : Γ ⊢[PRAAx] observationsClose C D N M d H E) : Γ ⊢[PRAAx]
    GaussianLagrangeCoefficientSensitivity.observationsClose (polynomial C N d H) (polynomial D M d H) d E := by
  have hn : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift d) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using hN.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift d) (Syn.shift M) := by simpa [Fm.shift,Syn.shift] using hM.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] observationsClose (Syn.shift C) (Syn.shift D) (Syn.shift N) (Syn.shift M)
      (Syn.shift d) (Syn.shift H) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let Δ := le (var 0) (Syn.shift d) :: Γ.map Fm.shift
  have gate : Δ ⊢[PRAAx] le (var 0) (Syn.shift d) ⟶ rationalLE
      (qL1 (qsub (observation (Syn.shift C) (Syn.shift N) (Syn.shift d) (Syn.shift H) (var 0))
        (observation (Syn.shift D) (Syn.shift M) (Syn.shift d) (Syn.shift H) (var 0)))) (Syn.shift E) := by
    simpa [observationsClose] using hs.wk.allE (var 0)
  have out := RationalArgmin.rationalLE_congr
    (GaussianCoefficientL1.qL1_congr (qsub_congr
      (original_evaluation (Γ := Δ) (Syn.shift C) (Syn.shift N) (Syn.shift d) (Syn.shift H) (var 0) hn.wk)
      (original_evaluation (Syn.shift D) (Syn.shift M) (Syn.shift d) (Syn.shift H) (var 0) hm.wk))).eqSymm
      (.eqRefl _) (Prf.impE gate Prf.hyp0)
  simpa only [Δ,Syn.shift,subst_polynomial] using out

theorem scaled_reader (C N d H e : PTm n) (he : Γ ⊢[PRAAx] le e d) : Γ ⊢[PRAAx]
    GaussianTranslatedNonconstant.recode (entry (polynomial C N d H) (monus d e)) ≐
      qmul (power (radius one H) e) (entry C (monus N e)) :=
  (GaussianTranslatedNonconstant.recode_congr (GaussianPolynomialLowPrefix.dilated_original_reader C N d (radius one H) e he)).eqTrans
    ((GaussianTranslatedNonconstant.recode_eq _ (GaussianRationalHorner.qmul_canonical _ _)).eqTrans
      (GaussianRationalPowerAlgebra.qmul_commutative _ _))

theorem original_coefficient_error (C D N M d H e A B : PTm n)
    (hdN : Γ ⊢[PRAAx] le d N) (hdM : Γ ⊢[PRAAx] le d M) (he : Γ ⊢[PRAAx] le e d)
    (hH : Γ ⊢[PRAAx] le one H) (hB : Γ ⊢[PRAAx] le one B)
    (h : Γ ⊢[PRAAx] observationsClose C D N M d H (fraction A B)) : Γ ⊢[PRAAx]
    distanceBounded (entry C (monus N e)) (entry D (monus M e)) (pw H e*gain d e*A) B := by
  have scaled := GaussianLagrangeCoefficientSensitivity.original_coefficient_error (polynomial C N d H) (polynomial D M d H)
    d e (fraction A B) (GaussianRationalPolynomialDilation.dilated_length _ _ _)
    (GaussianRationalPolynomialDilation.dilated_length _ _ _) he (grid_errors C D N M d H _ hdN hdM h)
  have code := (qsub_congr (scaled_reader C N d H e he) (scaled_reader D M d H e he)).eqTrans
    (GaussianPolynomialCoefficientDifferences.scalar_scaled_difference _ _ _)
  have scale : Γ ⊢[PRAAx] RationalArithmetic.multiply (natCode (gain d e)) (fraction A B) ≐ fraction (gain d e*A) B :=
    RationalNonnegativePowers.nat_mul_fraction hB (.eqRefl _)
  have metric := GaussianCoefficientNormEntries.l1_to_euclidean _ (gain d e*A) B hB
    (RationalArgmin.rationalLE_congr (GaussianCoefficientL1.qL1_congr code) scale scaled)
  have inverseBound : Γ ⊢[PRAAx] bounded (power (inverse one H) e) (pw H e) one :=
    GaussianRationalReciprocal.bound_congr (.eqRefl _) (.eqRefl _) (GaussianPolynomialPerturbation.one_power e)
      (GaussianRationalReciprocal.bounded_power _ H one e (le_refl one) (GaussianDominantPairAlgebra.radius_bounded H one (le_refl one)))
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) hB inverseBound metric
  have roundtrip := GaussianRationalInvertibleNorm.qmul_roundtrip _ _
    (qsub (entry C (monus N e)) (entry D (monus M e)))
      (GaussianRationalTravelScaling.inverse_powers one H e (le_refl one) hH)
      (GaussianRationalMetric.qsub_canonical _ _)
  exact GaussianRationalReciprocal.bound_congr roundtrip (by ipra_ring) (by ipra_ring) product

theorem actual_shrinking_grid_original_coefficient_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (le (var 4) (var 2) ⟶ le (var 4) (var 3) ⟶ le (var 6) (var 4) ⟶ le one (var 5) ⟶ le one (var 8) ⟶
      observationsClose (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (fraction (var 7) (var 8)) ⟶
      distanceBounded (entry (var 0) (monus (var 2) (var 6))) (entry (var 1) (monus (var 3) (var 6)))
        (pw (var 5) (var 6)*gain (var 4) (var 6)*var 7) (var 8)) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (.impI (.impI
    (original_coefficient_error _ _ _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk.wk Prf.hyp1.wk.wk.wk
      Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0)))))))

end LeanProofs.IPRA.Analysis.GaussianShrinkingGridCoefficientSensitivity
