import IPRADerivations.Analysis.GaussianGammaNegativeIntervalNative
import IPRADerivations.Analysis.GaussianGammaNegativeCriticalEndpoints
import IPRADerivations.Analysis.GaussianGammaDigammaStep

/-!
# Native unit steps within a negative Gamma interval

A large positive denominator gives the literal step `1/D` without
crossing a pole. At both endpoints the original shift product transfers
the quotient to the positive Euler derivative with the original error.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalCorrection (guard)
open GaussianGammaNegativeCriticalEndpoints (shifted_source)
open GaussianGammaNegativeIntervalNative (argument negative_regular productF productData original_product)
open GaussianGammaReciprocalInverse (gammaF)
open GaussianNamedDifferenceQuotient (input name_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNameArithmetic (multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_trans)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "GF" => GaussianNamedDifferenceQuotient.nameF gammaF gammaF
local notation "EF" => GaussianEulerLogarithmicImproperName.nameF
local notation "PF" => GaussianNamedDifferenceQuotient.nameF productF productF
local notation "gd" => GaussianGammaNegativeIntervalNative.data
local notation "minimumDenominator" => GaussianGammaDigammaNative.minimumDenominator

abbrev numerator (a b D : PTm n) : PTm n := GaussianGammaDigammaStep.neighborNumerator a b D
def denominator (b D : PTm n) : PTm n := D*b
def data (a b N D : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data gammaF gammaF (gd (numerator a b D) (denominator b D) N)
    (gd a b N) oneCode D
def productQuotientData (a b N D : PTm n) : PTm n :=
  GaussianNamedDifferenceQuotient.data productF productF (productData (numerator a b D) (denominator b D) N)
    (productData a b N) oneCode D

theorem denominator_positive {a b D : PTm n} (h : Γ ⊢[PRAAx] guard a b)
    (hD : Γ ⊢[PRAAx] lt b D) : Γ ⊢[PRAAx] le one D :=
  le_trans (shifted_source a b h).andE₂ (le_of_lt hD)

theorem neighbor_guard (a b D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] lt b D) :
    Γ ⊢[PRAAx] guard (numerator a b D) (denominator b D) := by
  have hs := denominator_positive h hD
  have gap := h.andE₂
  unfold lt at gap hD
  refine .andI (le_trans (GaussianRationalHorner.positive_product _ _ hs h.andE₁) (le_add_right _ _)) ?_
  unfold lt denominator numerator GaussianGammaDigammaStep.neighborNumerator
  ipra_le 𝔞(D)*sl gap+sl hD

theorem native_neighbor (a b N D : PTm n) : Γ ⊢[PRAAx]
    GaussianRootAlgebra.equal
      (GaussianEulerParameterExponentialIncrement.shifted (argument a b N) b oneCode D)
      (argument (numerator a b D) (denominator b D) N) := by
  apply GaussianRootAlgebra.equal_of_values <;>
    simp only [argument,GaussianGammaLocalPoleGuards.center,GaussianGammaPoleZeros.poleNumerator,
      GaussianEulerParameterExponentialIncrement.shifted,GaussianGammaDigammaStep.neighborNumerator,
      GaussianStirlingGammaLogarithm.arg,denominator,GaussianRootAlgebra.re_add,GaussianRootAlgebra.im_add,
      GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,GaussianRootAlgebra.re_neg,
      GaussianRootAlgebra.im_neg,GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;>
    ipra_simps <;> ring

theorem quotient_input (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] lt b D) :
    Γ ⊢[PRAAx] input gammaF gammaF (gd (numerator a b D) (denominator b D) N) (gd a b N) oneCode D :=
  .andI (negative_regular _ _ _ (neighbor_guard a b D h hD))
    (.andI (negative_regular _ _ _ h) (GaussianGammaUnitInverseSamples.actual_step_separated _ (denominator_positive h hD)))

theorem quotient_regular (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] lt b D) :
    Γ ⊢[PRAAx] pointCN GF (data a b N D) :=
  name_regular _ _ _ _ _ _ (quotient_input a b N D h hD)

theorem positive_neighbor_cross (a b D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] lt b D) :
    Γ ⊢[PRAAx] crossEquivalent gammaF gammaF
      (GaussianStirlingGammaLogarithm.gammaData (denominator b D+numerator a b D) (denominator b D))
      (GaussianGammaDigammaStep.neighborData (b+a) b D) := by
  let A := denominator b D+numerator a b D
  let B := denominator b D
  let C := GaussianGammaDigammaStep.neighborNumerator (b+a) b D
  let R := GaussianGammaDigammaStep.neighborDenominator b D
  have e : Γ ⊢[PRAAx] A ≐ C := by unfold A C denominator numerator GaussianGammaDigammaStep.neighborNumerator; ipra_ring
  have f : Γ ⊢[PRAAx] B ≐ R := mul_comm _ _
  have d : Γ ⊢[PRAAx] GaussianStirlingGammaLogarithm.gammaData A B ≐ GaussianStirlingGammaLogarithm.gammaData C R := by
    simpa only [GaussianStirlingGammaLogarithm.subst_gammaData,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (GaussianStirlingGammaLogarithm.gammaData (var 0) (var 1) : PTm 2)
        (σ := ![A,B]) (σ' := ![C,R]) (fun j => by fin_cases j <;> assumption)
  exact GaussianGammaInputProperness.code_data_cross gammaF _ _
    (GaussianStirlingGammaLogarithm.gamma_regular _ _ (shifted_source _ _ (neighbor_guard a b D h hD)))
    (GaussianStirlingGammaLogarithm.gamma_regular _ _
      (GaussianGammaDigammaStep.neighbor_source (b+a) b D (shifted_source a b h) (denominator_positive h hD))) d

theorem quotient_cross (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] lt b D) :
    Γ ⊢[PRAAx] crossEquivalent PF GF (productQuotientData a b N D) (GaussianGammaDigammaStep.stepQuotientData (b+a) b D) := by
  let a' := numerator a b D
  let b' := denominator b D
  have hn := neighbor_guard a b D h hD
  have hp := shifted_source a b h
  exact GaussianNamedDifferenceQuotientProperness.proper productF gammaF productF gammaF _ _ _ _ oneCode D
    (multiply_fast _ _ _ _ (constant_regular _) (negative_regular a' b' N hn))
    (GaussianStirlingGammaLogarithm.gamma_regular _ _
      (GaussianGammaDigammaStep.neighbor_source _ _ _ hp (denominator_positive h hD)))
    (multiply_fast _ _ _ _ (constant_regular _) (negative_regular a b N h))
    (GaussianStirlingGammaLogarithm.gamma_regular _ _ hp)
    (cross_trans _ _ _ _ _ _ (original_product a' b' N hn) (positive_neighbor_cross a b D h hD))
    (original_product a b N h)

theorem product_quotient_rate (p a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hD : Γ ⊢[PRAAx] lt b D)
    (hEuler : Γ ⊢[PRAAx] le (minimumDenominator p (b+a) b) D) : Γ ⊢[PRAAx]
    independentRate PF EF (productQuotientData a b N D) (GaussianGammaDigammaNative.derivativeData (b+a) b) one (unit p) :=
  GaussianNamedRateTransport.transport GF EF PF EF (GaussianGammaDigammaStep.stepQuotientData (b+a) b D)
    (GaussianGammaDigammaNative.derivativeData (b+a) b) (productQuotientData a b N D)
    (GaussianGammaDigammaNative.derivativeData (b+a) b) one (unit p) (unit_positive p)
    (GaussianGammaDigammaStep.step_rate p (b+a) b D (shifted_source a b h) hEuler)
    (quotient_cross a b N D h hD)
    (cross_refl _ _ (GaussianGammaDigammaNative.derivative_regular _ _ (shifted_source a b h)))

theorem actual_original_negative_Gamma_product_quotient_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((guard (var 1) (var 2) ⋏ (lt (var 2) (var 4) ⋏ le (minimumDenominator (var 0) (var 2+var 1) (var 2)) (var 4))) ⟶
        independentRate PF EF (productQuotientData (var 1) (var 2) (var 3) (var 4))
          (GaussianGammaDigammaNative.derivativeData (var 2+var 1) (var 2)) one (unit (var 0))) :=
  closeUniv 5 (.impI (product_quotient_rate _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalStep
