import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerTaylorUniform
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerStepReciprocal
import IPRADerivations.Analysis.Names.Rates.GaussianBoundedConstantRationalRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateRadius
import IPRADerivations.Analysis.Gamma.Poles.GaussianGammaPoleDifferenceQuotient

/-!
# Actual punctured cofinal log-Gamma difference quotient

The quotient multiplies the actual cofinal increment by the literal
canonical reciprocal of the rational displacement. The reciprocal
certificate gives the exact D/E amplification of the Taylor estimate.
The displacement cancels in the weighted cofinal slope. A computed
integer displacement radius gives a linear quotient error.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDerivativeQuotient

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerArgumentIncrement (step)
open GaussianLogGammaEulerStepReciprocal
  (certificate certified_step lower numerator radius step_inverse_identity)
open GaussianLogGammaEulerTaylorCofinal
  (incrementF incrementData weightedF weightedData increment_regular weighted_regular)
open GaussianLogGammaEulerTaylorRows (coefficient)
open GaussianNameArithmetic (multiplyData multiplyF)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (oneF one_fast multiply_one_left)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (reciprocal qone)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "source" => GaussianRightHalfPlaneLogarithm.source
local notation "S" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "sd" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "BProduct" => GaussianBoundedConstantProductName.nameF
local notation "bpData" => GaussianBoundedConstantProductName.data

def nameF : PR 2 := BProduct incrementF

def data (A B neg a b sign D : PTm n) : PTm n :=
  bpData D (reciprocal (step A B neg a b sign D)) (incrementData A B neg a b sign D)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (A B neg a b sign D : PTm n) :
    Syn.subst σ (data A B neg a b sign D) =
      data (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ neg)
        (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ sign) (Syn.subst σ D) := by simp [data]

def errorNumerator (H K : PTm n) : PTm n := num 8*H*(K*K+two)

theorem sample_at (p A B neg a b sign D : PTm n) : Γ ⊢[PRAAx]
    ap2 nameF p (data A B neg a b sign D) ≐
      qmul (reciprocal (step A B neg a b sign D))
        (ap2 incrementF (GaussianBoundedConstantProductName.clock p D) (incrementData A B neg a b sign D)) :=
  GaussianBoundedConstantProductName.sample_at incrementF p D _ _

private theorem inverse_bound (A B neg a b sign D : PTm n) (h : Γ ⊢[PRAAx] certificate A B neg a b sign D) :
    Γ ⊢[PRAAx] bounded (reciprocal (step A B neg a b sign D)) D one := by
  let E := lower (numerator A B neg a b sign)
  have hE : Γ ⊢[PRAAx] le one E := h.andE₁
  exact bounded_radius_mono _ _ E _ _ hE (le_refl one) (le_mul_mono (le_refl D) hE)
    h.andE₂.andE₂.andE₂.andE₂

theorem regular (A B neg a b sign D : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign)
    (cert : Γ ⊢[PRAAx] certificate A B neg a b sign D) : Γ ⊢[PRAAx]
    pointCN nameF (data A B neg a b sign D) :=
  GaussianBoundedConstantProductName.name_regular incrementF D _ _
    (.andI (increment_regular A B neg a b sign D h k) (inverse_bound A B neg a b sign D cert))

/-- The opposite endpoint in the scaled Taylor comparison is the
literal weighted name multiplied by the same inverse step. -/
theorem weighted_cancel (A B neg a b sign D : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (cert : Γ ⊢[PRAAx] certificate A B neg a b sign D) :
    Γ ⊢[PRAAx] crossEquivalent (BProduct weightedF) S
      (bpData D (reciprocal (step A B neg a b sign D)) (weightedData A B neg a b sign D))
      (sd A B D neg) := by
  let c := step A B neg a b sign D
  let v := reciprocal c
  let x := sd A B D neg
  let y := weightedData A B neg a b sign D
  let z := multiplyData constantF S (qmul v c) x
  let ordinary := multiplyData constantF weightedF v y
  have hx := GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular A B D neg h
  have hy := weighted_regular A B neg a b sign D h
  have first := GaussianBoundedConstantProductName.ordinary_product_identity weightedF D v y
    (.andI hy (inverse_bound A B neg a b sign D cert))
  have merge := GaussianGammaEulerShift.merge_head S v c x hx
  have q : Γ ⊢[PRAAx] qmul v c ≐ qone :=
    (GaussianRationalPowerAlgebra.qmul_commutative v c).eqTrans (step_inverse_identity A B neg a b sign D cert)
  have unitName := GaussianGammaPoleDifferenceQuotient.constant_unit_cross (qmul v c) x q
  have reduced := multiply_cross constantF oneF S S (qmul v c) x x x
    (constant_regular _) (one_fast x) hx hx unitName (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ ordinary _ first (cross_trans _ weightedF _ _ z _ merge
    (cross_trans weightedF (multiplyF oneF S) S z _ _ reduced (multiply_one_left S x hx)))

/-- Multiply the leading Taylor radius by the certified D/E while
retaining the two original dyadic observation allowances. -/
theorem exact_rate_of_taylor (A B neg a b sign D H K : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign)
    (cert : Γ ⊢[PRAAx] certificate A B neg a b sign D)
    (ht : Γ ⊢[PRAAx] independentRate incrementF weightedF (incrementData A B neg a b sign D)
      (weightedData A B neg a b sign D) (coefficient H K) (D*D)) :
    Γ ⊢[PRAAx] independentRate nameF S (data A B neg a b sign D) (sd A B D neg)
      (D*coefficient H K) (lower (numerator A B neg a b sign)*(D*D)) := by
  let E := lower (numerator A B neg a b sign)
  let c := reciprocal (step A B neg a b sign D)
  let x := incrementData A B neg a b sign D
  let y := weightedData A B neg a b sign D
  let u := data A B neg a b sign D
  let v := bpData D c y
  have hD := h.andE₂
  have hE : Γ ⊢[PRAAx] le one E := cert.andE₁
  have hD2 := positive_product D D hD hD
  have hED2 := positive_product E (D*D) hE hD2
  have hClock : Γ ⊢[PRAAx] le D (D*E) :=
    le_congr (one_mul D) (mul_comm E D) (mul_le_mul_right D hE)
  have hr := GaussianBoundedConstantRationalRate.original_rate incrementF weightedF D c x y D E
    (coefficient H K) (D*D) hE hD2 hClock cert.andE₂.andE₂.andE₂.andE₂ ht
  exact GaussianNamedRateTransport.transport nameF (BProduct weightedF) nameF S u v u (sd A B D neg)
    (D*coefficient H K) (E*(D*D)) hED2 hr (cross_refl nameF u (regular A B neg a b sign D h k cert))
    (cross_symm _ _ _ _ (weighted_cancel A B neg a b sign D h cert))

theorem reduced_rate_of_taylor (A B neg a b sign D H K : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (k : Γ ⊢[PRAAx] source a D sign)
    (cert : Γ ⊢[PRAAx] certificate A B neg a b sign D)
    (hH : Γ ⊢[PRAAx] le H (two*lower (numerator A B neg a b sign)))
    (ht : Γ ⊢[PRAAx] independentRate incrementF weightedF (incrementData A B neg a b sign D)
      (weightedData A B neg a b sign D) (coefficient H K) (D*D)) :
    Γ ⊢[PRAAx] independentRate nameF S (data A B neg a b sign D) (sd A B D neg) (errorNumerator H K) D := by
  let E := lower (numerator A B neg a b sign)
  have hD := h.andE₂
  have hED := positive_product E (D*D) cert.andE₁ (positive_product D D hD hD)
  have comp : Γ ⊢[PRAAx] le ((D*coefficient H K)*D) (errorNumerator H K*(E*(D*D))) := by
    unfold coefficient errorNumerator
    ipra_le 4*𝔞(H)*𝔞(K*K+two)*𝔞(D)*𝔞(D)*sl hH
  exact GaussianNamedRateRadius.weaken nameF S _ _ _ _ _ _ hED hD comp
    (exact_rate_of_taylor A B neg a b sign D H K h k cert ht)

theorem reduced_rate (A B neg a b sign D H J M K : PTm n)
    (h : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmIncrementBound.input A B neg a b sign D H J M)
    (hK : Γ ⊢[PRAAx] le D (K*A))
    (hn : Γ ⊢[PRAAx] le one (normSq (numerator A B neg a b sign)))
    (hH : Γ ⊢[PRAAx] le H (two*lower (numerator A B neg a b sign))) :
    Γ ⊢[PRAAx] independentRate nameF S (data A B neg a b sign D) (sd A B D neg) (errorNumerator H K) D :=
  reduced_rate_of_taylor A B neg a b sign D H K h.andE₁.andE₁ h.andE₁.andE₂.andE₁
    (certified_step A B neg a b sign D h.andE₁.andE₁.andE₂ hn) hH
    (GaussianLogGammaEulerTaylorCofinal.independent_rate A B neg a b sign D H J M K h hK)

def uniformSource (A B neg a b sign D K C : PTm n) : Fm PTm n :=
  GaussianLogGammaEulerTaylorUniform.source A B neg a b sign D (radius (numerator A B neg a b sign)) K C ⋏
    le one (normSq (numerator A B neg a b sign))

theorem uniform_rate (A B neg a b sign D K C : PTm n)
    (h : Γ ⊢[PRAAx] uniformSource A B neg a b sign D K C) :
    Γ ⊢[PRAAx] independentRate nameF S (data A B neg a b sign D) (sd A B D neg)
      (errorNumerator (radius (numerator A B neg a b sign)) K) D := by
  let H := radius (numerator A B neg a b sign)
  have hs : Γ ⊢[PRAAx] GaussianLogGammaEulerTaylorUniform.source A B neg a b sign D H K C := h.andE₁
  have cert := certified_step A B neg a b sign D hs.andE₁.andE₂ h.andE₂
  exact reduced_rate_of_taylor A B neg a b sign D H K hs.andE₁ hs.andE₂.andE₁ cert cert.andE₂.andE₂.andE₁
    (GaussianLogGammaEulerTaylorUniform.independent_rate A B neg a b sign D H K C hs)

theorem uniform_observations (p q A B neg a b sign D K C : PTm n)
    (h : Γ ⊢[PRAAx] uniformSource A B neg a b sign D K C) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B neg a b sign D)) (ap2 S q (sd A B D neg))
      (rateNumerator (errorNumerator (radius (numerator A B neg a b sign)) K) D p q) (rateDenominator D p q) :=
  rate_at nameF S _ _ _ _ p q (uniform_rate A B neg a b sign D K C h)

theorem modulus_rate (r A B neg a b sign D K C : PTm n)
    (h : Γ ⊢[PRAAx] uniformSource A B neg a b sign D K C)
    (hsmall : Γ ⊢[PRAAx] le (errorNumerator (radius (numerator A B neg a b sign)) K*unit r) D) :
    Γ ⊢[PRAAx] independentRate nameF S (data A B neg a b sign D) (sd A B D neg) one (unit r) :=
  GaussianNamedRateRadius.weaken nameF S _ _ _ _ _ _ h.andE₁.andE₁.andE₂ (unit_positive r)
    (le_congr (.eqRefl _) (one_mul D).eqSymm hsmall) (uniform_rate A B neg a b sign D K C h)

theorem modulus_observations (p q r A B neg a b sign D K C : PTm n)
    (h : Γ ⊢[PRAAx] uniformSource A B neg a b sign D K C)
    (hsmall : Γ ⊢[PRAAx] le (errorNumerator (radius (numerator A B neg a b sign)) K*unit r) D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 nameF p (data A B neg a b sign D)) (ap2 S q (sd A B D neg))
      (rateNumerator one (unit r) p q) (rateDenominator (unit r) p q) :=
  rate_at nameF S _ _ _ _ p q (modulus_rate r A B neg a b sign D K C h hsmall)

theorem actual_uniform_cofinal_log_Gamma_difference_quotient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (uniformSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        independentRate nameF S (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (sd (var 0) (var 1) (var 6) (var 2))
          (errorNumerator (radius (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) (var 7))
          (var 6)) :=
  closeUniv 9 (.impI (uniform_rate _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_uniform_cofinal_log_Gamma_difference_quotient_modulus_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
      (uniformSource (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        le (errorNumerator (radius (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5))) (var 7)*unit (var 9)) (var 6) ⟶
        independentRate nameF S (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6))
          (sd (var 0) (var 1) (var 6) (var 2)) one (unit (var 9))) :=
  closeUniv 10 (.impI (.impI (modulus_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDerivativeQuotient
