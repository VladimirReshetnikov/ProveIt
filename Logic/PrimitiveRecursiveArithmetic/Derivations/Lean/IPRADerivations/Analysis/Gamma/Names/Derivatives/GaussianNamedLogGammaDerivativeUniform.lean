import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.GaussianNamedLogGammaDigammaDerivative
import IPRADerivations.Analysis.Names.Apartness.GaussianNamedMinimumApartness

/-!
# Uniform derivative modulus from a comparable apartness witness

Use the smaller of the given upper distance and the distance inferred
from a comparable witness. This cancels the inverse size in the error,
leaving a linear bound in the original upper distance. The actual
quotient is independent of the choice of apartness witness.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedLogGammaDerivativeUniform

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianLogGammaEulerCommonDenominator (admissionBudget sizeBound)
open GaussianNameArithmetic (multiplyF multiplyData multiply_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_to_diagonal)
open GaussianNameReciprocal (apart nameData name_fast)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedLogGammaDigammaDerivative (data nameF rate)
open GaussianNamedLogGammaTaylorEstimate (admission input quadraticBudget)
open GaussianNamedMinimumApartness (first difference_comparable inverse_scale)
open GaussianRationalHorner (positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "stepF" => GaussianNamedDifference.nameF
local notation "stepData" => GaussianNamedDifference.data
local notation "psiF" => GaussianLogGammaEulerNamedDigamma.nameF
local notation "psiData" => GaussianLogGammaEulerNamedDigamma.data

def budget (P K : PTm n) : PTm n := num 192 * P * (K*K+two)

theorem witness_independent (f g : PR 2) (x y M S a b : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianLogGammaEulerNamed.source f x M S)
    (hg : Γ ⊢[PRAAx] GaussianLogGammaEulerNamed.source g y M S)
    (ha : Γ ⊢[PRAAx] apart (stepF g f) a (stepData y x))
    (hb : Γ ⊢[PRAAx] apart (stepF g f) b (stepData y x)) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f g) (nameF f g) (data f g x y M S a) (data f g x y M S b) := by
  let H := stepF g f
  let z := stepData y x
  let J := GaussianNameReciprocal.nameF H
  let F := GaussianNamedLogGammaTaylorEstimate.incrementF f g
  let u := GaussianNamedLogGammaTaylorEstimate.incrementData x y M S
  have hz := GaussianNamedDifference.name_regular g f y x hg.andE₁.andE₁ hf.andE₁.andE₁
  have hi := GaussianNameReciprocal.names_equivalent H H a b z z hz hz ha hb
    (cross_to_diagonal H H z z (cross_refl H z hz))
  have hu : Γ ⊢[PRAAx] pointCN F u := GaussianNamedDifference.name_regular _ _ _ _
    (GaussianLogGammaEulerNamed.name_regular g y M S hg) (GaussianLogGammaEulerNamed.name_regular f x M S hf)
  exact multiply_equivalent J J F F (nameData a z) (nameData b z) u u
    (name_fast H a z hz ha) (name_fast H b z hz hb) hu hu
    (cross_to_diagonal _ _ _ _ hi) (cross_to_diagonal _ _ _ _ (cross_refl _ _ hu))

private theorem admission_controls_radius (P K C Q : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (h : Γ ⊢[PRAAx] le (admission P K C) Q) : Γ ⊢[PRAAx] le P Q := by
  have hB := positive_product _ _ (le_add_left one C) (positive_product K K hK hK)
  have hC : Γ ⊢[PRAAx] le one (num 512*((C+one)*(K*K))) :=
    positive_product _ _ (by ipra_le 511) hB
  exact le_trans (le_congr (by ipra_ring) (by unfold admission admissionBudget; ipra_ring)
    (le_mul_mono (le_refl P) hC)) h

private theorem replace_admission (P K C Q U : PTm n) (hQ : Γ ⊢[PRAAx] le one Q)
    (h : Γ ⊢[PRAAx] le (admission P K C) Q) (hh : Γ ⊢[PRAAx] le (num 6*Q) (P*U)) :
    Γ ⊢[PRAAx] le (admission (num 6) K C) U := by
  apply RationalValueBounds.positive_cancel (c := Q) hQ
  unfold admission admissionBudget at h ⊢
  ipra_le 512*(𝔞(C)+1)*𝔞(K)^2*sl hh+𝔞(U)*sl h

private theorem comparison_on_given_radius (f g : PR 2) (x y M S P Q b : PTm n)
    (h : Γ ⊢[PRAAx] input f g x y M S P Q)
    (hb : Γ ⊢[PRAAx] apart (stepF g f) b (stepData y x))
    (hp : Γ ⊢[PRAAx] le (P*unit b) (num 6*Q)) : Γ ⊢[PRAAx]
    independentRate (nameF f g) (psiF f) (data f g x y M S b) (psiData x M S) (budget P (two*M)) Q := by
  let K := two*M
  have hQ := h.andE₂.andE₂.andE₁
  have formula : Γ ⊢[PRAAx] le ((two*unit b*quadraticBudget P K)*Q) (budget P K*(Q*Q)) := by
    unfold quadraticBudget budget
    ipra_le 32*𝔞(P)*𝔞(K*K+two)*𝔞(Q)*sl hp
  have hcoef := congrMul (inverse_scale (Γ := Γ) b) (.eqRefl (quadraticBudget P K))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product Q Q hQ hQ) hQ
    (le_congr (congrMul hcoef.eqSymm (.eqRefl _)) (.eqRefl _) formula) (rate f g x y M S P Q b h hb)

private theorem comparison_on_witness_radius (f g : PR 2) (x y M S P Q b : PTm n)
    (h : Γ ⊢[PRAAx] input f g x y M S P Q)
    (hb : Γ ⊢[PRAAx] apart (stepF g f) b (stepData y x))
    (hupper : Γ ⊢[PRAAx] independentRate g f y x (num 6) (unit b))
    (hp : Γ ⊢[PRAAx] le (num 6*Q) (P*unit b)) : Γ ⊢[PRAAx]
    independentRate (nameF f g) (psiF f) (data f g x y M S b) (psiData x M S) (budget P (two*M)) Q := by
  let K := two*M
  let U := unit b
  have hu : Γ ⊢[PRAAx] le one U := unit_positive b
  have hQ := h.andE₂.andE₂.andE₁
  have hr : Γ ⊢[PRAAx] input f g x y M S (num 6) U :=
    .andI h.andE₁ (.andI h.andE₂.andE₁ (.andI hu
      (.andI (replace_admission P K (sizeBound S S) Q U hQ h.andE₂.andE₂.andE₂.andE₁ hp) hupper)))
  have formula : Γ ⊢[PRAAx] le ((two*U*quadraticBudget (num 6) K)*Q) (budget P K*(U*U)) := by
    unfold quadraticBudget budget
    ipra_le 192*𝔞(U)*𝔞(K*K+two)*sl hp
  have hcoef := congrMul (inverse_scale (Γ := Γ) b) (.eqRefl (quadraticBudget (num 6) K))
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ (positive_product U U hu hu) hQ
    (le_congr (congrMul hcoef.eqSymm (.eqRefl _)) (.eqRefl _) formula) (rate f g x y M S (num 6) U b hr hb)

theorem comparable_witness_rate (f g : PR 2) (x y M S P Q a b : PTm n)
    (h : Γ ⊢[PRAAx] input f g x y M S P Q)
    (ha : Γ ⊢[PRAAx] apart (stepF g f) a (stepData y x))
    (hb : Γ ⊢[PRAAx] apart (stepF g f) b (stepData y x))
    (hupper : Γ ⊢[PRAAx] b ≐ zero ⋎ independentRate g f y x (num 6) (unit b)) : Γ ⊢[PRAAx]
    independentRate (nameF f g) (psiF f) (data f g x y M S a) (psiData x M S) (budget P (two*M)) Q := by
  have hK := positive_product two M (le_succ_self one) h.andE₁.andE₁.andE₂.andE₁
  have hPQ := admission_controls_radius P (two*M) (sizeBound S S) Q hK h.andE₂.andE₂.andE₂.andE₁
  have coarse : Γ ⊢[PRAAx] le (P*one) (num 6*Q) := by ipra_le sl hPQ+5*𝔞(Q)
  have hbRate : Γ ⊢[PRAAx] independentRate (nameF f g) (psiF f) (data f g x y M S b) (psiData x M S)
      (budget P (two*M)) Q := by
    refine hupper.orE ?_ ?_
    · have e : (b ≐ zero) :: Γ ⊢[PRAAx] unit b ≐ unit zero := congrAp2 powF Prf.hyp0 (.eqRefl two)
      have eu : (b ≐ zero) :: Γ ⊢[PRAAx] unit b ≐ one := e.eqTrans (pw_zero two)
      exact comparison_on_given_radius f g x y M S P Q b h.wk hb.wk
        (le_congr (congrMul (.eqRefl P) eu.eqSymm) (.eqRefl _) coarse.wk)
    · exact (le_total (P*unit b) (num 6*Q)).orE
        (comparison_on_given_radius f g x y M S P Q b h.wk.wk hb.wk.wk Prf.hyp0)
        (comparison_on_witness_radius f g x y M S P Q b h.wk.wk hb.wk.wk Prf.hyp1 Prf.hyp0)
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ h.andE₂.andE₂.andE₁ hbRate
    (witness_independent f g x y M S a b h.andE₁ h.andE₂.andE₁ ha hb)
    (cross_refl _ _ (GaussianLogGammaEulerNamedDigamma.name_regular f x M S h.andE₁))

theorem uniform_rate (f g : PR 2) (x y M S P Q a : PTm n)
    (h : Γ ⊢[PRAAx] input f g x y M S P Q)
    (ha : Γ ⊢[PRAAx] apart (stepF g f) a (stepData y x)) : Γ ⊢[PRAAx]
    independentRate (nameF f g) (psiF f) (data f g x y M S a) (psiData x M S) (budget P (two*M)) Q := by
  let b := first (stepF g f) a (stepData y x)
  have c := difference_comparable g f y x a h.andE₂.andE₁.andE₁.andE₁ h.andE₁.andE₁.andE₁ ha
  exact comparable_witness_rate f g x y M S P Q a b h ha c.andE₁ c.andE₂

theorem modulus (f g : PR 2) (x y M S P Q a r : PTm n)
    (h : Γ ⊢[PRAAx] input f g x y M S P Q)
    (ha : Γ ⊢[PRAAx] apart (stepF g f) a (stepData y x))
    (hsmall : Γ ⊢[PRAAx] le (budget P (two*M)*unit r) Q) : Γ ⊢[PRAAx]
    independentRate (nameF f g) (psiF f) (data f g x y M S a) (psiData x M S) one (unit r) :=
  GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ h.andE₂.andE₂.andE₁ (unit_positive r)
    (le_congr (.eqRefl _) (one_mul _).eqSymm hsmall) (uniform_rate f g x y M S P Q a h ha)

theorem actual_named_log_Gamma_uniform_derivative_rate_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
      (input f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        apart (stepF g f) (var 6) (stepData (var 1) (var 0)) ⟶
        independentRate (nameF f g) (psiF f) (data f g (var 0) (var 1) (var 2) (var 3) (var 6))
          (psiData (var 0) (var 2) (var 3)) (budget (var 4) (two*var 2)) (var 5)) :=
  closeUniv 7 (.impI (.impI (uniform_rate f g _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem actual_named_log_Gamma_uniform_derivative_modulus_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (input f g (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
        apart (stepF g f) (var 6) (stepData (var 1) (var 0)) ⟶
        le (budget (var 4) (two*var 2)*unit (var 7)) (var 5) ⟶
        independentRate (nameF f g) (psiF f) (data f g (var 0) (var 1) (var 2) (var 3) (var 6))
          (psiData (var 0) (var 2) (var 3)) one (unit (var 7))) :=
  closeUniv 8 (.impI (.impI (.impI (modulus f g _ _ _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedLogGammaDerivativeUniform
