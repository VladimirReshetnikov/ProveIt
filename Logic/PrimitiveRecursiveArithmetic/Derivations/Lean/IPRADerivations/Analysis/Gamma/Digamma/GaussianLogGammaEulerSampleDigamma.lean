import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerCommonDenominator
import IPRADerivations.Analysis.Gamma.Digamma.GaussianLogGammaEulerDigammaDerivative

/-!
# The digamma series as the limit of sampled log-Gamma quotients

At two independently retimed original samples, compute the common signed
rational chart and compare the actual punctured log-Gamma quotient to the
C27 digamma series at the base sample. The modulus is expressed solely in
terms of the original sample distance and their half-plane margins.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerSampleDigamma

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerCommonDenominator
  (admissionBudget commonImag commonReal displacement punctured quotientData radius_from_distance rateBudget sizeBound uniform_source)
open GaussianNamedRightHalfPlaneSigned (certificate sample sign)
open GaussianNamedInverseRate (independentRate rate_at rateDenominator rateNumerator)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalValueEquality (commonDen common_den_positive)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "quotientF" => GaussianLogGammaEulerDerivativeQuotient.nameF
local notation "digammaF" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF

def digammaData (q r : PTm n) : PTm n :=
  GaussianLogGammaEulerDigammaFractionsCofinal.data (commonReal q r) (commonImag q r) (commonDen q r) (sign q)

theorem quotient_rate (q r R S K P Qd : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hK : Γ ⊢[PRAAx] le one K) (hQ : Γ ⊢[PRAAx] le one Qd)
    (h : Γ ⊢[PRAAx] distanceBounded r q P Qd)
    (hne : Γ ⊢[PRAAx] (distanceBounded r q zero one ⟶ .bot))
    (hp : Γ ⊢[PRAAx] le (admissionBudget P K (sizeBound R S)) Qd) : Γ ⊢[PRAAx]
    independentRate quotientF digammaF (quotientData q r) (digammaData q r) (rateBudget P K) Qd := by
  let D := commonDen q r
  let E := GaussianLogGammaEulerDerivativeQuotient.errorNumerator
    (GaussianLogGammaEulerStepReciprocal.radius (displacement q r)) K
  have hn := punctured q r R S K hq hr hne
  have u := uniform_source q r R S K P Qd hq hr hK hQ h hn hp
  have bound := mul_le_mul_right (num 8*(K*K+two)) (radius_from_distance q r R S K P Qd hq hr hQ h hn)
  have radius : Γ ⊢[PRAAx] le (E*Qd) (rateBudget P K*D) :=
    le_congr (by unfold E GaussianLogGammaEulerDerivativeQuotient.errorNumerator; ipra_ring)
      (by unfold rateBudget D; ipra_ring) bound
  exact GaussianNamedRateRadius.weaken quotientF digammaF (quotientData q r) (digammaData q r)
    E D (rateBudget P K) Qd (common_den_positive q r) hQ radius
    (GaussianLogGammaEulerDigammaDerivative.uniform_rate _ _ _ _ _ _ _ _ _ u)

theorem quotient_modulus (q r R S K P Qd t : PTm n)
    (hq : Γ ⊢[PRAAx] certificate q R K) (hr : Γ ⊢[PRAAx] certificate r S K)
    (hK : Γ ⊢[PRAAx] le one K) (hQ : Γ ⊢[PRAAx] le one Qd)
    (h : Γ ⊢[PRAAx] distanceBounded r q P Qd)
    (hne : Γ ⊢[PRAAx] (distanceBounded r q zero one ⟶ .bot))
    (hp : Γ ⊢[PRAAx] le (admissionBudget P K (sizeBound R S)) Qd)
    (ht : Γ ⊢[PRAAx] le (rateBudget P K*unit t) Qd) : Γ ⊢[PRAAx]
    independentRate quotientF digammaF (quotientData q r) (digammaData q r) one (unit t) :=
  GaussianNamedRateRadius.weaken quotientF digammaF (quotientData q r) (digammaData q r) _ Qd one (unit t)
    hQ (unit_positive t) (le_congr (.eqRefl _) (one_mul Qd).eqSymm ht)
    (quotient_rate q r R S K P Qd hq hr hK hQ h hne hp)

theorem actual_retimed_quotient_modulus (f g : PR 2) (x y M i j P Qd t : PTm n)
    (hf : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source f x M)
    (hg : Γ ⊢[PRAAx] GaussianNamedRightHalfPlane.source g y M) :
    let q := sample f x M i
    let r := sample g y M j
    let K := two*M
    let R := GaussianNamedRightHalfPlane.radius f x
    let S := GaussianNamedRightHalfPlane.radius g y
    (Γ ⊢[PRAAx] le one Qd) →
    (Γ ⊢[PRAAx] distanceBounded r q P Qd) →
    (Γ ⊢[PRAAx] (distanceBounded r q zero one ⟶ .bot)) →
    (Γ ⊢[PRAAx] le (admissionBudget P K (sizeBound R S)) Qd) →
    (Γ ⊢[PRAAx] le (rateBudget P K*unit t) Qd) →
    (Γ ⊢[PRAAx] independentRate quotientF digammaF (quotientData q r) (digammaData q r) one (unit t)) := by
  dsimp only
  intro hQ h hne hp ht
  have hK : Γ ⊢[PRAAx] le one (two*M) := positive_product _ _ (zero_lt_succ _) hf.andE₂.andE₁
  exact quotient_modulus _ _ _ _ _ P Qd t
    (GaussianNamedRightHalfPlaneSigned.actual_retimed f x M i hf)
    (GaussianNamedRightHalfPlaneSigned.actual_retimed g y M j hg)
    hK hQ h hne hp ht

theorem actual_named_log_Gamma_sample_digamma_modulus_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let x := var 0
       let y := var 1
       let M := var 2
       let q := sample f x M (var 3)
       let r := sample g y M (var 4)
       let P := var 5
       let Qd := var 6
       let t := var 7
       let K := two*M
       let R := GaussianNamedRightHalfPlane.radius f x
       let S := GaussianNamedRightHalfPlane.radius g y
       (GaussianNamedRightHalfPlane.source f x M ⋏ GaussianNamedRightHalfPlane.source g y M) ⟶
       (le one Qd ⋏ (distanceBounded r q P Qd ⋏ ((distanceBounded r q zero one ⟶ .bot) ⋏
         (le (admissionBudget P K (sizeBound R S)) Qd ⋏ le (rateBudget P K*unit t) Qd)))) ⟶
       independentRate quotientF digammaF (quotientData q r) (digammaData q r) one (unit t)) := by
  refine closeUniv 8 (.impI (.impI ?_))
  exact actual_retimed_quotient_modulus f g _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerSampleDigamma
