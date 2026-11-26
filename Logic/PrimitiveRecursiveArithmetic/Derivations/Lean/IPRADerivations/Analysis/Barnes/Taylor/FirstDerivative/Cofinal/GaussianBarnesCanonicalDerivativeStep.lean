import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.NamedValues.GaussianBarnesCanonicalValueDerivative
import IPRADerivations.Analysis.Gamma.GaussianGammaEncodingRescaling

/-!
# Certified nonzero steps at every Barnes rational argument

Refine the original rational encoding of the base point to give room
for the real step with numerator one. A unit of extra disk radius
contains the shifted point. The resulting step meets the derivative
precision contract at any internal precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeStep

open_ipra
open ComplexLogarithmRemainder (add scale normSq normSq_one oneCode bounded bounded_scale bounded_add bounded_mono)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial_positive)
open GaussianBarnesCanonicalValueDerivative (stepGain numerator denominator precision_rate)
open GaussianCoefficientNameBounds (unit)
open GaussianL1 (norm1_one)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (ofGaussian positive_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def refinement (R p : PTm n) : PTm n :=
  stepGain (succ R)+(numerator (succ R) oneCode+one)*unit p+one

def nativeBase (z R p : PTm n) : PTm n := scale (refinement R p) z
def nativeDenominator (R B p : PTm n) : PTm n := refinement R p*B

def certificateAt (z R B p A : PTm n) : Fm PTm n :=
  let w := scale A z
  let E := A*B
  let S := succ R
  (ofGaussian w E ≐ ofGaussian z B) ⋏
    (le (unit p) E ⋏
      (GaussianBarnesCanonicalValueDerivative.input w oneCode S E ⋏ le (numerator S oneCode*unit p) (denominator S E)))

def certificate (z R B p : PTm n) : Fm PTm n := certificateAt z R B p (refinement R p)

theorem at_refinement (z R B p A : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hA : Γ ⊢[PRAAx] le (refinement R p) A) : Γ ⊢[PRAAx] certificateAt z R B p A := by
  let E := A*B
  let w := scale A z
  let S := succ R
  let C := numerator S oneCode
  let t := unit p
  have positive : Γ ⊢[PRAAx] le one A := le_trans (le_add_left _ _) hA
  have hE := positive_product _ _ positive hz.andE₁
  have grow : Γ ⊢[PRAAx] le A E :=
    le_congr (one_mul A) (mul_comm _ _) (mul_le_mul_right A hz.andE₁)
  have enough := le_trans hA grow
  have inside : Γ ⊢[PRAAx] bounded w (R*E) :=
    le_congr (.eqRefl _) (by change Γ ⊢[PRAAx] (A*(R*B))*(A*(R*B)) ≐ (R*(A*B))*(R*(A*B)); ipra_ring)
      (bounded_scale A hz.andE₂)
  have base : Γ ⊢[PRAAx] source w S E :=
    .andI hE (bounded_mono inside (mul_le_mul_right E (le_succ_self R)))
  have step : Γ ⊢[PRAAx] bounded (oneCode : PTm n) E :=
    bounded_mono (le_congr normSq_one.eqSymm (one_mul one).eqSymm (le_refl one)) hE
  have endRadius : Γ ⊢[PRAAx] R*E+E ≐ S*E := by change Γ ⊢[PRAAx] R*E+E ≐ succ R*E; ipra_ring
  have shifted : Γ ⊢[PRAAx] source (add w oneCode) S E :=
    .andI hE (le_congr (.eqRefl _) (congrMul endRadius endRadius) (bounded_add inside step))
  have hn : Γ ⊢[PRAAx] le one (normSq (oneCode : PTm n)) :=
    le_congr (.eqRefl _) normSq_one.eqSymm (le_refl one)
  have lead : Γ ⊢[PRAAx] le (stepGain S) (refinement R p) := le_trans (le_add_right _ _) (le_add_right _ _)
  have hMargin : Γ ⊢[PRAAx] le (stepGain S*GaussianL1.norm1 oneCode) E :=
    le_congr ((congrMul (.eqRefl _) norm1_one).eqTrans (by ipra_ring)).eqSymm (.eqRefl _)
      (le_trans lead enough)
  have middle : Γ ⊢[PRAAx] le ((C+one)*t) E := le_trans (le_add_left _ _) (le_trans (le_add_right _ _) enough)
  have small : Γ ⊢[PRAAx] le t E :=
    le_trans (le_congr (one_mul t) (.eqRefl _) (mul_le_mul_right t (le_add_left one C))) middle
  have money : Γ ⊢[PRAAx] le (C*t) E :=
    le_trans (mul_le_mul_right t (le_add_right C one)) middle
  have den : Γ ⊢[PRAAx] le E (denominator S E) :=
    le_congr (one_mul E) (mul_comm _ _) (mul_le_mul_right E (initial_positive S))
  exact .andI (GaussianGammaEncodingRescaling.fraction_rescale z B A hz.andE₁ positive)
    (.andI small (.andI (GaussianBarnesCanonicalValueDerivative.input_of_margin w oneCode S E base shifted hn hMargin)
      (le_trans money den)))

theorem certified (z R B p : PTm n) (hz : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] certificate z R B p :=
  at_refinement z R B p (refinement R p) hz (le_refl _)

theorem quotient_precision (z R B p : PTm n) (hz : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] independentRate GaussianBarnesCanonicalValueDerivative.quotientF GaussianBarnesCanonicalValueDerivative.nameF
      (GaussianBarnesCanonicalValueDerivative.quotientData (nativeBase z R p) oneCode (succ R) (nativeDenominator R B p))
      (GaussianBarnesCanonicalValueDerivative.data (nativeBase z R p) (succ R) (nativeDenominator R B p)) one (unit p) := by
  have h := certified z R B p hz
  exact precision_rate _ _ _ _ _ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂

theorem actual_Barnes_arbitrarily_small_certified_rational_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ certificate (var 0) (var 1) (var 2) (var 3)) :=
  closeUniv 4 (.impI (certified _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDerivativeStep
