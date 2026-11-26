import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.GaussianBinetArctangentResolvent
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerResidualRadius
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryLogDerivativeTail
import IPRADerivations.Analysis.Names.GaussianNamedRightHalfPlaneSigned

/-!
# Signed rational charts for the two arctangent poles

The exact poles `z±it` enter the original Laplace exponential
antiderivative through signed rational charts. A compact frequency
bound gives a uniform exponent radius and preserves the same real
margin over every frequency on the grid.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetArctangentSignedPole

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Foundations.GapDecision (zabs subst_zabs)
open ComplexLogarithmRemainder (code re im eval_re_code eval_im_code normSq scale bounded normSq_neg)
open GaussianBinetArctangentResolvent (pole poleNumerator signedTimeNumerator)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native source)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique represents_congr positive_product)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open GaussianRootAlgebra (equal equal_of_values normSq_equal re_add re_scale re_neg)
open GaussianSineProductImaginaryLogDerivative (axisNumerator)
open GaussianSineProductImaginaryLogDerivativeTail (axis_norm)
open PolynomialBisection (selector selector_cases selector_zero)
open RationalArithmetic (select select_zero select_one)
open RationalIntegerNormalization (positivePart negativePart parts_value)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def imagNumerator (s : Bool) (X Y D sign A B : PTm n) : PTm n := zabs (im (poleNumerator s X Y D sign A B))
def branch (s : Bool) (X Y D sign A B : PTm n) : PTm n := selector (im (poleNumerator s X Y D sign A B))

@[simp] theorem subst_imagNumerator {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (X Y D sign A B : PTm n) :
    Syn.subst σ (imagNumerator s X Y D sign A B) = imagNumerator s (Syn.subst σ X) (Syn.subst σ Y)
      (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B) := by
  simp only [imagNumerator,subst_zabs,ComplexLogarithmRemainder.subst_im,poleNumerator,
    ComplexLogarithmRemainder.subst_add,ComplexLogarithmRemainder.subst_scale,
    GaussianLogGammaEulerResidualDomain.subst_native,GaussianBinetArctangentResolvent.subst_signedTimeNumerator]

@[simp] theorem subst_branch {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (X Y D sign A B : PTm n) :
    Syn.subst σ (branch s X Y D sign A B) = branch s (Syn.subst σ X) (Syn.subst σ Y)
      (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B) := by
  change Syn.subst σ (eqb (positivePart (im (poleNumerator s X Y D sign A B))) zero) = _
  change _ = eqb (positivePart (im (poleNumerator s (Syn.subst σ X) (Syn.subst σ Y)
    (Syn.subst σ D) (Syn.subst σ sign) (Syn.subst σ A) (Syn.subst σ B)))) zero
  simp [poleNumerator]

private theorem signed_parts (u : ZT n) : Γ ⊢[PRAAx] ZT.eq (signedImag (zabs u) (selector u)) u := by
  refine .orE (selector_cases u) ?_ ?_
  · let Δ := (selector u ≐ zero) :: Γ
    have order : Δ ⊢[PRAAx] le (zero+u.neg) (u.pos+zero) := selector_zero Prf.hyp0
    have nz : Δ ⊢[PRAAx] negativePart u ≐ zero := le_congr (zero_add _) (add_zero _) order
    have mag : Δ ⊢[PRAAx] zabs u ≐ positivePart u := (congrAdd (.eqRefl _) nz).eqTrans (add_zero _)
    have l := (select_zero (Γ := Δ) (selector u) (zabs u) zero Prf.hyp0).eqTrans mag
    have r := (select_zero (Γ := Δ) (selector u) zero (zabs u) Prf.hyp0).eqTrans nz.eqSymm
    exact ZT.derive (by
      change 𝔞(select (selector u) (zabs u) zero) - 𝔞(select (selector u) zero (zabs u)) = ZT.toZ Δ u
      rw [natEq l, natEq r]
      exact ZT.toZ_eq (parts_value (Γ := Δ) u))
  · let Δ := (selector u ≐ one) :: Γ
    have pz : Δ ⊢[PRAAx] positivePart u ≐ zero := Foundations.BoundedReflection.eq_of_eqb Prf.hyp0
    have mag : Δ ⊢[PRAAx] zabs u ≐ negativePart u := (congrAdd pz (.eqRefl _)).eqTrans (zero_add _)
    have l := (select_one (Γ := Δ) (selector u) (zabs u) zero Prf.hyp0).eqTrans pz.eqSymm
    have r := (select_one (Γ := Δ) (selector u) zero (zabs u) Prf.hyp0).eqTrans mag
    exact ZT.derive (by
      change 𝔞(select (selector u) (zabs u) zero) - 𝔞(select (selector u) zero (zabs u)) = ZT.toZ Δ u
      rw [natEq l, natEq r]
      exact ZT.toZ_eq (parts_value (Γ := Δ) u))

theorem native_chart (s : Bool) (X Y D sign A B : PTm n) : Γ ⊢[PRAAx]
    equal (native (X*B) (imagNumerator s X Y D sign A B) (branch s X Y D sign A B))
      (poleNumerator s X Y D sign A B) := by
  apply equal_of_values
  · cases s <;> simp [poleNumerator,signedTimeNumerator,native,axisNumerator,re_add,re_scale,re_neg,eval_re_code,ZT.toZ_ofNat] <;> ring
  · simpa only [native,imagNumerator,branch,eval_im_code] using
      ZT.toZ_eq (signed_parts (Γ := Γ) (im (poleNumerator s X Y D sign A B)))

theorem argument_chart (s : Bool) (X Y D sign A B : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] argument (X*B) (imagNumerator s X Y D sign A B) (D*B) (branch s X Y D sign A B) ≐ pole s X Y D sign A B := by
  let P := poleNumerator s X Y D sign A B
  let Q := native (X*B) (imagNumerator s X Y D sign A B) (branch s X Y D sign A B)
  have hd := positive_product D B hD hB
  exact canonical_unique (ofGaussian Q (D*B)) (ofGaussian P (D*B)) P (D*B)
    (ofGaussian_canonical Q _ hd) (ofGaussian_canonical P _ hd) hd
    (represents_congr (.eqRefl _) (native_chart s X Y D sign A B) (.eqRefl _) (ofGaussian_represents Q _ hd))
    (ofGaussian_represents P _ hd)

theorem chart_source (s : Bool) (X Y D sign A B R U : PTm n) (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hB : Γ ⊢[PRAAx] le one B) (hU : Γ ⊢[PRAAx] le A (U*B)) :
    Γ ⊢[PRAAx] source (X*B) (imagNumerator s X Y D sign A B) (D*B) (branch s X Y D sign A B) (R+U) := by
  let p := signedTimeNumerator s A
  have hP : Γ ⊢[PRAAx] normSq p ≐ A*A := by
    cases s
    · exact axis_norm A
    · exact (normSq_neg (axisNumerator A)).eqTrans (axis_norm A)
  have pBound : Γ ⊢[PRAAx] bounded p (U*B) := le_congr hP.eqSymm (.eqRefl _) (le_mul_mono hU hU)
  have sum := ComplexLogarithmRemainder.bounded_add (ComplexLogarithmRemainder.bounded_scale B hz.andE₂)
    (ComplexLogarithmRemainder.bounded_scale D pBound)
  refine .andI (.andI (.andI (positive_product X B hz.andE₁.andE₁.andE₁ hB) (selector_cases _))
    (positive_product D B hz.andE₁.andE₂ hB)) ?_
  exact le_congr (normSq_equal (native_chart s X Y D sign A B)).eqSymm (by ipra_ring) sum

theorem preserved_margin (X D B K : PTm n) (h : Γ ⊢[PRAAx] le D (K*X)) :
    Γ ⊢[PRAAx] le (D*B) (K*(X*B)) := le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right B h)

end LeanProofs.IPRA.Analysis.GaussianBinetArctangentSignedPole
