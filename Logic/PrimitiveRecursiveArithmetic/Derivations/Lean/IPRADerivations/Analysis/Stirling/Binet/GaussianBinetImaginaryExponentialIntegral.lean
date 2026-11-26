import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetExponentialIntegral
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerResidualRadius

/-!
# Actual compact antiderivative for purely imaginary input

The checked finite exponential antiderivative extends to both signed
imaginary frequencies, including the zero row. This supplies the
original panel bound on the oscillatory side of the cosine rectangle,
with no division by the frequency.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetImaginaryExponentialIntegral

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (normSq)
open GaussianBinetExponentialIntegral (nonpositiveRows finite_error numerator)
open GaussianBinetExponentialIntegralGrid (exponent value row)
open GaussianBinetExponentialPanel (nonpositive)
open GaussianCoefficientNameBounds (unit)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianRationalHorner (ofGaussian_represents)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qnegative qsub subst_qnegative)
open GaussianRationalReciprocal (bounded_negative)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalHorner (qmul)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (A B sign : PTm n) : PTm n := qnegative (argument zero A B sign)

@[simp] theorem subst_coefficient {m : ℕ} (σ : Fin n → PTm m) (A B sign : PTm n) :
    Syn.subst σ (coefficient A B sign) = coefficient (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ sign) := by
  simp only [coefficient,subst_qnegative,GaussianLogGammaEulerRepresentation.subst_argument,ConciseIPRA.PTm.subst_zero]

theorem coefficient_bound (A B sign R : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hs : Γ ⊢[PRAAx] sign ≐ zero ⋎ sign ≐ one) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] bounded (coefficient A B sign) R one := by
  let z := native zero A sign
  have radius : Γ ⊢[PRAAx] normSq z ≐ A*A :=
    (GaussianLogGammaEulerResidualRadius.native_norm zero A sign hs).eqTrans (by ipra_ring)
  have raw : Γ ⊢[PRAAx] le (A*A) (R*R*(B*B)) := le_congr (.eqRefl _) (by ipra_ring) (le_mul_mono hA hA)
  have scale : Γ ⊢[PRAAx] A*A ≐ (one*one)*(A*A) := by ipra_ring
  have norm : Γ ⊢[PRAAx] le (one*one*normSq z) (R*R*(B*B)) :=
    le_congr (scale.eqTrans (congrMul (.eqRefl _) radius.eqSymm)) (.eqRefl _) raw
  exact bounded_negative _ _ _ (le_refl one)
    (bounded_of_cleared _ z B R one hB (le_refl one) (ofGaussian_represents z B hB) norm)

theorem exponent_nonpositive (A B sign a b : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] nonpositive (exponent (coefficient A B sign) a b) :=
  GaussianBinetLaplaceExponential.exponent_nonpositive zero A B sign a b hB hb

theorem imaginary_finite_error (p A B sign R T N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hs : Γ ⊢[PRAAx] sign ≐ zero ⋎ sign ≐ one)
    (hA : Γ ⊢[PRAAx] le A (R*B)) (hN : Γ ⊢[PRAAx] le one N) (hS : Γ ⊢[PRAAx] le (R*T) N) :
    let q := coefficient A B sign
    Γ ⊢[PRAAx] distanceBounded (qmul q (value p q (R*T) T N)) (qsub (row p q (R*T) T one) qone)
      (numerator p R T N) (unit p*N) := by
  let q := coefficient A B sign
  have rows : Γ ⊢[PRAAx] nonpositiveRows q T N := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := le (var 0) (s N) :: Γ.map Fm.shift
    have bs : Δ ⊢[PRAAx] le one (s B) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hB.shift.wk
    have ns : Δ ⊢[PRAAx] le one (s N) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hN.shift.wk
    simpa only [nonpositiveRows,q,s,Δ,Syn.shift,subst_coefficient] using
      exponent_nonpositive (s A) (s B) (s sign) (s T*var 0) (s N) bs ns
  exact finite_error p q R T N (coefficient_bound A B sign R hB hs hA) hN hS rows
    (exponent_nonpositive A B sign T N hB hN)

theorem actual_Binet_imaginary_exponential_antiderivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (le one (var 2) ⟶ (var 3 ≐ zero ⋎ var 3 ≐ one) ⟶ le (var 1) (var 4*var 2) ⟶ le one (var 6) ⟶
      le (var 4*var 5) (var 6) ⟶
      distanceBounded (qmul (coefficient (var 1) (var 2) (var 3))
        (value (var 0) (coefficient (var 1) (var 2) (var 3)) (var 4*var 5) (var 5) (var 6)))
        (qsub (row (var 0) (coefficient (var 1) (var 2) (var 3)) (var 4*var 5) (var 5) one) qone)
        (numerator (var 0) (var 4) (var 5) (var 6)) (unit (var 0)*var 6)) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (imaginary_finite_error _ _ _ _ _ _ _ Prf.hyp0.wk.wk.wk.wk Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianBinetImaginaryExponentialIntegral
