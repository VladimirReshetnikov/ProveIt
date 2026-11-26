import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalExponentTaylorBuffer
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalTaylorProduct
import IPRADerivations.Analysis.Exponential.GaussianPolynomialExponentialLowJet
import IPRADerivations.Analysis.Polynomials.GaussianPolynomialProductLeftPadding

/-!
# Retained coefficient invariance of the stored Barnes Taylor product

At fixed prefactor precision and tail cutoff, each admitted coefficient
of the original exponent buffer is independent of its retained order.
The original finite exponential preserves this equality. Padding the
actual centered head to the queried coefficient degree permits the same
convolution comparison even if that degree exceeds the original head.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductOrderInvariance

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalExponentTaylorBuffer (buffer buffer_zero entry_at subst_buffer)
open GaussianBarnesCanonicalHigherRows (previous subst_previous)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalTaylorProduct (polynomial headPolynomial headDegree)
open GaussianPolynomialLowJetProduct (jetEqual product_reader)
open GaussianRationalLowCoefficientConvolution (exponentCoefficient exponent_inside)
open GaussianRationalPolynomialBuffers (leftPad)
open GaussianRationalPolynomialExponentialProductTruncation (exponentialPrefix exponential_prefix_length subst_exponentialPrefix)
open GaussianRationalPolynomialProduct (product)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private abbrev retainedExponential (q z R B r M : PTm n) : PTm n :=
  exponentialPrefix (buffer q z R B r M) (previous M) (previous M) (previous M)

private theorem input_jet (q z R B r M S e : PTm n)
    (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) : Γ ⊢[PRAAx]
    jetEqual (buffer q z R B r M) (previous M) (buffer q z R B r S) (previous S) e := by
  let s (a : PTm n) := Syn.shift a
  have shift_order {a : PTm n} (ha : Γ ⊢[PRAAx] le e (previous a)) :
      Γ.map Fm.shift ⊢[PRAAx] le (s e) (previous (s a)) := by
    simpa only [Fm.shift,Syn.shift,s,subst_le,subst_previous] using ha.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (s e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (s e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  have left := le_trans hi (shift_order hM).wk
  have right := le_trans hi (shift_order hS).wk
  have first := exponent_inside (buffer (s q) (s z) (s R) (s B) (s r) (s M)) (previous (s M)) (var 0) left
  have second := exponent_inside (buffer (s q) (s z) (s R) (s B) (s r) (s S)) (previous (s S)) (var 0) right
  simpa only [Δ,s,Syn.shift,subst_buffer,subst_previous,ConciseIPRA.PTm.subst_succ] using
    first.eqTrans ((entry_at (s q) (s z) (s R) (s B) (s r) (s M) (var 0) left).eqTrans
      ((entry_at (s q) (s z) (s R) (s B) (s r) (s S) (var 0) right).eqSymm.eqTrans second.eqSymm))

private theorem degree_bound (M : PTm n) : Γ ⊢[PRAAx] le (previous M) (previous M*previous M) :=
  le_congr (one_mul (previous M)) (.eqRefl _)
    (mul_le_mul_right (previous M) (zero_lt_succ (succ M)))

private theorem prefix_coefficient (q z R B r M S e : PTm n)
    (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) : Γ ⊢[PRAAx]
    exponentCoefficient (retainedExponential q z R B r M) (previous M) e ≐
      exponentCoefficient (retainedExponential q z R B r S) (previous S) e := by
  let C := buffer q z R B r M
  let D := buffer q z R B r S
  let N := previous M
  let K := previous S
  let L := GaussianRationalPolynomialExponential.polynomial C N N
  let T := GaussianRationalPolynomialExponential.polynomial D K K
  have left := (exponent_inside (retainedExponential q z R B r M) N e hM).eqTrans
    ((GaussianPolynomialLowPrefix.original_reader L (N*N) N e hM).eqTrans
      (exponent_inside L (N*N) e (le_trans hM (degree_bound M))).eqSymm)
  have right := (exponent_inside (retainedExponential q z R B r S) K e hS).eqTrans
    ((GaussianPolynomialLowPrefix.original_reader T (K*K) K e hS).eqTrans
      (exponent_inside T (K*K) e (le_trans hS (degree_bound S))).eqSymm)
  have coeff := GaussianPolynomialExponentialLowJet.exponential_coefficient C N D K N K e
    (input_jet q z R B r M S e hM hS) (buffer_zero q z R B r M) (buffer_zero q z R B r S)
    hM hS hM hS
  exact left.eqTrans (coeff.eqTrans right.eqSymm)

private theorem prefix_jet (q z R B r M S e : PTm n)
    (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) : Γ ⊢[PRAAx]
    jetEqual (retainedExponential q z R B r M) (previous M) (retainedExponential q z R B r S) (previous S) e := by
  let s (a : PTm n) := Syn.shift a
  have shift_order {a : PTm n} (ha : Γ ⊢[PRAAx] le e (previous a)) :
      Γ.map Fm.shift ⊢[PRAAx] le (s e) (previous (s a)) := by
    simpa only [Fm.shift,Syn.shift,s,subst_le,subst_previous] using ha.shift
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (succ (s e)) :: Γ.map Fm.shift
  have hi : Δ ⊢[PRAAx] le (var 0) (s e) := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  simpa only [retainedExponential,Δ,s,Syn.shift,subst_buffer,subst_previous,subst_exponentialPrefix,ConciseIPRA.PTm.subst_succ] using
    prefix_coefficient (s q) (s z) (s R) (s B) (s r) (s M) (s S) (var 0)
      (le_trans hi (shift_order hM).wk) (le_trans hi (shift_order hS).wk)

private theorem padded_reader (q z R B r M e : PTm n) (he : Γ ⊢[PRAAx] le e (previous M)) : Γ ⊢[PRAAx]
    entry (polynomial z R B (buffer q z R B r M) (previous M) (previous M)) (monus (previous M) e) ≐
      exponentCoefficient (product (leftPad (headPolynomial z R B) e) (retainedExponential q z R B r M)
        (e+headDegree R) (previous M)) ((e+headDegree R)+previous M) e := by
  let N := previous M
  let P := headPolynomial z R B
  let Q := retainedExponential q z R B r M
  let J := headDegree R
  have hP := GaussianBarnesCanonicalCenteredHead.polynomial_length (Γ := Γ) z B (initial R)
  have hQ := exponential_prefix_length (Γ := Γ) (buffer q z R B r M) N N N
  have hi : Γ ⊢[PRAAx] le e (J+N) := le_trans he (le_add_left N J)
  have read := GaussianRationalPolynomialExponentialProductTruncation.coefficient
    P (buffer q z R B r M) J N N e he
  exact read.eqTrans ((exponent_inside (product P Q J N) (J+N) e hi).eqSymm.eqTrans
    (GaussianPolynomialProductLeftPadding.original_reader P Q J N e e hP hQ hi).eqSymm)

theorem order_invariance (q z R B r M S e : PTm n)
    (hM : Γ ⊢[PRAAx] le e (previous M)) (hS : Γ ⊢[PRAAx] le e (previous S)) : Γ ⊢[PRAAx]
    entry (polynomial z R B (buffer q z R B r M) (previous M) (previous M)) (monus (previous M) e) ≐
      entry (polynomial z R B (buffer q z R B r S) (previous S) (previous S)) (monus (previous S) e) := by
  let P := leftPad (headPolynomial z R B) e
  let D := e+headDegree R
  have head : Γ ⊢[PRAAx] jetEqual P D P D e := .allI (.impI (.eqRefl _))
  have hD : Γ ⊢[PRAAx] le e D := le_add_right e (headDegree R)
  have product := product_reader P D (retainedExponential q z R B r M) (previous M) P D (retainedExponential q z R B r S) (previous S) e e
    head (prefix_jet q z R B r M S e hM hS) (le_refl e) hD hM hD hS
  exact (padded_reader q z R B r M e hM).eqTrans (product.eqTrans (padded_reader q z R B r S e hS).eqSymm)

theorem actual_retained_Barnes_Taylor_product_order_invariance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let q := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let r := var 4
     let M := var 5
     let S := var 6
     let e := var 7
     le e (previous M) ⟶ le e (previous S) ⟶
       entry (polynomial z R B (buffer q z R B r M) (previous M) (previous M)) (monus (previous M) e) ≐
         entry (polynomial z R B (buffer q z R B r S) (previous S) (previous S)) (monus (previous S) e)) :=
  closeUniv 8 (.impI (.impI (order_invariance (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7)
    Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTaylorProductOrderInvariance
