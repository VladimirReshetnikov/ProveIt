import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalExponentTaylorBuffer
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeFractionProperness
import IPRADerivations.Analysis.Barnes.Taylor.Coefficients.GaussianBarnesCanonicalTaylorTailFraction
import IPRADerivations.Foundations.SequenceEquality

/-!
# Exact chart independence of the stored Barnes exponent Taylor buffer

At fixed prefactor precision, cutoff, radius and order, every actual
coefficient depends only on the normalized Gaussian rational center.
Equality of the indexed body evaluations gives equality of the
actual descending coefficient buffers.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorBufferProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.MasterCertificate (sequence_decode)
open LeanProofs.IPRA.Foundations.SequenceEquality (agree sequence_equal)
open ComplexLogarithmRemainder (scale)
open GaussianBarnesCanonicalExponentTaylorBuffer
  (prefactorLinear linearCoefficient quadraticCoefficient highCoefficient coefficient buffer bufferBody bufferData descending_at)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalTaylorTailFraction (second_tail_equal higher_tail_equal)
open GaussianRationalHorner (ofGaussian qzero positive_product)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qsub_congr)
open RationalArithmetic (select)
open ConciseIPRA.PTm (succ)
open LeanProofs.IPRA.PTm (num monus)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "sg" => LeanProofs.IPRA.Signum.sg

theorem prefactor_linear_equal (q z w B D : PTm n) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] prefactorLinear q z B ≐ prefactorLinear q w D :=
  qadd_congr (.eqRefl _) (qmul_congr (.eqRefl _)
    (qadd_congr (.eqRefl _) (qmul_congr (qadd_congr he he) (.eqRefl _))))

theorem linear_equal (q z w R B D r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] linearCoefficient q z R B r ≐ linearCoefficient q w R D r :=
  qadd_congr (qadd_congr (prefactor_linear_equal q z w B D he)
    (qsub_congr (qmul_congr he (.eqRefl _)) (.eqRefl _)))
    (GaussianBarnesCanonicalDerivativeFractionProperness.finite_equal z w B D (initial R) r hB hD he)

theorem quadratic_equal (q z w R B D r : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] quadraticCoefficient q z R B r ≐ quadraticCoefficient q w R D r :=
  qadd_congr (.eqRefl _) (qmul_congr (.eqRefl _) (second_tail_equal z w B D (initial R) r hB hD he))

theorem higher_equal (z w R B D r j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] highCoefficient z R B r j ≐ highCoefficient w R D r j :=
  higher_tail_equal z w B D (initial R) j r hB hD he

theorem coefficient_equal (q z w R B D r e : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] coefficient q z R B r e ≐ coefficient q w R D r e := by
  ipra_congr (select (sg (var 0)) qzero
    (select (sg (monus (var 0) one)) (var 1) (select (sg (monus (var 0) two)) (var 2) (var 3))) : PTm 4)
    with [.eqRefl e, linear_equal q z w R B D r hB hD he, quadratic_equal q z w R B D r hB hD he,
      higher_equal z w R B D r (monus e (num 3)) hB hD he] using [coefficient,one,two]

theorem buffer_equal (q z w R B D r M : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) :
    Γ ⊢[PRAAx] buffer q z R B r M ≐ buffer q w R D r M := by
  refine sequence_equal bufferBody bufferBody (succ (previous M)) (bufferData q z R B r M) (bufferData q w R D r M)
    (.allI (.impI ?_))
  let sh (u : PTm n) := Syn.shift u
  let L := succ (previous (sh M))
  let Δ := lt (var 0) L :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hB.shift.wk
  have hd : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,sh,Fm.shift,Syn.shift] using hD.shift.wk
  have eq : Δ ⊢[PRAAx] ofGaussian (sh z) (sh B) ≐ ofGaussian (sh w) (sh D) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using he.shift.wk
  have inRange : Δ ⊢[PRAAx] lt i L := Prf.hyp0
  have index : Δ ⊢[PRAAx] le i (previous (sh M)) := (succ_monus_succ _ _).eqSymm.eqTrans inRange
  have x := (sequence_decode bufferBody (x := bufferData (sh q) (sh z) (sh R) (sh B) (sh r) (sh M)) inRange).eqSymm.eqTrans
    (descending_at (sh q) (sh z) (sh R) (sh B) (sh r) (sh M) i index)
  have y := (sequence_decode bufferBody (x := bufferData (sh q) (sh w) (sh R) (sh D) (sh r) (sh M)) inRange).eqSymm.eqTrans
    (descending_at (sh q) (sh w) (sh R) (sh D) (sh r) (sh M) i index)
  have m := coefficient_equal (sh q) (sh z) (sh w) (sh R) (sh B) (sh D) (sh r) (monus (previous (sh M)) i) hb hd eq
  simpa [agree,Δ,sh,L,i,Syn.shift] using x.eqTrans (m.eqTrans y.eqSymm)

theorem buffer_rescale (q z R B E r M : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] buffer q z R B r M ≐ buffer q (scale E z) R (E*B) r M :=
  buffer_equal q z (scale E z) R B (E*B) r M hB (positive_product _ _ hE hB)
    (GaussianGammaEncodingRescaling.fraction_rescale z B E hB hE).eqSymm

theorem actual_Barnes_exponent_Taylor_buffer_proper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let q := var 0
     let z := var 1
     let w := var 2
     let R := var 3
     let B := var 4
     let D := var 5
     let r := var 6
     let M := var 7
     (le one B ⋏ (le one D ⋏ (ofGaussian z B ≐ ofGaussian w D))) ⟶
       buffer q z R B r M ≐ buffer q w R D r M) :=
  closeUniv 8 (.impI (buffer_equal _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_Barnes_exponent_Taylor_buffer_rescaling_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let q := var 0
     let z := var 1
     let R := var 2
     let B := var 3
     let E := var 4
     let r := var 5
     let M := var 6
     (le one B ⋏ le one E) ⟶ buffer q z R B r M ≐ buffer q (scale E z) R (E*B) r M) :=
  closeUniv 7 (.impI (buffer_rescale _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalExponentTaylorBufferProperness
