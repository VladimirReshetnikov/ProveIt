import Mathlib
import ConciseIPRA.NativeBiInterpretation
import IPRADerivations.Core.SumLemmas
import IPRADerivations.Core.MultiSums

/-!
# Object-language endpoints for expected value in iPRA

STATUS: uncompiled implementation scaffold.  It contains no `sorry` and does
not postulate any expected-value theorem.  A completed development must
construct the `InternalProof` records below.
-/

namespace ExpectedValueIPRA.ObjectLanguage

open LeanProofs.ConciseIPRA
open LeanProofs.ConciseIPRA.Syn
open scoped LeanProofs.ConciseIPRA.Fm

/-- Standard semantics of primitive-recursive syntax. -/
def evalPR : {k : Nat} -> PR k -> (Fin k -> Nat) -> Nat
  | _, .zero, _ => 0
  | _, .succ, v => v 0 + 1
  | _, .proj i, v => v i
  | _, .comp f gs, v => evalPR f (fun i => evalPR (gs i) v)
  | _, .prec f g, v =>
      Nat.rec (evalPR f (fun i => v i.succ))
        (fun y previous =>
          evalPR g (Fin.cases y (Fin.cases previous (fun i => v i.succ))))
        (v 0)

/-- One open equation checked by a concrete primitive-recursive verifier.
Arguments are packed into the free variables of the formula. -/
def checkedOpen {k : Nat} (check : PR k) : Fm PTm k :=
  PTm.app check Syn.var ≐ PTm.zero

theorem checkedOpen_qf {k : Nat} (check : PR k) : (checkedOpen check).QF :=
  True.intro

/-- Semantic checker type.  The concrete arity depends on the theorem family. -/
abbrev SemanticTest (k : Nat) := (Fin k -> Nat) -> Nat

/-- Compiler correctness for one concrete checker. -/
structure Representation {k : Nat} (semantic : SemanticTest k) where
  check : PR k
  correct : ∀ v, evalPR check v = semantic v

/-- Genuine iPRA endpoint. -/
structure InternalProof {k : Nat} (semantic : SemanticTest k)
    extends Representation semantic where
  derived : ([] : List (Fm PTm k)) ⊢[PRAAx] checkedOpen check

/-- The finite law checker decodes natural-weight laws, common-denominator
rational observables, events, and theorem-specific parameters. -/
abbrev FiniteSemanticTest := SemanticTest 4

/-- The regular checker additionally receives a precision parameter and checks
one interval inequality for a coded series/integral/simple-law presentation. -/
abbrev RegularSemanticTest := SemanticTest 5

/-- Required finite theorem derivations.  Each field must eventually be an
explicit `InternalProof` for the actual decoder/checker, not a vacuous
constant-zero function. -/
structure FiniteExpectationInternalPackage where
  expectAddTest : FiniteSemanticTest
  expectAdd : InternalProof expectAddTest
  monotoneTest : FiniteSemanticTest
  monotone : InternalProof monotoneTest
  indicatorTest : FiniteSemanticTest
  indicator : InternalProof indicatorTest
  lotusTest : FiniteSemanticTest
  lotus : InternalProof lotusTest
  tailSumTest : FiniteSemanticTest
  tailSum : InternalProof tailSumTest
  varianceTest : FiniteSemanticTest
  variance : InternalProof varianceTest
  markovTest : FiniteSemanticTest
  markov : InternalProof markovTest
  chebyshevTest : FiniteSemanticTest
  chebyshev : InternalProof chebyshevTest
  cauchySchwarzTest : FiniteSemanticTest
  cauchySchwarz : InternalProof cauchySchwarzTest
  independentProductTest : FiniteSemanticTest
  independentProduct : InternalProof independentProductTest
  totalExpectationTest : FiniteSemanticTest
  totalExpectation : InternalProof totalExpectationTest
  sampleMeanTest : FiniteSemanticTest
  sampleMean : InternalProof sampleMeanTest
  kolmogorovTest : FiniteSemanticTest
  kolmogorov : InternalProof kolmogorovTest

/-- Required effective analytic derivations. -/
structure RegularExpectationInternalPackage where
  seriesTest : RegularSemanticTest
  series : InternalProof seriesTest
  integralTest : RegularSemanticTest
  integral : InternalProof integralTest
  expectationLimitTest : RegularSemanticTest
  expectationLimit : InternalProof expectationLimitTest
  dominatedConvergenceTest : RegularSemanticTest
  dominatedConvergence : InternalProof dominatedConvergenceTest
  distributionTest : RegularSemanticTest
  distributions : InternalProof distributionTest
  fourierTest : RegularSemanticTest
  fourier : InternalProof fourierTest

/-- Existing bridge to the native scalar calculus, applied after universal
closure in the completed files. -/
theorem toNative {k : Nat} (check : PR k)
    (h : ([] : List (Fm PTm k)) ⊢[PRAAx] checkedOpen check) :
    NPrf ([] : List (NFm k)) (NFm.ofPRA (checkedOpen check)) :=
  pra_iff_native.mp h

/-!
Implementation order:

1. natural encoders and denominator-cleared evaluators;
2. defining equations;
3. bounded-sum algebra using `sum_add`, `sum_congr_bounded`, and
   `MultiSums`;
4. one explicit `Prf PRAAx` derivation per field above;
5. universal closure and `pra_iff_native` transport.
-/

end ExpectedValueIPRA.ObjectLanguage
