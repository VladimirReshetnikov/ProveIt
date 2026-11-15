import Mathlib
import ConciseIPRA.NativeBiInterpretation

/-!
# Transcendence in iPRA: interfaces for a future formalization

STATUS: UNCOMPILED BLUEPRINT, not a completed formal proof.

This file records executable finite definitions and the *type* of the missing
object-theory derivations. No instance of `Programs` or `Derivations` is
constructed. There is no claim here to have proved either transcendence
theorem in Lean. The conditional transport at the end uses the actual
ConciseIPRA API inspected at ProveIt commit
0bf379a84212abd05e9a3f0b1320a3d7da509cf9.

Place this in the Lean project containing the `ConciseIPRA` import root.
The companion ROADMAP.md lists all missing programs and proof obligations.
-/

namespace TranscendenceIPRA

open LeanProofs.ConciseIPRA
open scoped BigOperators

/-! ## Finite rational objects, used for testing the intended specification -/

def dyadic (s : ℕ) : ℚ := 1 / (2 : ℚ) ^ s

def expLength (R s : ℕ) : ℕ := 4 * (R + 1) ^ 2 + s + 4

/-- Final precision from an integer reciprocal margin and Lipschitz bound. -/
def separationPrecision (B lip : ℕ) : ℕ := 4 * B * lip + 1

def eApprox (s : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (s + 2), (Nat.factorial j : ℚ)⁻¹

def atanApprox (b s : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (s + 1),
    (-1 : ℚ) ^ j / (((2 * j + 1 : ℕ) : ℚ) * (b : ℚ) ^ (2 * j + 1))

def piApprox (s : ℕ) : ℚ :=
  16 * atanApprox 5 s - 4 * atanApprox 239 s

/-- Coefficients are listed in increasing order of degree. -/
def polyEval : List ℤ → ℚ → ℚ
  | [], _ => 0
  | a :: as, x => (a : ℚ) + x * polyEval as x

/-- A safe Lipschitz bound on [-4,4], with one unit of slack. -/
def polyLip (a : List ℤ) : ℚ :=
  1 + ∑ j ∈ Finset.range a.length,
    (j : ℚ) * |(a.getD j 0 : ℚ)| * (4 : ℚ) ^ (j - 1)

def AllZero (a : List ℤ) : Prop := ∀ z ∈ a, z = 0

/-- A finite, decidable rational separation certificate. -/
def ApartAt (name : ℕ → ℚ) (a : List ℤ) (s : ℕ) : Prop :=
  polyLip a * dyadic s < |polyEval a (name s)|

def expCut {d : ℕ} (B : Matrix (Fin d) (Fin d) ℚ) (L : ℕ) :
    Matrix (Fin d) (Fin d) ℚ :=
  ∑ j ∈ Finset.range (L + 1), (Nat.factorial j : ℚ)⁻¹ • B ^ j

/-!
The definitions above use Mathlib data structures for readability. Their
object-theory versions must be list/matrix codes built from `PR.zero`,
`PR.succ`, `PR.proj`, `PR.comp`, and `PR.prec`. Merely evaluating these Lean
definitions does not produce the corresponding internal iPRA derivations.
-/

/-! ## The semantics of the actual primitive-recursive syntax -/

/-!
`evalPR` is an OUTSIDE-THE-THEORY Lean semantics function. A universal
evaluator on arbitrary PR syntax is not itself primitive recursive. It must
never be introduced as an iPRA function symbol. Only the fixed programs
`eTest`, `piTest`, `eIndex`, and `piIndex` are object-language symbols.
-/

def evalPR : {k : ℕ} → PR k → (Fin k → ℕ) → ℕ
  | _, .zero, _ => 0
  | _, .succ, xs => Nat.succ (xs 0)
  | _, .proj i, xs => xs i
  | _, .comp f gs, xs => evalPR f (fun i => evalPR (gs i) xs)
  | _, .prec f g, xs =>
      Nat.rec (evalPR f (fun i => xs i.succ))
        (fun y z =>
          evalPR g (Fin.cases y (Fin.cases z (fun i => xs i.succ))))
        (xs 0)

def unaryEval (f : PR 1) (n : ℕ) : ℕ := evalPR f (fun _ => n)

/-- `test(p) = 1`, as an object-language formula with one free variable. -/
def Accepted (test : PR 1) : Fm PTm 1 :=
  Fm.eq (PTm.app test (fun _ => PTm.var 0)) (PTm.succ PTm.zero)

/-- The exact shape of each desired *closed iPRA statement*. -/
def AllAccepted (test : PR 1) : Fm PTm 0 := Fm.all (Accepted test)

/-!
`Programs` is a specification, not a supplied instance. The indices must be
the explicit bounds from the paper. The tests return 1 exactly when the
input is the zero polynomial or that computed index supplies a rational
separation certificate. The codec also needs PR implementations; only its
external, human-readable interface is shown here.
-/

structure Programs where
  encodePolynomial : List ℤ → ℕ
  decodePolynomial : ℕ → List ℤ
  decode_encode : ∀ a, decodePolynomial (encodePolynomial a) = a
  eIndex : PR 1
  piIndex : PR 1
  eTest : PR 1
  piTest : PR 1
  eSpecification : ∀ p,
    unaryEval eTest p = 1 ↔
      AllZero (decodePolynomial p) ∨
        ApartAt eApprox (decodePolynomial p) (unaryEval eIndex p)
  piSpecification : ∀ p,
    unaryEval piTest p = 1 ↔
      AllZero (decodePolynomial p) ∨
        ApartAt piApprox (decodePolynomial p) (unaryEval piIndex p)

/-!
Constructing this record is the remaining formal theorem, not an assumption
made by the human proof. Each component must be assembled from `Prf`
constructors, PR defining equations, and `PRA.qfInd`. A theorem in ambient
Lean about all natural numbers is not a substitute for these fields.
-/

structure Derivations (p : Programs) : Prop where
  e : Prf PRAAx ([] : List (Fm PTm 0)) (AllAccepted p.eTest)
  pi : Prf PRAAx ([] : List (Fm PTm 0)) (AllAccepted p.piTest)

/-! ## Conditional transport through the already existing repository theorem -/

theorem nativeE (p : Programs) (h : Derivations p) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (AllAccepted p.eTest)) := by
  simpa using (pra_iff_native.mp h.e)

theorem nativePi (p : Programs) (h : Derivations p) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (AllAccepted p.piTest)) := by
  simpa using (pra_iff_native.mp h.pi)

end TranscendenceIPRA
