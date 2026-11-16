import Mathlib
import ConciseIPRA.NativeBiInterpretation

/-!
# Object-language endpoint for the constructive CLT project

STATUS: uncompiled implementation scaffold, not a completed formalization.
It contains no `sorry` and does not postulate a CLT theorem.  A completed
project must construct an `InternalProof` value below.

Repository interface inspected at ProveIt commit
979613af639a0e33b9d17b74af2a5629bb2d749f, Lean/Mathlib v4.32.0.
-/

namespace CentralLimitIPRAPlan

open LeanProofs.ConciseIPRA
open LeanProofs.ConciseIPRA.Syn
open scoped LeanProofs.ConciseIPRA.Fm

/-- Standard interpretation of primitive-recursive syntax. -/
def evalPR : {k : ℕ} → PR k → (Fin k → ℕ) → ℕ
  | _, .zero, _ => 0
  | _, .succ, v => v 0 + 1
  | _, .proj i, v => v i
  | _, .comp f gs, v => evalPR f (fun i => evalPR (gs i) v)
  | _, .prec f g, v =>
      Nat.rec (evalPR f (fun i => v i.succ))
        (fun y previous =>
          evalPR g
            (Fin.cases y
              (Fin.cases previous (fun i => v i.succ))))
        (v 0)

/-- Arguments are: encoded finite row, encoded rational threshold, precision. -/
def checkerArgs (row q p : ℕ) : Fin 3 → ℕ :=
  Fin.cases row (Fin.cases q (fun _ => p))

/-- The concrete semantic checker is an explicit Lean function supplied by
the implementation layer.  It must decode:

* a finite list of finite rational laws;
* centering, total variance, and third moments;
* the exact rational CDF of the raw centered sum at `q`;
* regular interval names for `sqrt`, `pi`, `exp`, and `Phi`;
* the slackened inequality
    |F(q) - Phi(q/s)| ≤ 64 rho/s^3 + 2^(-p).

Invalid encodings must return zero, so the universal sentence behaves like an
implication without adding connectives to the open QF goal.  This generic file
does not replace that algorithm by a vacuous constant-zero placeholder.
-/
abbrev SemanticTest := ℕ → ℕ → ℕ → ℕ

/-- Open equation with variables 0=row, 1=q, 2=precision. -/
def berryEsseenOpen (check : PR 3) : Fm PTm 3 :=
  PTm.app check Syn.var ≐ PTm.zero

theorem berryEsseenOpen_qf (check : PR 3) : (berryEsseenOpen check).QF :=
  True.intro

/-- Closed universal sentence. -/
def berryEsseenSentence (check : PR 3) : Fm PTm 0 :=
  Fm.all (Fm.all (Fm.all (berryEsseenOpen check)))

/-- Representation is only the compiler-correctness layer for one concrete
semantic checker. -/
structure Representation (semanticTest : SemanticTest) where
  check : PR 3
  correct : ∀ row q p,
    evalPR check (checkerArgs row q p) = semanticTest row q p

/-- This is the genuine proof-theoretic endpoint.  Standard-model truth does
not construct the `derived` field. -/
structure InternalProof (semanticTest : SemanticTest)
    extends Representation semanticTest where
  derived : ([] : List (Fm PTm 3)) ⊢[PRAAx] berryEsseenOpen check

/-- Universal closure requires no new induction. -/
theorem closeProof (check : PR 3)
    (h : ([] : List (Fm PTm 3)) ⊢[PRAAx] berryEsseenOpen check) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] berryEsseenSentence check :=
  Prf.allI (Prf.allI (Prf.allI h))

/-- Existing ProveIt bridge from iPRA to the native scalar calculus. -/
theorem nativeProof (check : PR 3)
    (h : ([] : List (Fm PTm 0)) ⊢[PRAAx] berryEsseenSentence check) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (berryEsseenSentence check)) :=
  pra_iff_native.mp h

/-- Existing scalar compiler for PR syntax. -/
def scalarChecker (check : PR 3) : Tm 3 :=
  FromPRA.code check

/-!
Concrete unfinished endpoint:

    def beTest : SemanticTest := ...
    def completedCLT : InternalProof beTest := ...

The first definition must be the actual decoder/interval checker described
above; the second must be an explicit `PRAAx` derivation using only QF
induction.  The mathematical paper and `ROADMAP.md` give the induction
invariants and module order.  Neither declaration is present here.
-/

end CentralLimitIPRAPlan
