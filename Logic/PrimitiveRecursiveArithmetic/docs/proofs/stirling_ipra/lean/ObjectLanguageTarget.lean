import Mathlib
import ConciseIPRA.NativeBiInterpretation

/-!
# Object-language endpoint for the Stirling project

STATUS: uncompiled implementation scaffold, not a completed Stirling
formalization.  The repository APIs below were read at ProveIt commit
329161f8da0b319d51ba9f6246c4b19d243f7193, Lean / Mathlib v4.32.0.
No Lean executable was available in the authoring environment.

This file contains:
* an explicit mathematical specification for the rational finite theorem;
* the exact shape of its object-language iPRA sentence;
* a wrapper transferring an already constructed iPRA derivation to the native
  ConciseIPRA calculus.

It deliberately does NOT assert a Stirling derivation.  Building its PR
checker code and the proof of that code's universally vanishing value are
the outstanding formalization work.  The structures below record those
obligations rather than postulating them as axioms.
-/

namespace StirlingIPRAPlan

open LeanProofs.ConciseIPRA
open LeanProofs.ConciseIPRA.Syn
open scoped LeanProofs.ConciseIPRA.Fm

/-- Finite rational summation.  Every use below supplies a fixed
primitive-recursive summand; no higher-order objects enter iPRA. -/
def ratSum (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | m + 1 => ratSum f m + f m

/-- Bounded scan for the least b with n < 2^b.  The initial answer n+1
is a valid bound; the full scan examines b = 0,...,n+1. -/
def bitLengthScan (n : ℕ) : ℕ → ℕ
  | 0 => n + 1
  | m + 1 =>
      let old := bitLengthScan n m
      if n < 2 ^ m then min old m else old

def bitLength (n : ℕ) : ℕ :=
  bitLengthScan n (n + 2)

/-- Largest exponent i < bound with 2^i*b <= a, with default zero. -/
def exponentScan (a b : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 =>
      if 2 ^ m * b ≤ a then m else exponentScan a b m

/-- Finite atanh-type logarithm sum. -/
def logSeries (z : ℚ) (K : ℕ) : ℚ :=
  2 * ratSum (fun j => z ^ (2 * j + 1) / (2 * (j : ℚ) + 1)) K

/-- Range-reduced log approximation on q >= 1.  The numerator bound
is deliberately simple, not optimized for computational cost. -/
def logCore (q : ℚ) (r : ℕ) : ℚ :=
  let a := q.num.natAbs
  let b := q.den
  let k := exponentScan a b (a + 1)
  let y := q / (2 : ℚ) ^ k
  let K := r + k + 4
  (k : ℚ) * logSeries (1 / 3) K +
    logSeries ((y - 1) / (y + 1)) K

/-- Total rational logarithm approximant; the invalid nonpositive branch
is assigned zero and is never used in the theorem's valid computations. -/
def logApprox (q : ℚ) (r : ℕ) : ℚ :=
  if q ≤ 0 then 0
  else if 1 ≤ q then logCore q r
  else -logCore (1 / q) r

/-- pi = 4(atan(1/2)+atan(1/3)); all displayed sums are finite. -/
def piApprox (r : ℕ) : ℚ :=
  4 * ratSum
    (fun j => (-1 : ℚ) ^ j *
      (((1 / 2 : ℚ) ^ (2 * j + 1) +
        (1 / 3 : ℚ) ^ (2 * j + 1)) / (2 * (j : ℚ) + 1)))
    (r + 4)

/-- The manuscript's explicit approximation to the logarithmic
Stirling remainder, with the explicit convention Q(0,p)=0. -/
def stirlingApprox (n p : ℕ) : ℚ :=
  if n = 0 then 0 else
    let r := p + bitLength n + 4
    ratSum (fun j => logApprox ((j + 1 : ℕ) : ℚ) r) n -
      ((n : ℚ) + 1 / 2) * logApprox (n : ℚ) r +
      (n : ℚ) - (1 / 2 : ℚ) * logApprox (2 * piApprox r) r


/-- A mathematical (not yet object-language) specification for the output
of the rational approximation algorithm in the accompanying manuscript. -/
def finiteBounds (q : ℕ → ℕ → ℚ) (n p : ℕ) : Prop :=
  n = 0 ∨
    (1 / (12 * (n : ℚ) + 1) - 1 / (2 : ℚ) ^ p ≤ q n p ∧
      q n p ≤ 1 / (12 * (n : ℚ)) + 1 / (2 : ℚ) ^ p)

/-- The exact, decidable rational test, zero on success.  To use this in
iPRA, replace q by the specific PR rational algorithm and construct
corresponding PR syntax.  An arbitrary Lean function q is NOT assumed PR. -/
def boundsCheck (q : ℕ → ℕ → ℚ) (n p : ℕ) : ℕ :=
  letI : Decidable (finiteBounds q n p) := by
    unfold finiteBounds
    infer_instance
  if finiteBounds q n p then 0 else 1

/-- The concrete finite mathematical checker to be compiled into PR syntax. -/
def stirlingFiniteTest (n p : ℕ) : ℕ :=
  boundsCheck stirlingApprox n p

/-- Standard interpretation of PR syntax.  This is a metatheoretic map.
It must never be used as a reflection principle from true arithmetic
statements to iPRA derivations. -/
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

/-- Arguments of the two-variable checker, in its declared order n,p. -/
def checkerArgs (n p : ℕ) : Fin 2 → ℕ :=
  Fin.cases n (fun _ => p)

/-- The open formula check(n,p)=0, with free variables 0=n and 1=p.
This is literally an equation and therefore qualifies for QF induction. -/
def stirlingOpen (check : PR 2) : Fm PTm 2 :=
  PTm.app check Syn.var ≐ PTm.zero

theorem stirlingOpen_qf (check : PR 2) : (stirlingOpen check).QF :=
  True.intro

/-- The closed sentence is forall p, forall n, check(n,p)=0.
The order follows de Bruijn binding: the innermost bound variable is 0. -/
def stirlingSentence (check : PR 2) : Fm PTm 0 :=
  Fm.all (Fm.all (stirlingOpen check))

/-- Constructing concrete PR syntax and relating it to the rational program
is the representation layer.  This structure by itself does NOT supply an
object-level proof of Stirling. -/
structure Representation (q : ℕ → ℕ → ℚ) where
  check : PR 2
  correct : ∀ n p, evalPR check (checkerArgs n p) = boundsCheck q n p

/-- The genuinely relevant arithmetic endpoint.  A finished project must
CONSTRUCT this record, with a proof using PRAAx and its QF-induction rule.
A semantic proof finiteBounds(q,n,p) alone does not fill derived. -/
structure InternalProof (q : ℕ → ℕ → ℚ) extends Representation q where
  derived : ([] : List (Fm PTm 2)) ⊢[PRAAx] stirlingOpen check

/-- Universal generalization needs no additional induction. -/
theorem closeProof (check : PR 2)
    (h : ([] : List (Fm PTm 2)) ⊢[PRAAx] stirlingOpen check) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] stirlingSentence check :=
  Prf.allI (Prf.allI h)

/-- Once the iPRA proof is present, the already established repository
bridge gives the native ConciseIPRA proof. -/
theorem nativeProof (check : PR 2)
    (h : ([] : List (Fm PTm 0)) ⊢[PRAAx] stirlingSentence check) :
    NPrf ([] : List (NFm 0)) (NFm.ofPRA (stirlingSentence check)) :=
  pra_iff_native.mp h

/-- The scalar compiler for the checker is already available.  This compiles
PR SYNTAX, not arbitrary Lean programs, to iterator terms. -/
def scalarChecker (check : PR 2) : Tm 2 :=
  FromPRA.code check

/-!
Implementation order (see the detailed manuscript for the finite identities):

1. Encode signed integers and positive-denominator rational pairs with Nat
   pairs; define total addition, multiplication, comparison, and division
   with a specified zero-denominator default.  Prove validity at every call.
2. Build concrete PR syntax for bounded sums/products, powers, factorial,
   the logarithm approximant, pi approximant, precision schedule, and q(n,p).
   Prove their defining equations inside PRAAx.
3. Compile finite conjunctions/bounded searches to Boolean recursors.
   In every induction lemma, fix all precision/length parameters first and
   use only a QF invariant in the object language.
4. Prove the finite logarithm telescoping and Wallis inequalities in that
   language, with all approximation errors retained.
5. Construct Representation q, then the substantially stronger
   InternalProof q.  Do not infer the latter by standard-model soundness.
6. Apply closeProof and nativeProof.
7. Put the optional ordinary-real interpretation in a SEPARATE module.
   It identifies the rationally represented constants with Real.pi and
   Real.exp; it is not a dependency of the internal theorem.

Suggested audit commands after completing the project:
  lake env lean StirlingIPRA/ObjectLanguageTarget.lean
  #print axioms completedInternalTheorem
  #print axioms completedNativeTheorem

No completedInternalTheorem declaration is present here.
The concrete unfinished endpoint is to construct a value of
  InternalProof stirlingApprox.
-/

end StirlingIPRAPlan

