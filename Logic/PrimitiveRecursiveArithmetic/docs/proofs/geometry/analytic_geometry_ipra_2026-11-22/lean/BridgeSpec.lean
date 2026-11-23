import IPRADerivations.Core.Order
import IPRADerivations.Core.Tactic

/-!
# Explicit bridge interfaces and remaining obligations

STATUS: uncompiled specification. The structures below have NO supplied
instances. Their fields are proof obligations, not axioms or proved results.
The object-language constructors and names were read at the pinned repository
commit. All function symbols are fixed PR syntax; there is no universal PR
evaluator and no internal quantification over arbitrary real functions.
-/

namespace LeanProofs.IPRA.Geometry.AnalyticGeometryBridge

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app)

structure RatTerm (n : ℕ) where
  numerator : ZT n
  denominator : PTm n

namespace RatTerm

variable {n : ℕ}

def valid (x : RatTerm n) : Fm PTm n :=
  le (ConciseIPRA.PTm.succ ConciseIPRA.PTm.zero) x.denominator
def equal (x y : RatTerm n) : Fm PTm n :=
  (x.numerator*ZT.ofNat y.denominator).eq (y.numerator*ZT.ofNat x.denominator)

def add (x y : RatTerm n) : RatTerm n :=
  ⟨x.numerator*ZT.ofNat y.denominator+y.numerator*ZT.ofNat x.denominator,
   x.denominator*y.denominator⟩

def mul (x y : RatTerm n) : RatTerm n :=
  ⟨x.numerator*y.numerator, x.denominator*y.denominator⟩

def negated (x : RatTerm n) : RatTerm n := ⟨-x.numerator, x.denominator⟩
def sub (x y : RatTerm n) : RatTerm n := add x (negated y)

end RatTerm

/-- A particular family with m number parameters and one precision input.
This is a metatheoretic bundle of three *specified* PR programs. -/
structure FixedFamily (m : ℕ) where
  numeratorPos : PR (m+1)
  numeratorNeg : PR (m+1)
  denominator : PR (m+1)

def FixedFamily.at {m n : ℕ} (f : FixedFamily m)
    (parameters : Fin m → PTm n) (precision : PTm n) : RatTerm n :=
  let inputs := Fin.cases precision parameters
  ⟨⟨app f.numeratorPos inputs, app f.numeratorNeg inputs⟩,
   app f.denominator inputs⟩

/-- A complete rational bridge must supply these derivations. This structure
does not claim that the obligations have been discharged in this packet. -/
structure RationalBridgeObligations where
  add_valid : ∀ {n} {Γ : List (Fm PTm n)} (x y : RatTerm n),
    (Γ ⊢[PRAAx] x.valid) → (Γ ⊢[PRAAx] y.valid) →
    (Γ ⊢[PRAAx] (x.add y).valid)
  mul_valid : ∀ {n} {Γ : List (Fm PTm n)} (x y : RatTerm n),
    (Γ ⊢[PRAAx] x.valid) → (Γ ⊢[PRAAx] y.valid) →
    (Γ ⊢[PRAAx] (x.mul y).valid)
  add_congr : ∀ {n} {Γ : List (Fm PTm n)} (x x' y y' : RatTerm n),
    (Γ ⊢[PRAAx] x.equal x') → (Γ ⊢[PRAAx] y.equal y') →
    (Γ ⊢[PRAAx] (x.add y).equal (x'.add y'))
  mul_congr : ∀ {n} {Γ : List (Fm PTm n)} (x x' y y' : RatTerm n),
    (Γ ⊢[PRAAx] x.equal x') → (Γ ⊢[PRAAx] y.equal y') →
    (Γ ⊢[PRAAx] (x.mul y).equal (x'.mul y'))

/-- Each analytic proof is completed by concrete formulas, a fixed PR output
program, and a derivation of the finite-observation implication. There is no
instance in this delivery and no soundness/reflection axiom. -/
structure FiniteObservationTarget (m : ℕ) where
  output : FixedFamily m
  hypotheses : Fm PTm (m+1)
  conclusion : Fm PTm (m+1)
  hypothesesQF : hypotheses.QF
  conclusionQF : conclusion.QF
  proof : ([] : List (Fm PTm (m+1))) ⊢[PRAAx] (hypotheses ⟶ conclusion)

end LeanProofs.IPRA.Geometry.AnalyticGeometryBridge
