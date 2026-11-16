import AnalyticTargets
import FiniteContracts

/-!
# Coherent selection and empty windows: concrete UNPROVED targets

All declarations ending in `Target` below are definitions of propositions.
They are not axioms, assumptions exported as facts, or proved theorems.
Compilation checks this specification's syntax and types only.

The coherent-selection interface is written for scalar rational points in
a fixed rational interval.  The paper's finite-dimensional box version
replaces `Rat` by fixed-length rational coordinate lists, `qabs (x-y)` by
the finite maximum of coordinate distances, and scalar clipping by coordinate
clipping.  The same finite minimum and modulus schedules are unchanged.

The function arguments are host-Lean interfaces.  An object-iPRA instance
fixes their PR definitions in advance; numbers such as the requested
precision and parameter `a` remain inputs.  No evaluator for arbitrary PR
source codes and no object-level function quantifier is postulated.
Unbounded regularity, isolation, continuity and cardinality hypotheses remain
explicit assumptions.  The scanned-prefix invariants use only finite tests.
-/

namespace IPRAFramework.SelectionTargets

open AnalyticTargets

abbrev CandidateLists := Nat → List Rat
abbrev ResidualNames := Rat → RealName
abbrev ResidualSamples := Nat → Rat → Rat

def InInterval (lower upper x : Rat) : Prop := lower ≤ x ∧ x ≤ upper

def CandidateDomain (lower upper : Rat) (D : CandidateLists) : Prop :=
  lower ≤ upper ∧
    ∀ s, D s ≠ [] ∧ ∀ x, x ∈ D s → InInterval lower upper x

def ResidualValid (lower upper : Rat) (E : ResidualNames) : Prop :=
  ∀ x, InInterval lower upper x → Regular (E x) ∧ NameLower 0 (E x)

/--
The sample at search accuracy `s` has error at most 2^(-s-2) from the
represented residual.  The additional 2^(-p) is the error of the compared
name stage.  Taking `sample s x = E x (s+2)` is one concrete implementation.
-/
def SampleAccuracy (lower upper : Rat) (E : ResidualNames)
    (sample : ResidualSamples) : Prop :=
  ∀ s x, InInterval lower upper x →
    ∀ p, qabs (sample s x - E x p) ≤ dyadic (s + 2) + dyadic p

def HasApproximateWitnesses (D : CandidateLists) (E : ResidualNames) : Prop :=
  ∀ s, ∃ x, x ∈ D s ∧ NameUpper (E x) (dyadic (s + 1))

def SelectionAssumptions (lower upper : Rat) (D : CandidateLists)
    (E : ResidualNames) (sample : ResidualSamples) : Prop :=
  CandidateDomain lower upper D ∧ ResidualValid lower upper E ∧
    SampleAccuracy lower upper E sample ∧ HasApproximateWitnesses D E

/-- The default is irrelevant under the nonempty-list contract. -/
def candidate (D : CandidateLists) (s i : Nat) : Rat := (D s)[i]?.getD 0

def minimizingIndex (D : CandidateLists) (sample : ResidualSamples) (s : Nat) : Nat :=
  firstMin (fun i => sample s (candidate D s i)) ((D s).length - 1)

def approximant (D : CandidateLists) (sample : ResidualSamples) (s : Nat) : Rat :=
  candidate D s (minimizingIndex D sample s)

/-- Named goal: bounded minimization turns residual ≤ 2^(-s-1) into ≤ 2^(-s). -/
def ApproximantTarget : Prop :=
  ∀ lower upper D E sample, SelectionAssumptions lower upper D E sample →
    ∀ s, approximant D sample s ∈ D s ∧
      NameUpper (E (approximant D sample s)) (dyadic s)

/-- A supplied quantitative isolation condition, not qualitative uniqueness. -/
def Isolation (lower upper : Rat) (E : ResidualNames) (sigma : Nat → Nat) : Prop :=
  ∀ k x y, InInterval lower upper x → InInterval lower upper y →
    NameUpper (E x) (dyadic (sigma k)) →
    NameUpper (E y) (dyadic (sigma k)) →
      qabs (x - y) ≤ dyadic k

def tau (sigma : Nat → Nat) (k : Nat) : Nat := max k (sigma k)

def coherentName (D : CandidateLists) (sample : ResidualSamples)
    (sigma : Nat → Nat) (k : Nat) : Rat :=
  approximant D sample (tau sigma k)

/-- The one-sided fast-Cauchy estimate is stronger than `Regular`. -/
def CoherentSelectionTarget : Prop :=
  ∀ lower upper D E sample sigma,
    SelectionAssumptions lower upper D E sample → MonotoneModulus sigma →
    Isolation lower upper E sigma →
    let b := coherentName D sample sigma
    Regular b ∧ NameLower lower b ∧ NameUpper b upper ∧
      ∀ k l, k ≤ l → qabs (b k - b l) ≤ dyadic k

/-- Continuity is again a family of finite rational name comparisons. -/
def UniformResidual (lower upper : Rat) (E : ResidualNames) (mu : Nat → Nat) : Prop :=
  ∀ j x y, InInterval lower upper x → InInterval lower upper y →
    qabs (x - y) ≤ dyadic (mu j) →
    ∀ p, qabs (E x p - E y p) ≤ dyadic j + 2 * dyadic p

/-- Matches the paper: use an index at least j+2 and the modulus at j+2. -/
def residualEvaluationIndex (mu : Nat → Nat) (j : Nat) : Nat :=
  max (j + 2) (mu (j + 2))

/--
The residual of the represented limit is defined through its finite samples.
No pre-existing real completion is needed to define this output name.
-/
def residualAtCoherentName (D : CandidateLists) (E : ResidualNames)
    (sample : ResidualSamples) (sigma mu : Nat → Nat) (j : Nat) : Rat :=
  E (coherentName D sample sigma (residualEvaluationIndex mu j)) (j + 2)

def ResidualZeroTarget : Prop :=
  ∀ lower upper D E sample sigma mu,
    SelectionAssumptions lower upper D E sample → MonotoneModulus sigma →
    Isolation lower upper E sigma → MonotoneModulus mu →
    UniformResidual lower upper E mu →
    let r := residualAtCoherentName D E sample sigma mu
    Regular r ∧ NameEqual r (fun _ => 0)

/-! ## Bounded cardinality and a deterministic empty-window algorithm -/

abbrev HitFamily := Nat → Nat → Bool
abbrev WindowControl := Nat → Nat → Nat

/-- At most `bound` distinct successes, as an explicit negative list assertion. -/
def CardinalityBound (G : HitFamily) (a bound : Nat) : Prop :=
  ∀ xs : List Nat, xs.length = bound + 1 → xs.Nodup →
    (∀ n, n ∈ xs → G a n = true) → False

def ControlExpands (F : WindowControl) (a : Nat) : Prop :=
  ∀ n, n ≤ F a n

def cut (F : WindowControl) (a : Nat) : Nat → Nat
  | 0 => 1
  | i + 1 => F a (cut F a i) + 1

/-- Enumerates precisely [cut(i),cut(i+1)) when the control expands. -/
def windowEntries (F : WindowControl) (a i : Nat) : List Nat :=
  (List.range (cut F a (i + 1) - cut F a i)).map (fun t => cut F a i + t)

def windowHasHit (G : HitFamily) (F : WindowControl) (a i : Nat) : Bool :=
  (windowEntries F a i).any (G a)

/-- Search the B+1 windows 0,...,B, keeping an explicit failure case. -/
def findEmptyWindow (G : HitFamily) (F : WindowControl)
    (a bound : Nat) : Option Nat :=
  IPRAFramework.search (fun i => !(windowHasHit G F a i)) (bound + 1)

def WindowCutsTarget : Prop :=
  ∀ F a, ControlExpands F a →
    (∀ i, cut F a i < cut F a (i + 1)) ∧
    (∀ i j, i < j → cut F a (i + 1) ≤ cut F a j)

/--
The principal empty-window target. `B` is a numerical input, so no bound
computation is hidden. A uniform family may substitute a fixed PR term B(a).
-/
def EmptyWindowTarget : Prop :=
  ∀ G F a B, ControlExpands F a → CardinalityBound G a B →
    ∃ i, findEmptyWindow G F a B = some i ∧ i ≤ B ∧
      (∀ n, cut F a i ≤ n → n < cut F a (i + 1) → G a n = false) ∧
      (∀ n, cut F a i ≤ n → n ≤ F a (cut F a i) → G a n = false)

end IPRAFramework.SelectionTargets
