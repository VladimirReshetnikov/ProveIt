import FiniteHausdorff

/-!
Concrete interfaces for the aggregate chain and optimization theorems.
All ...Target declarations below are UNPROVED proposition definitions.
They neither add axioms nor claim embedded iPRA derivations. Host function
arguments are replaced by fixed PR symbols in the intended arithmetization.
-/

namespace FiniteDemand.AggregateTargets
open Aggregates

abbrev QVec := List Rat
abbrev Aggregate := Nat → List QVec
abbrev PointName := Nat → QVec
abbrev ScalarName := Nat → Rat

def absQ (x : Rat) : Rat := if x < 0 then -x else x

def dist (x y : QVec) : Rat :=
  (List.range (max x.length y.length)).foldl
    (fun r i => max r (absQ (x[i]?.getD 0 - y[i]?.getD 0))) 0

def firstMin (score : QVec → Rat) (s : List QVec) : QVec :=
  match s with
  | [] => []
  | q :: qs => qs.foldl (fun best r => if score r < score best then r else best) q

def nearest (q : QVec) (s : List QVec) : QVec := firstMin (dist q) s
def minDistance (q : QVec) (s : List QVec) : Rat := dist q (nearest q s)

def AggregateValid (d : Nat) (S : Aggregate) : Prop :=
  (∀ k, S k ≠ [] ∧ ∀ q ∈ S k, q.length = d) ∧
  (∀ s t, Within dist (dyadic s + dyadic t) (S s) (S t))

def PointValid (d : Nat) (x : PointName) : Prop :=
  (∀ k, (x k).length = d) ∧
  (∀ s t, dist (x s) (x t) ≤ dyadic s + dyadic t)

def ScalarValid (x : ScalarName) : Prop :=
  ∀ s t, absQ (x s - x t) ≤ dyadic s + dyadic t

/-- A zero name for the distance obtained by simultaneous shifted sampling. -/
def MemberZero (S : Aggregate) (x : PointName) : Prop :=
  ∀ k, minDistance (x (k + 1)) (S (k + 1)) ≤ dyadic k

def chain (S : Aggregate) (s seed : Nat) : Nat → QVec
  | 0 => (S s)[seed]?.getD []
  | n + 1 => nearest (chain S s seed n) (S (s + n + 1))

def chainName (S : Aggregate) (s seed k : Nat) : QVec :=
  chain S s seed (k + 2)

def ChainTarget : Prop :=
  ∀ d S, AggregateValid d S → ∀ s seed, seed < (S s).length →
    PointValid d (chainName S s seed) ∧ MemberZero S (chainName S s seed) ∧
    ∀ k, dist (chainName S s seed k) ((S s)[seed]?.getD []) ≤ 3 * dyadic s

def distanceName (S : Aggregate) (x : PointName) (k : Nat) : Rat :=
  minDistance (x (k + 1)) (S (k + 1))

def DistanceNameTarget : Prop :=
  ∀ d S x, AggregateValid d S → PointValid d x →
    ScalarValid (distanceName S x)

def LipschitzEvaluation (f : QVec → Nat → Rat) (L : Rat) : Prop :=
  0 ≤ L ∧ ∀ q r p t,
    absQ (f q p - f r t) ≤ L * dist q r + dyadic p + dyadic t

def rawMin (f : QVec → Nat → Rat) (S : Aggregate) (s : Nat) : Rat :=
  f (firstMin (fun q => f q s) (S s)) s

def minimumName (f : QVec → Nat → Rat) (S : Aggregate) (c k : Nat) : Rat :=
  rawMin f S (k + c)

def evalName (f : QVec → Nat → Rat) (c : Nat) (x : PointName) (k : Nat) : Rat :=
  f (x (k + c)) (k + c)

/-- Order with explicit slack for two regular scalar names. -/
def LeNamed (x y : ScalarName) (slack : Rat) : Prop :=
  ∀ k, x k ≤ y k + slack + 2 * dyadic k

def MinimumValueTarget : Prop :=
  ∀ d S f L c, AggregateValid d S → LipschitzEvaluation f L →
    L + 1 ≤ (2 ^ c : Nat) →
    ScalarValid (minimumName f S c) ∧
    ∀ x, PointValid d x → MemberZero S x →
      LeNamed (minimumName f S c) (evalName f c x) 0

/-- Index of the first rational minimum; bounded scan with default zero. -/
def minIndex (f : QVec → Rat) (s : List QVec) : Nat :=
  ((List.range s.length).foldl (fun best i =>
    if f (s[i]?.getD []) < f (s[best]?.getD []) then i else best) 0)

def approximateMinimizer (f : QVec → Nat → Rat) (S : Aggregate)
    (b k : Nat) : PointName :=
  let s := k + b
  chainName S s (minIndex (fun q => f q s) (S s))

def ApproximateMinimizerTarget : Prop :=
  ∀ d S f L c b, AggregateValid d S → LipschitzEvaluation f L →
    L + 1 ≤ (2 ^ c : Nat) → 4 * L + 2 ≤ (2 ^ b : Nat) → ∀ k,
    PointValid d (approximateMinimizer f S b k) ∧
    MemberZero S (approximateMinimizer f S b k) ∧
    LeNamed (evalName f c (approximateMinimizer f S b k))
      (minimumName f S c) (dyadic k)

-- A finite computation only, not a proof of any target above.
#eval nearest [0, 0] [[2, 0], [1, 1], [-1, 0]]

end FiniteDemand.AggregateTargets
