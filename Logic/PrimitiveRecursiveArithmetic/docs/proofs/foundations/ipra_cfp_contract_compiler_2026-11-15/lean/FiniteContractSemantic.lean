import Std

/-!
# Semantic prototype for certified finitary presentations

This file records ordinary Lean definitions for the finite algorithms in the
report.  It is not an object-language iPRA proof.  It is intentionally kept
separate from `ObjectCompilerBlueprint.lean`.

Formalization status in this delivered archive: UNCOMPILED.  Lean 4.32.0 was
not available in the artifact-building runtime.  The statements below are
dependency-ordered targets; placeholders are explicit.
-/

set_option autoImplicit false

namespace CFP

def allBelow (p : Nat → Bool) : Nat → Bool
  | 0 => true
  | n + 1 => allBelow p n && p n

def anyBelow (p : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => anyBelow p n || p n

def firstTrue (p : Nat → Bool) (bound : Nat) : Nat :=
  (List.range bound).foldl
    (fun w i => if w == bound && p i then i else w) bound

theorem firstTrue_le (p : Nat → Bool) (bound : Nat) :
    firstTrue p bound ≤ bound := by
  -- Fold invariant: the accumulator is either the sentinel `bound`
  -- or an index strictly below `bound`.
  sorry

theorem firstTrue_valid
    (p : Nat → Bool) (bound : Nat)
    (h : firstTrue p bound < bound) :
    p (firstTrue p bound) = true := by
  -- Induct over `List.range bound`, preserving validity once a witness
  -- replaces the sentinel.
  sorry

structure EdgeDemand where
  parent : Nat
  demand : Nat → Nat

/-- One reverse update for a child request. -/
def propagateChild
    (childRequest : Nat)
    (edges : List EdgeDemand)
    (requests : Array Nat) : Array Nat :=
  edges.foldl
    (fun req e =>
      if h : e.parent < req.size then
        req.set ⟨e.parent, h⟩
          (max req[e.parent] (e.demand childRequest))
      else req)
    requests

/-- Reverse demand propagation with explicit fuel/order.  The graph descriptor
is assumed topologically ordered: every parent index is smaller than its
child index. -/
def reverseDemands
    (parents : Array (List EdgeDemand))
    (external : Array Nat) : Array Nat :=
  (List.range parents.size).reverse.foldl
    (fun req child =>
      if h₁ : child < parents.size then
        if h₂ : child < req.size then
          propagateChild req[child] parents[child] req
        else req
      else req)
    external

def EdgeAdequate
    (parents : Array (List EdgeDemand))
    (requests : Array Nat) : Prop :=
  ∀ child (hc : child < parents.size) (e : EdgeDemand),
    e ∈ parents[child] →
    e.parent < requests.size →
    requests[e.parent] ≥ e.demand requests[child]

theorem reverseDemands_adequate
    (parents : Array (List EdgeDemand))
    (external : Array Nat)
    (hsize : parents.size = external.size)
    (htopo : ∀ child (hc : child < parents.size) e,
      e ∈ parents[child] → e.parent < child) :
    EdgeAdequate parents (reverseDemands parents external) := by
  -- Reverse induction over the child list.  Each update is a `max`, so
  -- previously established lower bounds are preserved.
  sorry

/-- Fuelled finite viability.  `cand k c` means candidate `c` is present at
level `k`; `compat k c d` is the refinement relation. -/
def viable
    (cand : Nat → Nat → Bool)
    (compat : Nat → Nat → Nat → Bool)
    (bound : Nat → Nat)
    (target : Nat) : Nat → Nat → Bool
  | 0, c => cand target c
  | fuel + 1, c =>
      let k := target - (fuel + 1)
      cand k c &&
        anyBelow
          (fun d => compat k c d && viable cand compat bound target fuel d)
          (bound (k + 1))

/-- The semantic path constructor uses backward viability tables and bounded
first-witness search.  The report gives the precise invariant. -/
def coherentPath
    (cand : Nat → Nat → Bool)
    (compat : Nat → Nat → Nat → Bool)
    (bound : Nat → Nat)
    (target : Nat) : Option (List Nat) :=
  -- Implementation target: first build the viability table backward,
  -- then choose the least viable root and least viable successors.
  none

theorem coherentPath_sound
    (cand : Nat → Nat → Bool)
    (compat : Nat → Nat → Nat → Bool)
    (bound : Nat → Nat)
    (target : Nat)
    (path : List Nat)
    (h : coherentPath cand compat bound target = some path) :
    path.length = target + 1 ∧
    ∀ k, k < target →
      cand k path[k]! = true ∧
      compat k path[k]! path[k+1]! = true := by
  sorry

def boundedEnumerate (p : Nat → Bool) (bound : Nat) : List Nat :=
  (List.range (bound + 1)).filter (fun n => p n)

theorem boundedEnumerate_sound
    (p : Nat → Bool) (bound x : Nat)
    (h : x ∈ boundedEnumerate p bound) :
    x ≤ bound ∧ p x = true := by
  sorry

theorem boundedEnumerate_complete
    (p : Nat → Bool) (bound x : Nat)
    (hx : x ≤ bound) (hp : p x = true) :
    x ∈ boundedEnumerate p bound := by
  sorry

/-- A finite trace system at the semantic level. -/
structure TraceSystem where
  State : Type
  init : Nat → State
  step : Nat → State → Nat → State
  inv : Nat → State → Nat → Prop
  finish : State → Nat → Prop

def run (S : TraceSystem) (param : Nat) : Nat → S.State
  | 0 => S.init param
  | t + 1 => S.step t (run S param t) param

theorem finiteTraceReflection
    (S : TraceSystem)
    (param horizon : Nat)
    (hbase : S.inv 0 (S.run param 0) param)
    (hstep : ∀ t, t < horizon →
      S.inv t (S.run param t) param →
      S.inv (t + 1) (S.run param (t + 1)) param)
    (hfinish : S.inv horizon (S.run param horizon) param →
      S.finish (S.run param horizon) param) :
    S.finish (S.run param horizon) param := by
  apply hfinish
  induction horizon with
  | zero => simpa using hbase
  | succ n ih =>
      exact hstep n (Nat.lt_succ_self n) ih

end CFP
