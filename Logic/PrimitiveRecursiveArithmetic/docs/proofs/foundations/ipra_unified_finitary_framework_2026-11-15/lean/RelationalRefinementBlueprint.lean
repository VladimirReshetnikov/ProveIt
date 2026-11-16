/-!
# Finite relations, viability, and shrinking refinement

STATUS: Lean blueprint, not compiled.  The first part is an ordinary finite
semantic prototype; the comments give the exact object-language migration.
The main universal theorems are left with `sorry` and are not claimed proved.
-/

set_option autoImplicit false

namespace IPRAFramework

/-- Finite layered relation. Candidates at level `k` are numbers below
`bound p k`; `good` and `compat` are intended to be primitive recursive. -/
structure LayeredRelation where
  bound  : Nat → Nat → Nat
  good   : Nat → Nat → Nat → Bool
  compat : Nat → Nat → Nat → Nat → Bool

/-- Finite existential fold. -/
def anyBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec false (fun i acc => acc || p i) n

/-- Forward viability for `d` more edges. -/
def viable (R : LayeredRelation) (p : Nat) : Nat → Nat → Nat → Bool
  | k, 0, a => decide (a < R.bound p k) && R.good p k a
  | k, d + 1, a =>
      decide (a < R.bound p k) && R.good p k a &&
        anyBelow (R.bound p (k + 1)) (fun b =>
          R.good p (k + 1) b && R.compat p k a b && viable R p (k + 1) d b)

/-- A path checker can be implemented with a bounded-list code in the object
language.  This semantic version uses a Lean list. -/
def pathOK (R : LayeredRelation) (p k : Nat) : List Nat → Bool
  | [] => false
  | a :: tail =>
      let rec loop (level prev : Nat) : List Nat → Bool
        | [] => true
        | b :: bs =>
            R.good p (level + 1) b && R.compat p level prev b &&
              loop (level + 1) b bs
      decide (a < R.bound p k) && R.good p k a && loop k a tail

/-- Main semantic target: viability is equivalent to existence of a bounded
path with the requested initial node and depth.  The production theorem must
be an embedded `Prf PRAAx` derivation for fixed PR symbols. -/
theorem viable_iff_path_target (R : LayeredRelation) (p k d a : Nat) :
    viable R p k d a = true ↔
      ∃ xs : List Nat, xs.length = d + 1 ∧ xs.head? = some a ∧
        pathOK R p k xs = true := by
  sorry

/-- Reachability from level zero; production code should use a finite table
rather than recomputing paths. -/
def reaches (R : LayeredRelation) (p target : Nat) (a : Nat) : Prop :=
  ∃ xs : List Nat, xs.length = target + 1 ∧ xs.getLast? = some a ∧
    pathOK R p 0 xs = true

/-- Full-horizon viability: the candidate occurs on a complete path from zero
to `h`. -/
def fullViable (R : LayeredRelation) (p h k a : Nat) : Prop :=
  k ≤ h ∧ ∃ xs : List Nat,
    xs.length = h + 1 ∧ pathOK R p 0 xs = true ∧ xs[k]? = some a

/-- Abstract observation data for the shrinking theorem.  Distances and
budgets are natural numbers here; a production rational module will replace
this with coded positive-denominator rationals. -/
structure ObservationData (R : LayeredRelation) where
  obs     : Nat → Nat → Nat → Nat
  dist    : Nat → Nat → Nat
  horizon : Nat → Nat → Nat
  eps     : Nat → Nat → Nat
  delta   : Nat → Nat → Nat

/-- The exact mathematical target from the report.  In the integrated module,
all hypotheses become `Prf PRAAx` fields and the conclusion is an embedded
formula. -/
theorem shrinking_viability_target
    (R : LayeredRelation) (D : ObservationData R) (p : Nat)
    (select : Nat → Nat)
    (hNonempty : ∀ k, fullViable R p (D.horizon p k) k (select k))
    (hHorizon : ∀ k l, k ≤ l → D.horizon p k ≤ D.horizon p l)
    (hDiameter : ∀ k a b,
      fullViable R p (D.horizon p k) k a →
      fullViable R p (D.horizon p k) k b →
      D.dist (D.obs p k a) (D.obs p k b) ≤ D.eps p k)
    (hEdge : ∀ k a b,
      R.compat p k a b = true →
      D.dist (D.obs p k a) (D.obs p (k + 1) b) ≤ D.delta p k)
    (hTriangle : ∀ x y z, D.dist x z ≤ D.dist x y + D.dist y z) :
    ∀ k l, k ≤ l →
      D.dist (D.obs p k (select k)) (D.obs p l (select l)) ≤
        D.eps p k + (List.range' k (l-k)).foldl (fun s j => s + D.delta p j) 0 := by
  /-
  Choose a complete path through `select l`, take its level-k ancestor,
  truncate at `horizon p k`, apply the cloud diameter hypothesis, telescope
  the edge bounds, and use the triangle inequality.
  -/
  sorry

/-!
## Object-language migration

1. Replace `Bool` functions by fixed `PR` symbols and list paths by a canonical
   bounded sequence code.
2. Prove Boolean path checking, viability recursion, and least-witness search
   with `PRA.qfInd`.
3. Define forward and backward bit tables; prove their intersection equivalent
   to the bounded path-code definition of full viability.
4. Encode rational observations, triangle inequality, cloud diameter, and edge
   budgets as equations/inequalities over the shared rational code.
5. Apply the proof-producing trace compiler to path extraction and telescoping.
6. Export the resulting ordinary derivation with `pra_iff_native`.
-/

end IPRAFramework
