import Std

/-!
Rational envelope evaluation for atlas.tex. A nonempty finite list may be
coded as a binary tree. Minima select the atomic guard within each chart,
maxima select the chart, and transfer_guard keeps the very same chart after
two perturbations. The code is independent of the algorithm for computing
the global margin and of any modulus / point representation.
-/
namespace IPRAReport.AtlasCase

inductive Tree (α : Type u) where
  | leaf (x : α)
  | branch (a b : Tree α)

def treeMin (v : α → Rat) : Tree α → Rat
  | .leaf x => v x
  | .branch a b => min (treeMin v a) (treeMin v b)

def treeMax (v : α → Rat) : Tree α → Rat
  | .leaf x => v x
  | .branch a b => max (treeMax v a) (treeMax v b)

/-- Tie convention agrees with Rat.max_def. -/
def select (v : α → Rat) : Tree α → α
  | .leaf x => x
  | .branch a b =>
    if treeMax v a ≤ treeMax v b then select v b else select v a

theorem select_score (v : α → Rat) (s : Tree α) : v (select v s) = treeMax v s := by
  induction s with
  | leaf _ => rfl
  | branch a b ha hb =>
    change v (if treeMax v a ≤ treeMax v b then select v b else select v a) =
      max (treeMax v a) (treeMax v b)
    rw [Rat.max_def]
    by_cases h : treeMax v a ≤ treeMax v b
    · rw [if_pos h, if_pos h]
      exact hb
    · rw [if_neg h, if_neg h]
      exact ha

theorem min_transfer (u v : α → Rat) (e : Rat)
    (bound : ∀ x, u x ≤ v x + e) (s : Tree α) :
    treeMin u s ≤ treeMin v s + e := by
  induction s with
  | leaf x => exact bound x
  | branch a b ha hb =>
    change min _ _ ≤ min _ _ + e
    rw [Rat.min_def, Rat.min_def]
    split <;> split <;> grind

/-- Even before choosing a chart, the supremum of their slacks obeys
the same one-sided perturbation bound. Swap u and v for the other side. -/
theorem envelope_transfer (u v : α → Rat) (e : Rat)
    (bound : ∀ x, u x ≤ v x + e) (charts : Tree (Tree α)) :
    treeMax (treeMin u) charts ≤ treeMax (treeMin v) charts + e := by
  induction charts with
  | leaf c => exact min_transfer u v e bound c
  | branch a b ha hb =>
    change max _ _ ≤ max _ _ + e
    rw [Rat.max_def, Rat.max_def]
    split <;> split <;> grind

/-- If q approximates x and y is near x, a maximizer at q still has
slack at least mu / 2 at y, assuming at most e loss per observation.
For an L-Lipschitz atlas take e = L * delta. -/
theorem transfer_guard (charts : Tree (Tree α)) (q x y : α → Rat) (e mu : Rat)
    (hq : ∀ i, q i ≤ x i + e) (hy : ∀ i, x i ≤ y i + e)
    (margin : mu ≤ treeMax (treeMin q) charts) (budget : 4 * e ≤ mu) :
    mu / 2 ≤ treeMin y (select (treeMin q) charts) := by
  let c := select (treeMin q) charts
  have h0 : treeMin q c = treeMax (treeMin q) charts := select_score _ _
  have h1 := min_transfer q x e hq c
  have h2 := min_transfer x y e hy c
  change mu / 2 ≤ treeMin y c
  grind

end IPRAReport.AtlasCase

#print axioms IPRAReport.AtlasCase.transfer_guard
