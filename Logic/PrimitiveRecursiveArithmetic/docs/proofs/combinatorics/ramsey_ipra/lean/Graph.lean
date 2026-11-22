import Std

/-!
A constructive two-colour graph Ramsey algorithm. `pascal a b` bounds the
number of vertices needed for a false clique of size `a+1` or a true clique
of size `b+1`. The edge function is read only forward in the input order.
Starting with a duplicate-free vertex list therefore represents an ordinary
undirected graph, with no symmetry hypothesis on the unused reverse entries.
-/

namespace Ramsey.Graph

private def nextRow (previous : Nat → Nat) : Nat → Nat
  | 0 => 1
  | b+1 => previous (b+1) + nextRow previous b

def pascal : Nat → Nat → Nat
  | 0 => fun _ => 1
  | a+1 => nextRow (pascal a)

theorem pascal_step (a b : Nat) :
    pascal (a+1) (b+1) = pascal a (b+1) + pascal (a+1) b := rfl

theorem pascal_positive (a b : Nat) : 0 < pascal a b := by
  induction a generalizing b with
  | zero => exact Nat.zero_lt_succ _
  | succ a ih =>
    cases b with
    | zero => exact Nat.zero_lt_succ _
    | succ b => rw [pascal_step]; have := ih (b+1); omega

structure Clique {α : Type} (c : α → α → Bool) (xs : List α)
    (color : Bool) (size : Nat) where
  vertices : List α
  inside : vertices.Sublist xs
  size_eq : vertices.length = size
  mono : vertices.Pairwise (fun u v => c u v = color)

private def singleton {α : Type} (c : α → α → Bool) (xs : List α)
    (color : Bool) (enough : 1 ≤ xs.length) : Clique c xs color 1 := by
  cases xs with
  | nil => simp at enough
  | cons x xs => exact ⟨[x], .cons₂ x (List.nil_sublist xs), rfl, by simp⟩

private def skipPivot {α : Type} {c : α → α → Bool} {xs : List α}
    {p : α → Bool} {color : Bool} {n : Nat} (x : α)
    (h : Clique c (xs.filter p) color n) : Clique c (x :: xs) color n :=
  ⟨h.vertices, .cons x (h.inside.trans List.filter_sublist), h.size_eq, h.mono⟩

private def addPivot {α : Type} {c : α → α → Bool} {xs : List α}
    {color : Bool} {n : Nat} (x : α)
    (h : Clique c (xs.filter (fun y => c x y == color)) color n) :
    Clique c (x :: xs) color (n+1) :=
  ⟨x :: h.vertices, .cons₂ x (h.inside.trans List.filter_sublist),
    by simp [h.size_eq], .cons (fun _ hy => by
      simpa using (List.mem_filter.mp (h.inside.subset hy)).2) h.mono⟩

private theorem split_length {α : Type} (p : α → Bool) (xs : List α) :
    (xs.filter (fun y => p y == false)).length +
      (xs.filter (fun y => p y == true)).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hx : p x <;> simp_all [List.filter] <;> omega

/-- Extract a clique and its sublist and homogeneity certificates. -/
def extract {α : Type} (c : α → α → Bool) :
    ∀ a b (xs : List α), pascal a b ≤ xs.length →
      Clique c xs false (a+1) ⊕ Clique c xs true (b+1) := by
  intro a
  induction a with
  | zero => intro b xs enough; exact .inl (singleton c xs false enough)
  | succ a outer =>
    intro b
    induction b with
    | zero => intro xs enough; exact .inr (singleton c xs true enough)
    | succ b inner =>
      intro vs enough
      cases vs with
      | nil => have := pascal_positive (a+1) (b+1); simp at enough; omega
      | cons x xs =>
        change pascal a (b+1) + pascal (a+1) b ≤ xs.length + 1 at enough
        let red := xs.filter (fun y => c x y == false)
        let blue := xs.filter (fun y => c x y == true)
        if hr : pascal a (b+1) ≤ red.length then
          match outer (b+1) red hr with
          | .inl h => exact .inl (addPivot x h)
          | .inr h => exact .inr (skipPivot x h)
        else
          have partition : red.length + blue.length = xs.length := split_length (c x) xs
          have hb : pascal (a+1) b ≤ blue.length := by omega
          match inner blue hb with
          | .inl h => exact .inl (skipPivot x h)
          | .inr h => exact .inr (addPivot x h)

/-- Every colouring of the unordered pairs on six vertices yields an actual triangle. -/
def triangleOnSix (c : Fin 6 → Fin 6 → Bool) :
    Clique c (List.finRange 6) false 3 ⊕ Clique c (List.finRange 6) true 3 :=
  extract c 2 2 (List.finRange 6) (by decide)

/-- Sides versus diagonals of a pentagon give the sharp lower bound. -/
def pentagon (x y : Fin 5) : Bool :=
  decide ((x.val + 1) % 5 = y.val ∨ (y.val + 1) % 5 = x.val)

private theorem pentagon_check : ∀ x y z : Fin 5, x < y → y < z →
    ¬ (pentagon x y = pentagon x z ∧ pentagon x z = pentagon y z) := by decide

theorem pentagon_obstruction (color : Bool) (h : Clique pentagon (List.finRange 5) color 3) : False := by
  have sorted : h.vertices.Pairwise (· < ·) :=
    (by decide : (List.finRange 5).Pairwise (· < ·)).sublist h.inside
  have size := h.size_eq
  have mono := h.mono
  generalize h.vertices = vs at sorted size mono
  cases vs with
  | nil => simp_all
  | cons x xs =>
    cases xs with
    | nil => simp_all
    | cons y ys =>
      cases ys with
      | nil => simp_all
      | cons z zs =>
        simp only [List.pairwise_cons, List.mem_cons, List.length_cons] at sorted mono size
        have xy := sorted.1 y (.inl rfl)
        have yz := sorted.2.1 z (.inl rfl)
        have cxy := mono.1 y (.inl rfl)
        have cxz := mono.1 z (.inr (.inl rfl))
        have cyz := mono.2.1 z (.inl rfl)
        exact pentagon_check x y z xy yz ⟨cxy.trans cxz.symm, cxz.trans cyz.symm⟩

end Ramsey.Graph
