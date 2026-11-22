import Std

/-!
Finite kernels for the constructive hairy ball argument. Lean 4.19.0, Std only.
The octahedron calculations use kernel evaluation (`decide`). The degree
comparison consumes explicit finite local and boundary certificates.
-/
namespace ConstructiveHairyBall

/-- Search the natural indices strictly below the bound, from largest to smallest. -/
def scan (good : Nat → Bool) : Nat → Option Nat
  | 0 => none
  | n + 1 => if good n then some n else scan good n

theorem scan_none_iff (good : Nat → Bool) (b : Nat) :
    scan good b = none ↔ ∀ i, i < b → good i = false := by
  induction b with
  | zero => simp [scan]
  | succ b ih =>
    cases hg : good b with
    | false =>
      simp only [scan, hg, Bool.false_eq_true, ↓reduceIte, ih]
      constructor
      · intro h i hi
        by_cases hib : i = b
        · simpa [hib] using hg
        · exact h i (by omega)
      · intro h i hi
        exact h i (by omega)
    | true =>
      simp only [scan, hg, ↓reduceIte, reduceCtorEq, false_iff]
      intro h
      have hn := h b (Nat.lt_succ_self b)
      simp [hg] at hn

theorem scan_sound {good : Nat → Bool} {b i : Nat}
    (h : scan good b = some i) : i < b ∧ good i = true := by
  induction b with
  | zero => simp [scan] at h
  | succ b ih =>
    cases hg : good b with
    | false =>
      simp [scan, hg] at h
      obtain ⟨hi, hgood⟩ := ih h
      exact ⟨by omega, hgood⟩
    | true =>
      simp [scan, hg] at h
      cases h
      exact ⟨Nat.lt_succ_self _, hg⟩

/-- A finite list of degree values transports equality by ordinary induction. -/
theorem transport {v : Nat → Int} {k : Nat}
    (h : ∀ t, t < k → v (t + 1) = v t) : v k = v 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact (h k (Nat.lt_succ_self k)).trans (ih (fun t ht => h t (by omega)))

/-- General dimension-independent extraction from a degree obstruction. -/
theorem finite_obstruction (good : Nat → Bool) (b k : Nat) (v : Nat → Int)
    (endpoints : v k ≠ v 0)
    (step : (∀ i, i < b → good i = false) →
      ∀ t, t < k → v (t + 1) = v t) :
    ∃ i, scan good b = some i ∧ i < b ∧ good i = true := by
  cases hs : scan good b with
  | none => exact False.elim (endpoints (transport (step ((scan_none_iff good b).mp hs))))
  | some i => exact ⟨i, rfl, scan_sound hs⟩

/-- Sign of a crosspolytope facet, encoded by its negative coordinate flags. -/
def facetSign : List Bool → Int
  | [] => 1
  | s :: ss => (if s then -1 else 1) * facetSign ss

theorem antipodal_facet_sign (ss : List Bool) :
    facetSign (ss.map Bool.not) = (-1 : Int) ^ ss.length * facetSign ss := by
  induction ss with
  | nil => decide
  | cons s ss ih =>
    cases s <;>
      simp [facetSign, ih, Int.pow_succ, Int.mul_assoc, Int.mul_comm, Int.mul_left_comm, Int.neg_mul_neg]

namespace Octahedron

/-- 0,1,2 denote +e₁,+e₂,+e₃; 3,4,5 denote their respective negatives. -/
abbrev Label := Fin 6

def compatible (u v : Label) : Bool :=
  (u.val + 3) % 6 != v.val

def admissible (a b c d : Label) : Bool :=
  compatible a b && compatible a c && compatible a d &&
  compatible b c && compatible b d && compatible c d

/-- Coefficient of the oriented all-positive facet in a labeled triangle. -/
def top (a b c : Label) : Int :=
  match a.val, b.val, c.val with
  | 0, 1, 2 | 1, 2, 0 | 2, 0, 1 => 1
  | 0, 2, 1 | 1, 0, 2 | 2, 1, 0 => -1
  | _, _, _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
/-- A tetrahedron in one closed octahedral facet has zero oriented boundary count. -/
theorem four_label_cocycle :
    ∀ a b c d : Label, admissible a b c d = true →
    top b c d - top a c d + top a b d - top a b c = 0 := by
  decide

/-- Signed count on the two triangles of a vertical rectangular side. -/
def side (a b A B : Label) : Int := top a A B - top a b B

/-- The three tetrahedra of a prism over a triangle telescope. -/
theorem triangle_prism (a b c A B C : Label)
    (h₀ : admissible a A B C = true)
    (h₁ : admissible a b B C = true)
    (h₂ : admissible a b c C = true) :
    top A B C - top a b c =
    side b c B C - side a c A C + side a b A B := by
  have p := four_label_cocycle a A B C h₀
  have q := four_label_cocycle a b B C h₁
  have r := four_label_cocycle a b c C h₂
  unfold side
  omega

structure Triangle (α : Type) where
  weight : Int
  a : α
  b : α
  c : α

def evalChain {α : Type} (t : List (Triangle α)) (f : α → α → α → Int) : Int :=
  match t with
  | [] => 0
  | x :: xs => x.weight * f x.a x.b x.c + evalChain xs f

def coboundary {α : Type} (edge : α → α → Int) (a b c : α) : Int :=
  edge b c - edge a c + edge a b

def degree {α : Type} (triangles : List (Triangle α)) (L : α → Label) : Int :=
  evalChain triangles (fun a b c => top (L a) (L b) (L c))

def prismOK {α : Type} (f g : α → Label) (x : Triangle α) : Prop :=
  admissible (f x.a) (g x.a) (g x.b) (g x.c) = true ∧
  admissible (f x.a) (f x.b) (g x.b) (g x.c) = true ∧
  admissible (f x.a) (f x.b) (f x.c) (g x.c) = true

theorem chain_prism {α : Type} (triangles : List (Triangle α)) (f g : α → Label)
    (localOK : ∀ x ∈ triangles, prismOK f g x) :
    degree triangles g - degree triangles f =
      evalChain triangles (coboundary (fun a b => side (f a) (f b) (g a) (g b))) := by
  induction triangles with
  | nil => simp [degree, evalChain]
  | cons x xs ih =>
    obtain ⟨h₀, h₁, h₂⟩ := localOK x (List.mem_cons_self)
    have hp := triangle_prism _ _ _ _ _ _ h₀ h₁ h₂
    have ht := ih (fun y hy => localOK y (List.mem_cons_of_mem _ hy))
    simp only [degree, evalChain] at ht ⊢
    simp only [coboundary] at ht ⊢
    have hs := congrArg (fun i : Int => x.weight * i) hp
    simp only [Int.mul_sub] at hs
    omega

/-- A boundary certificate is only needed at the explicitly computed side cochain. -/
theorem degree_step {α : Type} (triangles : List (Triangle α)) (f g : α → Label)
    (localOK : ∀ x ∈ triangles, prismOK f g x)
    (boundaryZero :
      evalChain triangles (coboundary (fun a b => side (f a) (f b) (g a) (g b))) = 0) :
    degree triangles g = degree triangles f := by
  have h := (chain_prism triangles f g localOK).trans boundaryZero
  omega

/-- The base cycle is ordered by coordinate axis; weights are products of signs. -/
def baseCycle : List (Triangle Label) := [
  ⟨1,  0, 1, 2⟩, ⟨-1, 0, 1, 5⟩, ⟨-1, 0, 4, 2⟩, ⟨1,  0, 4, 5⟩,
  ⟨-1, 3, 1, 2⟩, ⟨1,  3, 1, 5⟩, ⟨1,  3, 4, 2⟩, ⟨-1, 3, 4, 5⟩]

def antipode (u : Label) : Label := ⟨(u.val + 3) % 6, by omega⟩

theorem base_cycle_closed (edge : Label → Label → Int) :
    evalChain baseCycle (coboundary edge) = 0 := by
  simp [baseCycle, evalChain, coboundary]
  omega

theorem base_identity : degree baseCycle id = 1 := by decide
theorem base_antipode : degree baseCycle antipode = -1 := by decide

end Octahedron
end ConstructiveHairyBall
