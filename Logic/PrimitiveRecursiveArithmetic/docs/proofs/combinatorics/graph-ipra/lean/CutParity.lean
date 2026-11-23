import Std

/-! Cycle/cut orthogonality and the parity obstruction for Euler trails.
    Repeated pairs in an edge list represent distinct edge occurrences. -/
namespace GraphCutParity

abbrev Edge := Nat × Nat

/-- Addition over F₂. -/
def add (a b : Bool) : Bool := xor a b

private theorem add_cancel_middle (a b c : Bool) :
    add (add a b) (add b c) = add a c := by
  cases a <;> cases b <;> cases c <;> decide

private theorem add_mix (a b c d : Bool) :
    add (add a b) (add c d) = add (add a c) (add b d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private theorem add_swap (a b c : Bool) : add a (add b c) = add b (add a c) := by
  cases a <;> cases b <;> cases c <;> decide

def edgeBit (side : Nat → Bool) (e : Edge) := add (side e.1) (side e.2)

def crossingParity (side : Nat → Bool) : List Edge → Bool
  | [] => false
  | e :: es => add (edgeBit side e) (crossingParity side es)

def singleton (v u : Nat) : Bool := decide (u = v)
def oddDegree (v : Nat) (es : List Edge) : Bool := crossingParity (singleton v) es

/-- Ordinary degree counts incidence ends, including two for a loop. -/
def endCount (v u : Nat) : Nat := if u = v then 1 else 0

def degree (v : Nat) : List Edge → Nat
  | [] => 0
  | e :: es => (endCount v e.1 + endCount v e.2) + degree v es

private theorem odd_add (a b : Nat) :
    decide ((a+b)%2 = 1) = add (decide (a%2 = 1)) (decide (b%2 = 1)) := by
  by_cases ha : a%2 = 1 <;> by_cases hb : b%2 = 1 <;>
    simp only [ha, hb, decide_true, decide_false, add, Bool.xor_true,
      Bool.xor_false, Bool.not_true, Bool.not_false] <;> simp <;> omega

private theorem odd_endCount (v u : Nat) :
    decide (endCount v u % 2 = 1) = singleton v u := by
  by_cases h : u = v <;> simp [endCount, singleton, h]

theorem oddDegree_eq (v : Nat) (es : List Edge) :
    decide (degree v es % 2 = 1) = oddDegree v es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    change decide (((endCount v e.1 + endCount v e.2) + degree v es) % 2 = 1) =
      add (edgeBit (singleton v) e) (oddDegree v es)
    rw [odd_add, odd_add, ih, odd_endCount, odd_endCount]
    rfl

theorem crossing_add (s t : Nat → Bool) (es : List Edge) :
    crossingParity (fun x => add (s x) (t x)) es =
      add (crossingParity s es) (crossingParity t es) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [crossingParity, edgeBit, ih]
    rw [add_mix (s e.1) (t e.1) (s e.2) (t e.2)]
    apply add_mix

theorem crossing_zero (es : List Edge) : crossingParity (fun _ => false) es = false := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [crossingParity, ih]; rfl

/-- A vertex mask as a sum of singleton masks. A repeated index cancels. -/
def sideOf : List Nat → Nat → Bool
  | [], _ => false
  | v :: vs, u => add (singleton v u) (sideOf vs u)

/-- An ordinary set-membership mask when the index list has distinct entries. -/
theorem sideOf_eq_contains (vs : List Nat) (h : vs.Nodup) (u : Nat) :
    sideOf vs u = decide (u ∈ vs) := by
  induction vs with
  | nil => simp [sideOf]
  | cons v vs ih =>
    obtain ⟨hv, hs⟩ := List.nodup_cons.mp h
    by_cases huv : u = v
    · subst u
      simp [sideOf, singleton, ih hs, hv, add]
    · simp [sideOf, singleton, ih hs, huv, add]

theorem even_orthogonal (es : List Edge) (vs : List Nat)
    (h : ∀ v ∈ vs, oddDegree v es = false) : crossingParity (sideOf vs) es = false := by
  induction vs with
  | nil => exact crossing_zero es
  | cons v vs ih =>
    change crossingParity (fun u => add (singleton v u) (sideOf vs u)) es = false
    rw [crossing_add, ← oddDegree, h v (by simp), ih (fun u hu => h u (by simp [hu]))]
    rfl

theorem even_iff_all_cuts (es : List Edge) :
    (∀ v, oddDegree v es = false) ↔
    (∀ vs : List Nat, vs.Nodup → crossingParity (sideOf vs) es = false) := by
  constructor
  · intro h vs _
    exact even_orthogonal es vs (fun v _ => h v)
  · intro h v
    have hs : sideOf [v] = singleton v := by
      funext u
      change add (singleton v u) false = singleton v u
      cases singleton v u <;> rfl
    simpa [hs, oddDegree] using h [v] (by simp)

theorem crossing_perm (side : Nat → Bool) {a b : List Edge} (h : a.Perm b) :
    crossingParity side a = crossingParity side b := by
  induction h with
  | nil => rfl
  | cons e _ ih => simp only [crossingParity, ih]
  | swap e f es => exact add_swap _ _ _
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

/-- Canonicalize endpoint order to allow either direction of undirected traversal. -/
def edge (a b : Nat) : Edge := if a ≤ b then (a, b) else (b, a)

theorem edgeBit_canonical (side : Nat → Bool) (a b : Nat) :
    edgeBit side (edge a b) = add (side a) (side b) := by
  unfold edge
  split
  · rfl
  · change add (side b) (side a) = add (side a) (side b)
    cases side a <;> cases side b <;> rfl

def walkEdges (a : Nat) : List Nat → List Edge
  | [] => []
  | b :: bs => edge a b :: walkEdges b bs

def lastVertex (a : Nat) : List Nat → Nat
  | [] => a
  | b :: bs => lastVertex b bs

theorem crossing_walk (side : Nat → Bool) (a : Nat) (bs : List Nat) :
    crossingParity side (walkEdges a bs) = add (side a) (side (lastVertex a bs)) := by
  induction bs generalizing a with
  | nil => change false = add (side a) (side a); cases side a <;> rfl
  | cons b bs ih =>
    simp only [walkEdges, crossingParity, lastVertex, edgeBit_canonical, ih]
    exact add_cancel_middle _ _ _

/-- Every input edge occurrence is used once, with multiplicities preserved. -/
def EulerTrail (es : List Edge) (a b : Nat) : Prop :=
  ∃ bs : List Nat, lastVertex a bs = b ∧ (walkEdges a bs).Perm es

theorem euler_boundary {a b : Nat} {es : List Edge} (h : EulerTrail es a b) (v : Nat) :
    oddDegree v es = add (singleton v a) (singleton v b) := by
  obtain ⟨bs, hb, hp⟩ := h
  unfold oddDegree
  rw [← crossing_perm (singleton v) hp, crossing_walk, hb]

theorem euler_closed_even {a : Nat} {es : List Edge} (h : EulerTrail es a a) (v : Nat) :
    oddDegree v es = false := by
  rw [euler_boundary h]
  cases singleton v a <;> rfl

end GraphCutParity
