import Std
import Init.Data.Nat.Sqrt.Lemmas

/-! Executable first-order finite-stage model. All natural inputs may vary.
The report imposes n ≥ 2, M,H,D > 0, and positive side numerators. -/
namespace Hyperbox

abbrev Point := List Nat

/-- All coordinate lists of the specified dimension on the normalized m-grid. -/
def grid (m : Nat) : Nat → List Point
  | 0 => [[]]
  | n+1 => (List.range (m+1)).flatMap fun j => (grid m n).map (List.cons j)

theorem mem_grid (m n : Nat) (p : Point) :
    p ∈ grid m n ↔ p.length = n ∧ ∀ j ∈ p, j ≤ m := by
  induction n generalizing p with
  | zero => cases p <;> simp [grid]
  | succ n ih =>
    cases p with
    | nil => simp [grid]
    | cons x xs =>
      simp [grid, ih, Nat.lt_succ_iff]
      exact and_left_comm

def boundary (m : Nat) (p : Point) : Bool := p.any fun x => x == 0 || x == m

def nodes (m n : Nat) := (grid m n).filter (boundary m)

/-- For valid grid vectors, both points belong to one closed facet. -/
def share (m : Nat) (p q : Point) : Bool :=
  (p.zip q).any fun (x,y) => x == y && (x == 0 || x == m)

theorem share_iff (m : Nat) (p q : Point) :
    share m p q = true ↔ ∃ v ∈ p.zip q, v.1 = v.2 ∧ (v.1 = 0 ∨ v.1 = m) := by
  simp [share]

def absDiff (i j : Nat) := (i-j)+(j-i)

/-- For sides A_i/D and coordinate indices i,j, the actual squared distance is
    sqChord A p q / (D*m)^2. -/
def sqChord (A p q : Point) : Nat :=
  (A.zipWith (fun a v => (a*v)^2) (p.zipWith absDiff q)).sum

def ceilRoot (s : Nat) : Nat :=
  let r := s.sqrt
  if r*r = s then r else r+1

theorem rootBracket (s : Nat) :
    s ≤ ceilRoot s * ceilRoot s ∧ ceilRoot s ≤ s.sqrt + 1 ∧ s.sqrt * s.sqrt ≤ s := by
  rw [ceilRoot]
  split <;> rename_i e
  · exact ⟨Nat.le_of_eq e.symm, Nat.le_succ _, Nat.sqrt_le s⟩
  · exact ⟨Nat.le_of_lt (Nat.lt_succ_sqrt s), Nat.le_refl _, Nat.sqrt_le s⟩

def edgeCost (A : Point) (H : Nat) (p q : Point) := ceilRoot (H^2 * sqChord A p q)

def foldMin {α : Type} (top : Nat) (f : α → Nat) : List α → Nat
  | [] => top
  | x::xs => min (f x) (foldMin top f xs)

private theorem min_le_disj (a b c : Nat) : min a b ≤ c ↔ a ≤ c ∨ b ≤ c := by omega

theorem foldMin_le_iff {α : Type} (top b : Nat) (hb : b < top) (f : α → Nat) (s : List α) :
    foldMin top f s ≤ b ↔ ∃ x ∈ s, f x ≤ b := by
  induction s with
  | nil => simp [foldMin, Nat.not_le_of_lt hb]
  | cons x xs ih => simp [foldMin, min_le_disj, ih]

section FiniteOptimization
variable {α : Type} [DecidableEq α]
variable (vertices : List α) (edge : α → α → Bool) (weight : α → α → Nat) (top : Nat)

/-- Capped Bellman recurrence. The cap is a sentinel for no route. This direct
    implementation recomputes equal subproblems; a tabulated layer gives the same values. -/
def distanceCost : Nat → α → α → Nat
  | 0, p, q => if p=q then 0 else top
  | k+1, p, q => min (if p=q then 0 else top)
      (foldMin top (fun r => if edge p r then weight p r +
        distanceCost k r q else top) vertices)

/-- A walk costing at most b in at most k legs. A shared facet is required
    for every leg. The empty walk is always legal from a point to itself. -/
def Feasible : Nat → α → α → Nat → Prop
  | 0, p, q, _ => p=q
  | k+1, p, q, b => p=q ∨ ∃ r ∈ vertices,
      edge p r = true ∧ weight p r ≤ b ∧ Feasible k r q (b-weight p r)

theorem distanceCost_correct (k : Nat) (p q : α) (b : Nat) (hb : b < top) :
    distanceCost vertices edge weight top k p q ≤ b ↔ Feasible vertices edge weight k p q b := by
  induction k generalizing p q b with
  | zero =>
    by_cases e : p=q <;> simp [distanceCost, Feasible, e, Nat.not_le_of_lt hb]
  | succ k ih =>
    rw [distanceCost, Feasible, min_le_disj, foldMin_le_iff _ _ hb]
    have stop : (if p=q then 0 else top) ≤ b ↔ p=q := by
      by_cases e : p=q <;> simp [e, Nat.not_le_of_lt hb]
    rw [stop]
    apply or_congr_right
    constructor
    · rintro ⟨r, hr, hv⟩
      cases he : edge p r with
      | false => simp [he, Nat.not_le_of_lt hb] at hv
      | true =>
        simp only [he, if_true] at hv
        refine ⟨r, hr, he, ?_, (ih r q _ (by omega)).mp ?_⟩ <;> omega
    · rintro ⟨r, hr, he, hw, htail⟩
      have hc := (ih r q _ (by omega)).mpr htail
      refine ⟨r, hr, ?_⟩
      simp only [he, if_true]
      omega

end FiniteOptimization

/-- Endpoints in the nonempty input list are retained as maximizing witnesses. -/
def bestFrom {α : Type} (score : α → Nat) (x : α) : List α → α
  | [] => x
  | y::ys => bestFrom score (if score x < score y then y else x) ys

theorem bestFrom_spec {α : Type} (score : α → Nat) (x : α) (s : List α) :
    bestFrom score x s ∈ x::s ∧ ∀ y ∈ x::s, score y ≤ score (bestFrom score x s) := by
  induction s generalizing x with
  | nil => simp [bestFrom]
  | cons z zs ih =>
    by_cases hz : score x < score z
    · rw [bestFrom, if_pos hz]
      obtain ⟨hm, hb⟩ := ih z
      constructor
      · exact List.mem_cons_of_mem x hm
      · intro y hy
        rcases List.mem_cons.mp hy with h | h
        · subst y; exact Nat.le_trans (Nat.le_of_lt hz) (hb z (by simp))
        · exact hb _ h
    · rw [bestFrom, if_neg hz]
      obtain ⟨hm, hb⟩ := ih x
      constructor
      · rcases List.mem_cons.mp hm with he | he <;> simp [he]
      · intro y hy
        rcases List.mem_cons.mp hy with he | he
        · exact he ▸ hb x (by simp)
        · rcases List.mem_cons.mp he with he | he
          · subst y; exact Nat.le_trans (Nat.le_of_not_gt hz) (hb x (by simp))
          · exact hb _ (List.mem_cons_of_mem _ he)

def topCost (A : Point) (M H : Nat) := 1 + 2*A.length*(H*M*A.sum+1)

def stageDistance (A : Point) (M H : Nat) :=
  distanceCost (nodes M A.length) (share M) (edgeCost A H) (topCost A M H) (2*A.length)

def corner (n : Nat) : Point := List.replicate n 0

def farthest (A : Point) (M H : Nat) : Point :=
  bestFrom (stageDistance A M H (corner A.length)) (corner A.length) (nodes M A.length)

def diameterPair (A : Point) (M H : Nat) : Point × Point :=
  let vs := nodes M A.length
  let p := corner A.length
  bestFrom (fun (x,y) => stageDistance A M H x y) (p,p)
    (vs.flatMap fun x => vs.map (fun y => (x,y)))

-- Two non-unit sides in the smallest connected dimension.
#guard stageDistance [3,4] 1 1 [0,0] [1,1] == 7

end Hyperbox
