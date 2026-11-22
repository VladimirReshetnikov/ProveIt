import Std

/-!
# Ternary coding for Lipschitz sample tables

All theorems in this file concern ordinary Lean integers and lists. The
quantizer input is the clipped rational sample in units of the value mesh;
a common positive denominator clears all comparisons. The paper derives the
three hypotheses of `edgeUpper` from the requested evaluation precisions.
-/

namespace LipschitzEntropy

theorem edgeUpper (D X Y q r : Int) (positive : 0 < D)
    (roundLeft : 2 * (D*q) ≤ 2*X + D)
    (neighbours : 4*X ≤ 4*Y + 3*D)
    (roundRight : 2*Y ≤ 2*(D*r) + D) : q ≤ r + 1 := by
  by_cases h : q ≤ r + 1
  · exact h
  · have gap : r + 2 ≤ q := by omega
    have big := Int.mul_le_mul_of_nonneg_left gap (Int.le_of_lt positive)
    rw [Int.mul_add] at big
    omega

/-- Nearest integer to X / D, with half-integers rounded upwards. -/
def roundNearest (X D : Int) : Int := (2*X + D) / (2*D)

theorem roundNearest_bounds (X D : Int) (positive : 0 < D) :
    2*(D*roundNearest X D) ≤ 2*X + D ∧
    2*X ≤ 2*(D*roundNearest X D) + D := by
  let q := roundNearest X D
  have floorBounds := (Int.ediv_eq_iff_of_pos (x := 2*X + D) (y := q)
    (k := 2*D) (by omega)).mp (show (2*X + D)/(2*D) = q from rfl)
  have swap : q*(2*D) = 2*(D*q) := by ac_rfl
  rw [swap] at floorBounds
  change 2*(D*q) ≤ 2*X + D ∧ 2*X ≤ 2*(D*q) + D
  omega

theorem roundedEdge (X Y D : Int) (positive : 0 < D)
    (xy : 4*X ≤ 4*Y + 3*D) (yx : 4*Y ≤ 4*X + 3*D) :
    roundNearest X D - 1 ≤ roundNearest Y D ∧
    roundNearest Y D ≤ roundNearest X D + 1 := by
  obtain ⟨xlo, xhi⟩ := roundNearest_bounds X D positive
  obtain ⟨ylo, yhi⟩ := roundNearest_bounds Y D positive
  have upper := edgeUpper D X Y _ _ positive xlo xy yhi
  have lower := edgeUpper D Y X _ _ positive ylo yx xhi
  omega

inductive Step where
  | down | same | up
deriving Repr, DecidableEq

def Step.next : Step → Int → Int
  | .down, x => x - 1
  | .same, x => x
  | .up, x => x + 1

def stepTo (x y : Int) : Step :=
  if y < x then .down else if x < y then .up else .same

theorem stepTo_correct (x y : Int) (lo : x-1 ≤ y) (hi : y ≤ x+1) :
    (stepTo x y).next x = y := by
  unfold stepTo
  split
  · simp only [Step.next]; omega
  · split
    · simp only [Step.next]; omega
    · simp only [Step.next]; omega

def localSteps (x : Int) : List Int → Prop
  | [] => True
  | y :: ys => x-1 ≤ y ∧ y ≤ x+1 ∧ localSteps y ys

def encode (x : Int) : List Int → List Step
  | [] => []
  | y :: ys => stepTo x y :: encode y ys

def decode (x : Int) : List Step → List Int
  | [] => []
  | s :: ss => let y := s.next x; y :: decode y ss

theorem decode_encode (xs : List Int) (x : Int) (h : localSteps x xs) :
    decode x (encode x xs) = xs := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih =>
    obtain ⟨lo, hi, more⟩ := h
    simp only [encode, decode, stepTo_correct x y lo hi, ih y more]

theorem encode_length (xs : List Int) (x : Int) :
    (encode x xs).length = xs.length := by
  induction xs generalizing x with
  | nil => rfl
  | cons y ys ih => simp [encode, ih]

/-- Exhaustive catalog of length-n ternary suffixes; calculus uses packed indices. -/
def words : Nat → List (List Step)
  | 0 => [[]]
  | n+1 =>
    let tails := words n
    tails.map (Step.down :: ·) ++ tails.map (Step.same :: ·) ++ tails.map (Step.up :: ·)

theorem words_length (n : Nat) : (words n).length = 3^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [words, List.length_append, List.length_map, ih, Nat.pow_succ]
    omega

theorem mem_words (ss : List Step) : ss ∈ words ss.length := by
  induction ss with
  | nil => simp [words]
  | cons s ss ih => cases s <;> simp [words, ih]

end LipschitzEntropy
