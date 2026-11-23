/-
# Finite sums and the handshaking lemma

This file uses Lean's Init library. The final statements take natural-number
graph masks. The intermediate matrix theorems express the combinatorial
identities independently of a choice of encoding.
-/
import Init

namespace GraphCounting

/-- Sum the first n natural values of f. -/
def prefixSum (n : Nat) (f : Nat → Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => prefixSum k f + f k

theorem prefix_congr (n : Nat) (f g : Nat → Nat) (equal : ∀ i, f i = g i) :
    prefixSum n f = prefixSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change prefixSum n f + f n = prefixSum n g + g n
    rw [ih, equal n]

theorem prefix_zero (n : Nat) : prefixSum n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem prefix_add (n : Nat) (f g : Nat → Nat) :
    prefixSum n (fun i => f i + g i) = prefixSum n f + prefixSum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change prefixSum n (fun i => f i + g i) + (f n + g n) =
      (prefixSum n f + f n) + (prefixSum n g + g n)
    rw [ih]
    exact Nat.add_add_add_comm _ _ _ _

/-- Finite Fubini, without assumptions on the matrix. -/
theorem transpose_sum (m n : Nat) (w : Nat → Nat → Nat) :
    prefixSum m (fun i => prefixSum n (w i)) =
    prefixSum n (fun j => prefixSum m (fun i => w i j)) := by
  induction m with
  | zero => exact (prefix_zero n).symm
  | succ m ih =>
    change prefixSum m (fun i => prefixSum n (w i)) + prefixSum n (w m) =
      prefixSum n (fun j => prefixSum m (fun i => w i j) + w m j)
    rw [prefix_add, ih]

/-- Each unordered pair i < j contributes the matrix entry w i j once. -/
def edgeTotal (w : Nat → Nat → Nat) (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | k + 1 => edgeTotal w k + prefixSum k (fun i => w i k)

theorem weighted_handshaking (w : Nat → Nat → Nat)
    (symm : ∀ i j, w i j = w j i) (noLoops : ∀ i, w i i = 0) (n : Nat) :
    prefixSum n (fun i => prefixSum n (w i)) = 2 * edgeTotal w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change prefixSum n (fun i => prefixSum n (w i) + w i n) +
      (prefixSum n (w n) + w n n) =
      2 * (edgeTotal w n + prefixSum n (fun i => w i n))
    have row_eq_col : prefixSum n (w n) = prefixSum n (fun i => w i n) :=
      prefix_congr n _ _ (fun i => symm n i)
    rw [prefix_add, ih, row_eq_col, noLoops, Nat.add_zero, Nat.mul_add,
        Nat.two_mul (prefixSum n (fun i => w i n)), Nat.add_assoc]

/-- Least binary digit and quotient by two by explicit primitive recursion.
    Their division-with-remainder identity is proved below. -/
def oddDigit : Nat → Bool
  | 0 => false
  | n + 1 => !(oddDigit n)

def half : Nat → Nat
  | 0 => 0
  | n + 1 => half n + (oddDigit n).toNat

theorem half_spec (n : Nat) : 2 * half n + (oddDigit n).toNat = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change 2 * (half n + (oddDigit n).toNat) + (!(oddDigit n)).toNat = n + 1
    rw [Nat.mul_add]
    cases digit : oddDigit n <;> rw [digit] at ih <;> exact congrArg Nat.succ ih

def bitAt : Nat → Nat → Bool
  | 0, mask => oddDigit mask
  | i + 1, mask => bitAt i (half mask)

/-- Lexicographic position of the ordered pair u < v on vertices 0,...,n-1. -/
def upperWeight (n mask u v : Nat) : Nat :=
  if u < v then
    (bitAt (prefixSum u (fun i => n - (i + 1)) + (v - u - 1)) mask).toNat
  else 0

/-- Exactly one of the two ordered entries can be nonzero. -/
def edgeWeight (n mask u v : Nat) : Nat :=
  upperWeight n mask u v + upperWeight n mask v u

theorem edgeWeight_symm (n mask u v : Nat) :
    edgeWeight n mask u v = edgeWeight n mask v u := Nat.add_comm _ _

theorem edgeWeight_diag (n mask v : Nat) : edgeWeight n mask v v = 0 := by
  unfold edgeWeight upperWeight
  rw [if_neg (Nat.lt_irrefl v)]

def degree (n mask v : Nat) : Nat := prefixSum n (edgeWeight n mask v)
def edgeCount (n mask : Nat) : Nat := edgeTotal (edgeWeight n mask) n

theorem handshaking (n mask : Nat) :
    prefixSum n (degree n mask) = 2 * edgeCount n mask :=
  weighted_handshaking (edgeWeight n mask) (edgeWeight_symm n mask)
    (edgeWeight_diag n mask) n

theorem oddDigit_add (a b : Nat) :
    oddDigit (a+b) = Bool.xor (oddDigit a) (oddDigit b) := by
  induction b with
  | zero =>
    change oddDigit a = Bool.xor (oddDigit a) false
    cases oddDigit a <;> rfl
  | succ b ih =>
    change (!(oddDigit (a+b))) = Bool.xor (oddDigit a) (!(oddDigit b))
    rw [ih]
    cases oddDigit a <;> cases oddDigit b <;> rfl

theorem oddDigit_toNat (b : Bool) : oddDigit b.toNat = b := by cases b <;> rfl

theorem prefix_parity (n : Nat) (f : Nat → Nat) :
    oddDigit (prefixSum n (fun i => (oddDigit (f i)).toNat)) =
    oddDigit (prefixSum n f) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change oddDigit (prefixSum n (fun i => (oddDigit (f i)).toNat) +
      (oddDigit (f n)).toNat) = oddDigit (prefixSum n f + f n)
    rw [oddDigit_add, ih, oddDigit_toNat, ← oddDigit_add]

def oddDegreeCount (n mask : Nat) : Nat :=
  prefixSum n (fun i => (oddDigit (degree n mask i)).toNat)

theorem odd_degree_count_digit (n mask : Nat) : oddDigit (oddDegreeCount n mask) = false := by
  unfold oddDegreeCount
  rw [prefix_parity, handshaking, Nat.two_mul, oddDigit_add]
  cases oddDigit (edgeCount n mask) <;> rfl

/-- The halved count is an explicit witness to evenness. -/
theorem odd_degree_count_even (n mask : Nat) :
    2 * half (oddDegreeCount n mask) = oddDegreeCount n mask := by
  have result := half_spec (oddDegreeCount n mask)
  rw [odd_degree_count_digit] at result
  exact result

#print axioms transpose_sum
#print axioms weighted_handshaking
#print axioms handshaking
#print axioms odd_degree_count_even

end GraphCounting
