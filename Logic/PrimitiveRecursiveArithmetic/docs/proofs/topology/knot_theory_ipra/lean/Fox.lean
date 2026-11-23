import Std

/-!
Explicit integer lifts for Fox colors. Every local identity descends to residues.
The main theorem, `closed_iff_dvd`, treats arbitrary signed two-strand words
of the form σ₁^m and an update which reduces modulo n after *each* crossing.
-/
namespace KnotPacket.Fox

def reflect (under over : Int) : Int := over + over - under

theorem typeI (x : Int) : reflect x x = x := by
  unfold reflect
  omega

theorem typeII (x y : Int) : reflect (reflect x y) y = x := by
  unfold reflect
  omega

theorem typeIII (x y z : Int) :
    reflect (reflect x y) z = reflect (reflect x z) (reflect y z) := by
  unfold reflect
  omega

theorem reflect_congr {n x x' y y' : Int}
    (hx : x % n = x' % n) (hy : y % n = y' % n) :
    reflect x y % n = reflect x' y' % n := by
  unfold reflect
  rw [Int.sub_emod, Int.sub_emod (y' + y'), Int.add_emod y y,
      Int.add_emod y' y', hx, hy]

abbrev Row := Int × Int

def difference (w : Row) := w.1 - w.2
def shift (h : Int) (w : Row) : Row := (w.1 + h, w.2 + h)
def shear (m : Int) (w : Row) := shift (m * difference w) w

def pos (w : Row) : Row := (reflect w.2 w.1, w.1)
def neg (w : Row) : Row := (w.2, reflect w.1 w.2)

theorem difference_shift (h : Int) (w : Row) :
    difference (shift h w) = difference w := by
  simp only [difference, shift]
  omega

theorem shift_shift (k h : Int) (w : Row) :
    shift k (shift h w) = shift (h + k) w := by
  simp [shift, Int.add_assoc]

theorem shear_add (k h : Int) (w : Row) :
    shear k (shear h w) = shear (h + k) w := by
  simp only [shear, difference_shift, shift_shift, Int.add_mul]

theorem pos_shear (w : Row) : pos w = shear 1 w := by
  apply Prod.ext <;> simp [pos, shear, reflect, shift, difference] <;> omega

theorem neg_shear (w : Row) : neg w = shear (-1) w := by
  apply Prod.ext <;> simp [neg, shear, reflect, shift, difference] <;> omega

def iterate (f : Row → Row) (w : Row) : Nat → Row
  | 0 => w
  | k + 1 => f (iterate f w k)

theorem positive_power (w : Row) (k : Nat) : iterate pos w k = shear k w := by
  induction k with
  | zero => simp [iterate, shear, shift]
  | succ k ih =>
    rw [iterate, ih, pos_shear, shear_add, Int.natCast_succ]

theorem negative_power (w : Row) (k : Nat) : iterate neg w k = shear (-(k : Int)) w := by
  induction k with
  | zero => simp [iterate, shear, shift]
  | succ k ih =>
    rw [iterate, ih, neg_shear, shear_add, Int.natCast_succ]
    congr 1
    omega

def reduce (n : Int) (w : Row) : Row := (w.1 % n, w.2 % n)

theorem reduce_pos (n : Int) (w : Row) :
    reduce n (pos (reduce n w)) = reduce n (pos w) := by
  apply Prod.ext
  · exact reflect_congr (Int.emod_emod ..) (Int.emod_emod ..)
  · exact Int.emod_emod ..

theorem reduce_neg (n : Int) (w : Row) :
    reduce n (neg (reduce n w)) = reduce n (neg w) := by
  apply Prod.ext
  · exact Int.emod_emod ..
  · exact reflect_congr (Int.emod_emod ..) (Int.emod_emod ..)

theorem iterate_reduced {f : Row → Row} (n : Int) (w : Row)
    (h : ∀ x, reduce n (f (reduce n x)) = reduce n (f x)) (k : Nat) :
    iterate (fun x => reduce n (f x)) (reduce n w) k = reduce n (iterate f w k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [iterate, ih, h]

def signedRun (n : Int) (w : Row) : Int → Row
  | .ofNat k => iterate (fun x => reduce n (pos x)) (reduce n w) k
  | .negSucc k => iterate (fun x => reduce n (neg x)) (reduce n w) (k+1)

theorem signed_power (n m : Int) (w : Row) : signedRun n w m = reduce n (shear m w) := by
  cases m with
  | ofNat k =>
    exact (iterate_reduced n w (reduce_pos n) k).trans
      (congrArg (reduce n) (positive_power w k))
  | negSucc k =>
    exact (iterate_reduced n w (reduce_neg n) (k+1)).trans
      (congrArg (reduce n) (negative_power w (k+1)))

theorem shift_fixed (a h n : Int) : (a + h) % n = a % n ↔ n ∣ h := by
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, Int.dvd_iff_emod_eq_zero]
  have e : a + h - a = h := by omega
  rw [e]

theorem closed_iff_dvd (n m : Int) (w : Row) :
    signedRun n w m = reduce n w ↔ n ∣ m * difference w := by
  rw [signed_power]
  constructor
  · intro h
    exact (shift_fixed w.1 (m * difference w) n).mp (congrArg Prod.fst h)
  · intro h
    exact Prod.ext ((shift_fixed w.1 _ n).mpr h) ((shift_fixed w.2 _ n).mpr h)

/-! Conway rational tangles. Each word acts on actual boundary colors
and, independently, on their two integer slope coefficients. -/

inductive Twist where
  | right | left | quarterTurn
  deriving DecidableEq, Repr

structure Corners where
  nw : Int
  ne : Int
  se : Int
  sw : Int
  deriving DecidableEq, Repr

structure Parameters where
  base : Int
  unit : Int
  p : Int
  q : Int
  deriving DecidableEq, Repr

def boundary (s : Parameters) : Corners :=
  ⟨s.base, s.base + s.p*s.unit, s.base + (s.p+s.q)*s.unit, s.base + s.q*s.unit⟩

def moveColors (c : Corners) : Twist → Corners
  | .right => ⟨c.nw, c.se, reflect c.ne c.se, c.sw⟩
  | .left => ⟨c.nw, reflect c.se c.ne, c.ne, c.sw⟩
  | .quarterTurn => ⟨c.sw, c.nw, c.ne, c.se⟩

def moveParameters (s : Parameters) : Twist → Parameters
  | .right => {s with p := s.p + s.q}
  | .left => {s with p := s.p - s.q}
  | .quarterTurn => {s with base := s.base + s.q*s.unit, p := -s.q, q := s.p}

theorem move_boundary (s : Parameters) (op : Twist) :
    moveColors (boundary s) op = boundary (moveParameters s op) := by
  cases op <;> simp [moveColors, moveParameters, boundary, reflect,
    Int.add_mul, Int.sub_mul, Int.neg_mul] <;> omega

theorem boundary_word (s : Parameters) (ops : List Twist) :
    ops.foldl moveColors (boundary s) = boundary (ops.foldl moveParameters s) := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.foldl_cons, move_boundary]
    apply ih

def numeratorCloses (n : Int) (c : Corners) :=
  c.ne % n = c.nw % n ∧ c.se % n = c.sw % n

def denominatorCloses (n : Int) (c : Corners) :=
  c.sw % n = c.nw % n ∧ c.se % n = c.ne % n

theorem numerator_criterion (n : Int) (s : Parameters) :
    numeratorCloses n (boundary s) ↔ n ∣ s.p*s.unit := by
  simp only [numeratorCloses, boundary]
  have e : s.base + (s.p+s.q)*s.unit = (s.base+s.q*s.unit) + s.p*s.unit := by
    rw [Int.add_mul]
    omega
  rw [e, shift_fixed, shift_fixed, and_self]

theorem denominator_criterion (n : Int) (s : Parameters) :
    denominatorCloses n (boundary s) ↔ n ∣ s.q*s.unit := by
  simp only [denominatorCloses, boundary]
  have e : s.base + (s.p+s.q)*s.unit = (s.base+s.p*s.unit) + s.q*s.unit := by
    rw [Int.add_mul]
    omega
  rw [e, shift_fixed, shift_fixed, and_self]

end KnotPacket.Fox
