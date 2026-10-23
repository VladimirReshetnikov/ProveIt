import DiophantineConsistency.ScalarPRCode

/-! # Supplied scalar programs for elementary natural arithmetic -/

namespace DiophantineConsistency.DirectScalar

open ScalarPRCode
abbrev R (f : ℕ → ℕ) := ScalarPRCode.Realizes f

def identity : R id :=
  ⟨.pair .left .right, fun n => Nat.pair_unpair n⟩

def constant : (k : ℕ) → R (fun _ => k)
  | 0 => Realizes.zero
  | k + 1 => Realizes.succ.comp (constant k)

def successor {f : ℕ → ℕ} (p : R f) : R (fun n => f n + 1) :=
  Realizes.succ.comp p

/-- Recurse on the second component of a paired input. -/
def recursion {f : ℕ → ℕ} {g : ℕ → ℕ → ℕ → ℕ}
    (p : R f) (q : R (fun n => g n.unpair.1 n.unpair.2.unpair.1 n.unpair.2.unpair.2)) :
    R (fun n => n.unpair.2.rec (f n.unpair.1) (fun i acc => g n.unpair.1 i acc)) :=
  (Realizes.prec p q).ofEq (fun n => by simp [Nat.unpaired])

def addition : R (fun n => n.unpair.1 + n.unpair.2) := by
  let p := recursion (g := fun _ _ acc => acc + 1)
    identity (Realizes.succ.comp (Realizes.right.comp Realizes.right))
  refine p.ofEq ?_
  intro n
  change Nat.rec (motive := fun _ => ℕ) n.unpair.1 (fun _ acc => acc + 1) n.unpair.2 = _
  induction n.unpair.2 with
  | zero => rfl
  | succ k ih =>
    change Nat.rec (motive := fun _ => ℕ) n.unpair.1 (fun _ acc => acc + 1) k + 1 = _
    rw [ih]
    omega

def add {f g : ℕ → ℕ} (p : R f) (q : R g) : R (fun n => f n + g n) :=
  (addition.comp (p.pair q)).ofEq (fun _ => by simp)

def predecessor : R Nat.pred := by
  let p := recursion (g := fun _ i _ => i) Realizes.zero (Realizes.left.comp Realizes.right)
  refine (p.comp (Realizes.zero.pair identity)).ofEq ?_
  intro n
  simp only [Nat.unpair_pair, id_eq]
  cases n <;> rfl

def pred {f : ℕ → ℕ} (p : R f) : R (fun n => (f n).pred) :=
  predecessor.comp p

def subtraction : R (fun n => n.unpair.1 - n.unpair.2) := by
  let p := recursion (g := fun _ _ acc => acc.pred)
    identity (pred (Realizes.right.comp Realizes.right))
  refine p.ofEq ?_
  intro n
  change Nat.rec (motive := fun _ => ℕ) n.unpair.1 (fun _ acc => acc.pred) n.unpair.2 = _
  induction n.unpair.2 with
  | zero => rfl
  | succ k ih =>
    change (Nat.rec (motive := fun _ => ℕ) n.unpair.1 (fun _ acc => acc.pred) k).pred = _
    rw [ih]
    rw [Nat.pred_eq_sub_one]
    omega

def sub {f g : ℕ → ℕ} (p : R f) (q : R g) : R (fun n => f n - g n) :=
  (subtraction.comp (p.pair q)).ofEq (fun _ => by simp)

def multiplication : R (fun n => n.unpair.1 * n.unpair.2) := by
  let p := recursion (g := fun z _ acc => z + acc)
    Realizes.zero (add Realizes.left (Realizes.right.comp Realizes.right))
  refine p.ofEq ?_
  intro n
  change Nat.rec (motive := fun _ => ℕ) 0 (fun _ acc => n.unpair.1 + acc) n.unpair.2 = _
  induction n.unpair.2 <;> simp_all [Nat.mul_succ, Nat.add_comm]

def mul {f g : ℕ → ℕ} (p : R f) (q : R g) : R (fun n => f n * g n) :=
  (multiplication.comp (p.pair q)).ofEq (fun _ => by simp)

/-- A branch program takes `(thenValue,elseValue)` as parameter and the
tested number as its recursion argument. -/
def zeroBranch : R (fun n =>
    if n.unpair.2 = 0 then n.unpair.1.unpair.1 else n.unpair.1.unpair.2) := by
  let p := recursion (g := fun z _ _ => z.unpair.2)
    Realizes.left (Realizes.right.comp Realizes.left)
  refine p.ofEq ?_
  intro n
  change Nat.rec (motive := fun _ => ℕ) n.unpair.1.unpair.1
    (fun _ _ => n.unpair.1.unpair.2) n.unpair.2 = _
  cases n.unpair.2 <;> simp

def ifZero {f g h : ℕ → ℕ} (p : R f) (q : R g) (r : R h) :
    R (fun n => if f n = 0 then g n else h n) :=
  (zeroBranch.comp ((q.pair r).pair p)).ofEq (fun _ => by simp)

def ifEq {f g h k : ℕ → ℕ} (p : R f) (q : R g) (r : R h) (s : R k) :
    R (fun n => if f n = g n then h n else k n) :=
  (ifZero (add (sub p q) (sub q p)) r s).ofEq (fun n => by
    have h : f n - g n + (g n - f n) = 0 ↔ f n = g n := by omega
    simp only [h])

/-- Iteration of a supplied unary program from a supplied numerical seed. -/
def iterate {f : ℕ → ℕ} (p : R f) (initial : ℕ) :
    R (fun n => n.rec initial (fun _ acc => f acc)) :=
  ((recursion (g := fun _ _ acc => f acc)
    (constant initial) (p.comp (Realizes.right.comp Realizes.right))).comp
    (Realizes.zero.pair identity)).ofEq (fun _ => by simp)

#print axioms ifEq

end DiophantineConsistency.DirectScalar
