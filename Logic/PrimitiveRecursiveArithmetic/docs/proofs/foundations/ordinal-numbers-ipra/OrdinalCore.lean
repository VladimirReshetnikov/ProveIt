import Std

/-! Finite binary encodings of expanded hereditary Cantor normal forms.
The comparison proofs apply to *all* trees. No ordinal well-foundedness
assumption is used. All declarations are ordinary Lean mathematics. -/
namespace OrdinalPacket
inductive T where
  | nil : T
  | cons (head tail : T) : T
deriving DecidableEq, Repr
open T

def cmp : T → T → Ordering
  | nil, nil => .eq
  | nil, cons _ _ => .lt
  | cons _ _, nil => .gt
  | cons a b, cons c d =>
    match cmp a c with
    | .eq => cmp b d
    | .lt => .lt
    | .gt => .gt
termination_by structural x _ => x

@[simp] theorem cmp_self (x : T) : cmp x x = .eq := by
  induction x with
  | nil => rfl
  | cons a b ha hb => simp [cmp, ha, hb]

theorem cmp_eq_iff (x y : T) : cmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | nil => cases y <;> simp [cmp]
  | cons a b ha hb =>
    cases y with
    | nil => simp [cmp]
    | cons c d =>
      cases h : cmp a c with
      | lt => have hn : a ≠ c := fun t => by subst c; simp at h
              simp [cmp, h, hn]
      | eq => have he := (ha c).mp h
              simp [cmp, he, hb]
      | gt => have hn : a ≠ c := fun t => by subst c; simp at h
              simp [cmp, h, hn]

theorem cmp_swap (x y : T) : cmp y x = (cmp x y).swap := by
  induction x generalizing y with
  | nil => cases y <;> rfl
  | cons a b ha hb =>
    cases y with
    | nil => rfl
    | cons c d =>
      cases h : cmp a c <;> simp [cmp, h, ha c, hb d, Ordering.swap]

theorem cons_lt_iff (a b c d : T) :
    cmp (cons a b) (cons c d) = .lt ↔
    cmp a c = .lt ∨ (a = c ∧ cmp b d = .lt) := by
  cases h : cmp a c with
  | eq => simp [cmp, (cmp_eq_iff a c).mp h]
  | lt => simp [cmp, h]
  | gt => have hn : a ≠ c := fun e => by subst c; simp at h
          simp [cmp, h, hn]

theorem cmp_trans (x y z : T) (p : cmp x y = .lt) (q : cmp y z = .lt) :
    cmp x z = .lt := by
  induction x generalizing y z with
  | nil =>
    cases z with
    | nil => cases y <;> simp [cmp] at q
    | cons => rfl
  | cons a b ha hb =>
    cases y with
    | nil => simp [cmp] at p
    | cons c d =>
      cases z with
      | nil => simp [cmp] at q
      | cons e f =>
        apply (cons_lt_iff ..).mpr
        rcases (cons_lt_iff ..).mp p with ac | ⟨rfl, bd⟩ <;>
          rcases (cons_lt_iff ..).mp q with ce | ⟨rfl, df⟩
        · exact Or.inl (ha _ _ ac ce)
        · exact Or.inl ac
        · exact Or.inl ce
        · exact Or.inr ⟨rfl, hb _ _ bd df⟩

def ok : T → Bool
  | nil => true
  | cons a b => ok a && ok b && (match b with
    | nil => true
    | cons c _ => cmp a c != .lt)

def append : T → T → T
  | nil, y => y
  | cons a b, y => cons a (append b y)

def copies (a : T) : Nat → T
  | 0 => nil
  | n+1 => cons a (copies a n)

def fin := copies nil
def principal (a : T) := cons a nil
def one := principal nil
def omega := principal one
def succ (a : T) := append a one

def add : T → T → T
  | nil, y => y
  | cons a b, nil => cons a b
  | cons a b, cons c d =>
    if cmp a c == .lt then cons c d else cons a (add b (cons c d))

def degree : T → T
  | nil => nil
  | cons a _ => a

def monomialProduct (a b : T) : T :=
  match a, b with
  | nil, _ => nil
  | _, nil => a
  | _, cons _ _ => principal (add (degree a) b)

def mul (a : T) : T → T
  | nil => nil
  | cons b bs => add (monomialProduct a b) (mul a bs)

theorem append_assoc (a b c : T) :
    append (append a b) c = append a (append b c) := by
  induction a with
  | nil => rfl
  | cons a b _ ih => simp [append, ih]

@[simp] theorem add_zero (a : T) : add a nil = a := by cases a <;> rfl
@[simp] theorem zero_add (a : T) : add nil a = a := by rfl
@[simp] theorem mul_zero (a : T) : mul a nil = nil := rfl
@[simp] theorem mul_one (a : T) : mul a one = a := by
  cases a <;> simp [mul, one, principal, monomialProduct]

theorem succ_gt (a : T) : cmp a (succ a) = .lt := by
  induction a with
  | nil => rfl
  | cons a b _ ih => simpa [cmp, succ, append] using ih

theorem principal_cmp (a b : T) : cmp (principal a) (principal b) = cmp a b := by
  cases h : cmp a b <;> simp [principal, cmp, h]

theorem finite_add (m n : Nat) : add (fin m) (fin n) = fin (m+n) := by
  induction m with
  | zero => simp [fin, copies]
  | succ m ih =>
    cases n with
    | zero => simp [fin, copies]
    | succ n =>
      simpa [fin, copies, add, cmp, Nat.succ_add] using congrArg (cons nil) ih

example : add one omega = omega := rfl
example : cmp omega (add omega one) = .lt := rfl
example : mul (fin 2) omega = omega := rfl
example : mul omega (fin 2) = cons one (cons one nil) := rfl
end OrdinalPacket
