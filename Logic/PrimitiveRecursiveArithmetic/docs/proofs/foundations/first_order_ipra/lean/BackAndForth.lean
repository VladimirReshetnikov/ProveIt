import Std

/- Relational formulas with equality. An atom carries its argument vector.
   The semantics interprets each pair of symbol and arity independently. -/
namespace FirstOrderPacket

inductive Form : Nat → Type where
  | falsum {k} : Form k
  | eqv {k} (i j : Fin k) : Form k
  | rel {k} (symbol : Nat) (args : List (Fin k)) : Form k
  | conj {k} (a b : Form k) : Form k
  | neg {k} (a : Form k) : Form k
  | ex {k} (a : Form (k+1)) : Form k

def rank {k} : Form k → Nat
  | .falsum | .eqv _ _ | .rel _ _ => 0
  | .conj a b => max (rank a) (rank b)
  | .neg a => rank a
  | .ex a => rank a + 1

abbrev Relations (α : Type) := Nat → List α → Prop
abbrev Env (α : Type) (k : Nat) := Fin k → α

def extend {α k} (x : α) (s : Env α k) : Env α (k+1) :=
  Fin.cases x s

def Holds {α : Type} (m : Relations α) {k} (s : Env α k) : Form k → Prop
  | .falsum => False
  | .eqv i j => s i = s j
  | .rel p xs => m p (xs.map s)
  | .conj a b => Holds m s a ∧ Holds m s b
  | .neg a => ¬ Holds m s a
  | .ex a => ∃ x, Holds m (extend x s) a

variable {α β : Type} (m : Relations α) (n : Relations β)
def Atomic {k} (s : Env α k) (t : Env β k) : Prop :=
  (∀ i j, s i = s j ↔ t i = t j) ∧
  (∀ p (xs : List (Fin k)), m p (xs.map s) ↔ n p (xs.map t))

def Game : (r : Nat) → {k : Nat} → Env α k → Env β k → Prop
  | 0, _, s, t => Atomic m n s t
  | r+1, _, s, t => Atomic m n s t ∧
      (∀ x, ∃ y, Game r (extend x s) (extend y t)) ∧
      (∀ y, ∃ x, Game r (extend x s) (extend y t))

theorem Game.atomic {r k} {s : Env α k} {t : Env β k}
    (h : Game m n r s t) : Atomic m n s t := by
  cases r with
  | zero => exact h
  | succ r => exact h.1

theorem transfer {k} (a : Form k) {r} (s : Env α k) (t : Env β k)
    (hr : rank a ≤ r) (hg : Game m n r s t) : Holds m s a ↔ Holds n t a := by
  induction a generalizing r with
  | falsum => exact Iff.rfl
  | eqv i j => exact (Game.atomic m n hg).1 i j
  | rel p xs => exact (Game.atomic m n hg).2 p xs
  | conj a b ia ib =>
    exact and_congr (ia s t (Nat.le_trans (Nat.le_max_left _ _) hr) hg)
      (ib s t (Nat.le_trans (Nat.le_max_right _ _) hr) hg)
  | neg a ia => exact not_congr (ia s t hr hg)
  | ex a ia =>
    cases r with
    | zero => exact False.elim (Nat.not_succ_le_zero _ hr)
    | succ r =>
      have ha : rank a ≤ r := Nat.le_of_succ_le_succ hr
      constructor
      · intro ⟨x, hx⟩
        obtain ⟨y, hxy⟩ := hg.2.1 x
        exact ⟨y, (ia (extend x s) (extend y t) ha hxy).mp hx⟩
      · intro ⟨y, hy⟩
        obtain ⟨x, hxy⟩ := hg.2.2 y
        exact ⟨x, (ia (extend x s) (extend y t) ha hxy).mpr hy⟩

theorem sentence_transfer (a : Form 0) {r} (hr : rank a ≤ r)
    (hg : Game m n r Fin.elim0 Fin.elim0) :
    Holds m Fin.elim0 a ↔ Holds n Fin.elim0 a :=
  transfer m n a _ _ hr hg

#print axioms transfer
#print axioms sentence_transfer
end FirstOrderPacket
