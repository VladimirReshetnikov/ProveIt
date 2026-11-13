module
public import M6.Source.Cantor
@[expose] public section

/-! Exact numeric proof calculus for the equality-vacuity PA196 machine.

Only the six heads printed in `paper/pa196.tex`, its guarded gate, the
restricted propositional head, modus ponens and closed generalization are
constructors. In particular no equality symmetry, reflexivity, transitivity,
substitution rule or propositional-tautology oracle is a constructor.

These are finite external derivation trees. Their arithmetization and their
binding to the literal transition table are separate obligations.
-/
namespace PA196.Logic
open M6.Source.Cantor

def wim (a b : Nat) := 4 * pair a b
def wel (a b : Nat) := 4 * pair a b + 1
def wal (a b : Nat) := 4 * pair b a + 2
def weq (a b : Nat) := 4 * pair a b + 3
def wn (a : Nat) := wim a 1
def wa (a b : Nat) := wn (wim a (wn b))
def wex (a b : Nat) := wn (wal a (wn b))
def iffCode (a b : Nat) := wa (wim a b) (wim b a)

def head1 (d h : Nat) := wim (wex d (wal d h)) h
def head2 (d a h : Nat) := wim (wal d (wal a h)) (wal a (wal d h))
def head3 (h d a : Nat) := wim (wel h d) (wim (weq h a) (wel a d))
def head4 (h d a : Nat) := wim (weq h d) (wim (wel a h) (wel a d))
def head5 (d h : Nat) := wex d (weq h d)
def head6 (d a h : Nat) := wim (wal d a) (wim (wal d (wim a h)) (wal d h))
def rho8 (a b c u : Nat) := wim (wim (wim c u) a) (wim (wim a c) (wim b c))

def eqVac (a b c : Nat) := wim (weq a b) (wal c (weq a b))
def memVac (a b c : Nat) := wim (wel a b) (wal c (wel a b))
def point (_a b c : Nat) := wim c (wel c b)
def separation (a b c : Nat) :=
  wal b (wa (wim (wel a b) (point a b c)) (wim (wel c b) c))
def qGate (a b c : Nat) := wal c (wim (separation a b c) (wn (point a b c)))
def oldGate (a b c : Nat) := wn (wim (memVac a b c) (qGate a b c))
def bundle (a b c : Nat) := wn (wim (eqVac a b c) (wim (memVac a b c) (qGate a b c)))

attribute [local irreducible] head1 head2 head3 head4 head5 head6 rho8 bundle

inductive Derivation : Nat → Type where
  | mp {a b} : Derivation a → Derivation (wim a b) → Derivation b
  | all (a) {b} : Derivation b → Derivation (wal a b)
  | h1 (d h) : Derivation (head1 d h)
  | h2 (d a h) : Derivation (head2 d a h)
  | h3 (h d a) : Derivation (head3 h d a)
  | h4 (h d a) : Derivation (head4 h d a)
  | h5 (d h) : Derivation (head5 d h)
  | h6 (d a h) : Derivation (head6 d a h)
  | r8 (a b c u) : u ≤ a → Derivation (rho8 a b c u)
  | gate (a b c) : c ≠ a → c ≠ b → Derivation (bundle a b c)

theorem triangle_ge (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [triangle]; omega

theorem pair_bounds (a b : Nat) : a ≤ pair a b ∧ b ≤ pair a b := by
  have h := triangle_ge (a+b)
  simp only [pair]
  omega

theorem wim_bounds (a b : Nat) : a ≤ wim a b ∧ b ≤ wim a b := by
  have h := pair_bounds a b
  simp only [wim]
  omega

theorem wel_bounds (a b : Nat) : a < wel a b ∧ b < wel a b := by
  have h := pair_bounds a b
  simp only [wel]
  omega

theorem wn_strict (a : Nat) : a < wn a := by
  have h := pair_bounds a 1
  simp only [wn,wim]
  omega

end PA196.Logic
