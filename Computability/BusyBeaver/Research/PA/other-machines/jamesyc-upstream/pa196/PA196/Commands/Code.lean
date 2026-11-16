module
public import M6.Source.Cantor
@[expose] public section

/-!
Exact natural-number constructors and AX formulas from `paper/pa196.tex`, §3.
The universal constructor deliberately transposes the Cantor arguments.
No assertion about the literal Turing-machine program is made in this module.
-/
namespace PA196.Commands.Code
open M6.Source.Cantor

def I (a b : Nat) : Nat := 4 * pair a b
def M (a b : Nat) : Nat := 4 * pair a b + 1
def U (a b : Nat) : Nat := 4 * pair b a + 2
def E (a b : Nat) : Nat := 4 * pair a b + 3
def N (a : Nat) : Nat := I a 1
def conj (a b : Nat) : Nat := N (I a (N b))
def iffCode (a b : Nat) : Nat := conj (I a b) (I b a)
def ex (a b : Nat) : Nat := N (U a (N b))

/-- Paper head 1: existential elimination of a vacuous quantifier. -/
def head1 (D H : Nat) : Nat := I (ex D (U D H)) H
/-- Paper head 2: exchange of universal quantifiers. -/
def head2 (D A H : Nat) : Nat := I (U D (U A H)) (U A (U D H))
/-- Paper head 3, with its antecedents in the new order. -/
def head3 (D A H : Nat) : Nat := I (M H D) (I (E H A) (M A D))
/-- Paper head 4: membership rewriting in the second position. -/
def head4 (D A H : Nat) : Nat := I (E H D) (I (M A H) (M A D))
/-- Paper head 5: the mirrored primitive-equality witness. -/
def head5 (D H : Nat) : Nat := ex D (E H D)
/-- Paper head 6, with its antecedents in the new order. -/
def head6 (D A H : Nat) : Nat := I (U D A) (I (U D (I A H)) (U D H))
/-- The restricted propositional schema; the fourth argument obeys `u ≤ a`. -/
def rho8 (a b c u : Nat) : Nat := I (I (I c u) a) (I (I a c) (I b c))

def eqVac (a b c : Nat) : Nat := I (E a b) (U c (E a b))
def memVac (a b c : Nat) : Nat := I (M a b) (U c (M a b))
def point (_a b c : Nat) : Nat := I c (M c b)
def separation (a b c : Nat) : Nat :=
  U b (conj (I (M a b) (point a b c)) (I (M c b) c))
def separationTail (a b c : Nat) : Nat :=
  U c (I (separation a b c) (N (point a b c)))
/-- The old gate's unguarded formula, in the new numeric encoding. -/
def oldBundle (a b c : Nat) : Nat := N (I (memVac a b c) (separationTail a b c))
/-- The new equality-vacuity gate's unguarded formula. -/
def bundle (a b c : Nat) : Nat :=
  N (I (eqVac a b c) (I (memVac a b c) (separationTail a b c)))
def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle a b c

/-- The eight generated formulas, in top-to-bottom stack order after AX.
The saved incoming top is the ninth stack item and is added separately. -/
def heads (D H A d h : Nat) : List Nat :=
  [head6 D A H, head5 D H, head4 D A H, head3 D A H,
   head2 D A H, head1 D H, rho8 D A H d, U d h]

@[simp] theorem heads_length (D H A d h : Nat) : (heads D H A d h).length = 8 := rfl

theorem triangle_ge (n : Nat) : n ≤ triangle n := by
  induction n with
  | zero => omega
  | succ n ih => simp only [triangle]; omega

theorem left_le_pair (a b : Nat) : a ≤ pair a b := by
  have h := triangle_ge (a + b)
  simp only [pair]
  omega

theorem right_le_pair (a b : Nat) : b ≤ pair a b := by
  simp only [pair]
  omega

theorem left_le_I (a b : Nat) : a ≤ I a b := by
  have h := left_le_pair a b
  simp only [I]
  omega

theorem right_le_I (a b : Nat) : b ≤ I a b := by
  have h := right_le_pair a b
  simp only [I]
  omega

theorem left_lt_M (a b : Nat) : a < M a b := by
  have h := left_le_pair a b
  simp only [M]
  omega

theorem right_lt_M (a b : Nat) : b < M a b := by
  have h := right_le_pair a b
  simp only [M]
  omega

theorem left_lt_E (a b : Nat) : a < E a b := by
  have h := left_le_pair a b
  simp only [E]
  omega

theorem right_lt_E (a b : Nat) : b < E a b := by
  have h := right_le_pair a b
  simp only [E]
  omega

theorem left_lt_U (a b : Nat) : a < U a b := by
  have h := right_le_pair b a
  simp only [U]
  omega

theorem right_lt_U (a b : Nat) : b < U a b := by
  have h := left_le_pair b a
  simp only [U]
  omega

theorem lt_N (a : Nat) : a < N a := by
  have h := left_le_pair a 1
  have h' := right_le_pair a 1
  simp only [N, I]
  omega

@[simp] theorem I_ne_one (a b : Nat) : I a b ≠ 1 := by
  simp only [I]; omega
@[simp] theorem I_sum_ne_one (a b c d : Nat) : I a b + I c d ≠ 1 := by
  simp only [I]; omega
@[simp] theorem U_add_ne_one (a b t : Nat) : U a b + t ≠ 1 := by
  simp only [U]; omega
@[simp] theorem add_U_ne_one (a b t : Nat) : t + U a b ≠ 1 := by
  simp only [U]; omega
@[simp] theorem I_ne_U (a b c d : Nat) : I a b ≠ U c d := by
  simp only [I, U]; omega
@[simp] theorem I_zero_iff (a b : Nat) : I a b = 0 ↔ a = 0 ∧ b = 0 := by
  simp only [I, Nat.mul_eq_zero, Nat.reduceEqDiff, false_or, pair_zero_iff]
@[simp] theorem I_one_ne_zero (a : Nat) : I a 1 ≠ 0 := by simp
@[simp] theorem U_ne_zero (a b : Nat) : U a b ≠ 0 := by
  simp only [U]; omega
@[simp] theorem I_U_zero_ne_zero (a b : Nat) : I (U a b) 0 ≠ 0 := by simp
@[simp] theorem gate_ne_one (a b c : Nat) : gate a b c ≠ 1 := by
  unfold gate
  split
  · omega
  · exact I_ne_one _ _

theorem I_injective {a b c d : Nat} (h : I a b = I c d) : a = c ∧ b = d := by
  apply pair_injective
  simp only [I] at h
  omega
theorem U_injective {a b c d : Nat} (h : U a b = U c d) : a = c ∧ b = d := by
  have hp : pair b a = pair d c := by simp only [U] at h; omega
  have he := pair_injective hp
  exact ⟨he.2, he.1⟩

#print axioms left_lt_U
#print axioms U_injective
end PA196.Commands.Code
