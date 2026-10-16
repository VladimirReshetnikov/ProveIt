import Init

/-!
# Locally nameless opening, closing, and two-slot plugging

This finite-tree syntax matches the transformations in `binder_kernel.py`:
free variable names and bound De Bruijn indices are different constructors;
the unary `all` constructor has no name.  The traversal depth increases by
one under every `all`.

Opening replaces the bound index equal to the traversal depth by a free
name. Closing replaces one free name by that bound index. No index shift is
needed: opening's source-scope condition excludes any index greater than the
one removed, while bound indices smaller than the depth refer to inner
binders and remain unchanged.

The checked statements are about finite syntax functions. They do not certify
the Python DAG serialization, its witness verifier, the Hilbert proof checker,
a formula-code decoder, or a binary-machine compiler.
-/

namespace BinderSyntax

inductive Term where
  | free : Nat → Term
  | bound : Nat → Term
  deriving DecidableEq, Repr

inductive Form where
  | bot : Form
  | mem : Term → Term → Form
  | imp : Form → Form → Form
  | all : Form → Form
  deriving DecidableEq, Repr

def Term.scoped : Term → Nat → Prop
  | .free _, _ => True
  | .bound i, d => i < d

def Form.scoped : Form → Nat → Prop
  | .bot, _ => True
  | .mem x y, d => x.scoped d ∧ y.scoped d
  | .imp A B, d => A.scoped d ∧ B.scoped d
  | .all A, d => A.scoped (d + 1)

def Term.fresh (a : Nat) : Term → Prop
  | .free b => b ≠ a
  | .bound _ => True

def Form.fresh (a : Nat) : Form → Prop
  | .bot => True
  | .mem x y => x.fresh a ∧ y.fresh a
  | .imp A B => A.fresh a ∧ B.fresh a
  | .all A => A.fresh a

def Term.closeAt (a d : Nat) : Term → Term
  | .free b => if b = a then .bound d else .free b
  | .bound i => .bound i

def Term.openAt (a d : Nat) : Term → Term
  | .free b => .free b
  | .bound i => if i = d then .free a else .bound i

def Term.renameFree (a b : Nat) : Term → Term
  | .free c => if c = a then .free b else .free c
  | .bound i => .bound i

def Term.plugAt (i j d : Nat) : Term → Term
  | .free a =>
      if a = 0 then .bound (d + i)
      else if a = 1 then .bound (d + j)
      else .free a
  | .bound k => .bound k

def Form.closeAt (a : Nat) : Nat → Form → Form
  | _, .bot => .bot
  | d, .mem x y => .mem (x.closeAt a d) (y.closeAt a d)
  | d, .imp A B => .imp (A.closeAt a d) (B.closeAt a d)
  | d, .all A => .all (A.closeAt a (d + 1))

def Form.openAt (a : Nat) : Nat → Form → Form
  | _, .bot => .bot
  | d, .mem x y => .mem (x.openAt a d) (y.openAt a d)
  | d, .imp A B => .imp (A.openAt a d) (B.openAt a d)
  | d, .all A => .all (A.openAt a (d + 1))

def Form.renameFree (a b : Nat) : Form → Form
  | .bot => .bot
  | .mem x y => .mem (x.renameFree a b) (y.renameFree a b)
  | .imp A B => .imp (A.renameFree a b) (B.renameFree a b)
  | .all A => .all (A.renameFree a b)

def Form.plugAt (i j : Nat) : Nat → Form → Form
  | _, .bot => .bot
  | d, .mem x y => .mem (x.plugAt i j d) (y.plugAt i j d)
  | d, .imp A B => .imp (A.plugAt i j d) (B.plugAt i j d)
  | d, .all A => .all (A.plugAt i j (d + 1))

theorem Term.closeAt_scoped (a d : Nat) (t : Term) (h : t.scoped d) :
    (t.closeAt a d).scoped (d + 1) := by
  cases t with
  | free b =>
      by_cases hb : b = a
      · simp [Term.closeAt, Term.scoped, hb]
      · simp [Term.closeAt, Term.scoped, hb]
  | bound i =>
      exact Nat.lt_trans h (Nat.lt_succ_self d)

theorem Term.openAt_scoped (a d : Nat) (t : Term)
    (h : t.scoped (d + 1)) : (t.openAt a d).scoped d := by
  cases t with
  | free b => trivial
  | bound i =>
      by_cases hi : i = d
      · simp [Term.openAt, Term.scoped, hi]
      · simp only [Term.openAt, hi, if_false, Term.scoped]
        exact (Nat.lt_succ_iff_lt_or_eq.mp h).resolve_right hi

theorem Term.renameFree_scoped (a b d : Nat) (t : Term)
    (h : t.scoped d) : (t.renameFree a b).scoped d := by
  cases t with
  | free c =>
      by_cases hc : c = a <;> simp [Term.renameFree, Term.scoped, hc]
  | bound i => exact h

theorem Term.openAt_closeAt (a b d : Nat) (t : Term) (h : t.scoped d) :
    (t.closeAt a d).openAt b d = t.renameFree a b := by
  cases t with
  | free c =>
      by_cases hc : c = a <;> simp [Term.closeAt, Term.openAt, Term.renameFree, hc]
  | bound i =>
      have hi : i ≠ d := Nat.ne_of_lt h
      simp [Term.closeAt, Term.openAt, Term.renameFree, hi]

theorem Term.renameFree_self (a : Nat) (t : Term) : t.renameFree a a = t := by
  cases t with
  | free c =>
      by_cases hc : c = a
      · subst c; simp [Term.renameFree]
      · simp [Term.renameFree, hc]
  | bound i => rfl

theorem Term.closeAt_openAt (a d : Nat) (t : Term) (h : t.fresh a) :
    (t.openAt a d).closeAt a d = t := by
  cases t with
  | free b => simp [Term.openAt, Term.closeAt, Term.fresh] at h ⊢; exact h
  | bound i =>
      by_cases hi : i = d
      · subst i; simp [Term.openAt, Term.closeAt]
      · simp [Term.openAt, Term.closeAt, hi]

theorem Term.closeAt_eq_self_iff (a d : Nat) (t : Term) :
    t.closeAt a d = t ↔ t.fresh a := by
  cases t with
  | free b =>
      by_cases hb : b = a <;> simp [Term.closeAt, Term.fresh, hb]
  | bound i => simp [Term.closeAt, Term.fresh]

theorem Term.plugAt_scoped (i j d width : Nat) (t : Term)
    (hi : i < width) (hj : j < width) (h : t.scoped d) :
    (t.plugAt i j d).scoped (d + width) := by
  cases t with
  | free a =>
      by_cases ha0 : a = 0
      · simp only [Term.plugAt, ha0, if_true, Term.scoped]
        exact Nat.add_lt_add_left hi d
      · by_cases ha1 : a = 1
        · simp only [Term.plugAt, ha1, if_true, Term.scoped]
          exact Nat.add_lt_add_left hj d
        · simp [Term.plugAt, Term.scoped, ha0, ha1]
  | bound k =>
      exact Nat.lt_of_lt_of_le h (Nat.le_add_right d width)

theorem Form.closeAt_scoped (a : Nat) (A : Form) :
    ∀ d, A.scoped d → (A.closeAt a d).scoped (d + 1) := by
  induction A with
  | bot => intro d h; trivial
  | mem x y =>
      intro d h
      exact ⟨Term.closeAt_scoped a d x h.1, Term.closeAt_scoped a d y h.2⟩
  | imp A B ihA ihB =>
      intro d h
      exact ⟨ihA d h.1, ihB d h.2⟩
  | all A ihA =>
      intro d h
      exact ihA (d + 1) h

theorem Form.openAt_scoped (a : Nat) (A : Form) :
    ∀ d, A.scoped (d + 1) → (A.openAt a d).scoped d := by
  induction A with
  | bot => intro d h; trivial
  | mem x y =>
      intro d h
      exact ⟨Term.openAt_scoped a d x h.1, Term.openAt_scoped a d y h.2⟩
  | imp A B ihA ihB =>
      intro d h
      exact ⟨ihA d h.1, ihB d h.2⟩
  | all A ihA =>
      intro d h
      exact ihA (d + 1) h

theorem Form.renameFree_scoped (a b : Nat) (A : Form) :
    ∀ d, A.scoped d → (A.renameFree a b).scoped d := by
  induction A with
  | bot => intro d h; trivial
  | mem x y =>
      intro d h
      exact ⟨Term.renameFree_scoped a b d x h.1, Term.renameFree_scoped a b d y h.2⟩
  | imp A B ihA ihB =>
      intro d h
      exact ⟨ihA d h.1, ihB d h.2⟩
  | all A ihA =>
      intro d h
      exact ihA (d + 1) h

/-- Opening with any free name after closing is ordinary free-name substitution.
The replacement name may already occur freely in A; no freshness gate is used. -/
theorem Form.openAt_closeAt (a b : Nat) (A : Form) :
    ∀ d, A.scoped d → (A.closeAt a d).openAt b d = A.renameFree a b := by
  induction A with
  | bot => intro d h; rfl
  | mem x y =>
      intro d h
      simp only [Form.closeAt, Form.openAt, Form.renameFree,
        Term.openAt_closeAt a b d x h.1, Term.openAt_closeAt a b d y h.2]
  | imp A B ihA ihB =>
      intro d h
      simp only [Form.closeAt, Form.openAt, Form.renameFree, ihA d h.1, ihB d h.2]
  | all A ihA =>
      intro d h
      simp only [Form.closeAt, Form.openAt, Form.renameFree, ihA (d + 1) h]

theorem Form.renameFree_self (a : Nat) (A : Form) : A.renameFree a a = A := by
  induction A with
  | bot => rfl
  | mem x y => simp [Form.renameFree, Term.renameFree_self]
  | imp A B ihA ihB => simp [Form.renameFree, ihA, ihB]
  | all A ihA => simp [Form.renameFree, ihA]

/-- The requested exact inverse for every locally scoped finite formula. -/
theorem Form.openAt_closeAt_self (a : Nat) (A : Form) (d : Nat)
    (h : A.scoped d) : (A.closeAt a d).openAt a d = A := by
  rw [Form.openAt_closeAt a a A d h, Form.renameFree_self]

theorem Form.closeAt_openAt (a : Nat) (A : Form) :
    ∀ d, A.fresh a → (A.openAt a d).closeAt a d = A := by
  induction A with
  | bot => intro d h; rfl
  | mem x y =>
      intro d h
      simp only [Form.openAt, Form.closeAt,
        Term.closeAt_openAt a d x h.1, Term.closeAt_openAt a d y h.2]
  | imp A B ihA ihB =>
      intro d h
      simp only [Form.openAt, Form.closeAt, ihA d h.1, ihB d h.2]
  | all A ihA =>
      intro d h
      simp only [Form.openAt, Form.closeAt, ihA (d + 1) h]

/-- A closing witness with identical input and output is exactly a freshness
certificate. This is the side condition used by the proposed UD rule. -/
theorem Form.closeAt_eq_self_iff (a : Nat) (A : Form) :
    ∀ d, A.closeAt a d = A ↔ A.fresh a := by
  induction A with
  | bot => intro d; simp [Form.closeAt, Form.fresh]
  | mem x y =>
      intro d
      simp [Form.closeAt, Form.fresh, Term.closeAt_eq_self_iff]
  | imp A B ihA ihB =>
      intro d
      simp [Form.closeAt, Form.fresh, ihA d, ihB d]
  | all A ihA =>
      intro d
      simp [Form.closeAt, Form.fresh, ihA (d + 1)]

theorem Form.plugAt_scoped (i j width : Nat) (A : Form)
    (hi : i < width) (hj : j < width) :
    ∀ d, A.scoped d → (A.plugAt i j d).scoped (d + width) := by
  induction A with
  | bot => intro d h; trivial
  | mem x y =>
      intro d h
      exact ⟨Term.plugAt_scoped i j d width x hi hj h.1,
        Term.plugAt_scoped i j d width y hi hj h.2⟩
  | imp A B ihA ihB =>
      intro d h
      exact ⟨ihA d h.1, ihB d h.2⟩
  | all A ihA =>
      intro d h
      simpa only [Form.plugAt, Form.scoped, Nat.add_assoc,
        Nat.add_comm 1 width] using ihA (d + 1) h

#print axioms Form.openAt_closeAt_self
#print axioms Form.openAt_closeAt
#print axioms Form.closeAt_scoped
#print axioms Form.openAt_scoped
#print axioms Form.closeAt_openAt
#print axioms Form.closeAt_eq_self_iff
#print axioms Form.plugAt_scoped

end BinderSyntax
