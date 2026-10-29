/-
  SetTheory.PAHF.PACore

  First-order PA syntax (`Term`, `Formula`), its semantics, the `BProv` Hilbert
  calculus and the PA axiom set `Ax_s`. The `BProv_Ax_s_*` derived-rule library
  is in `PAHF.PASyntax`, which imports this module.
-/
import FirstOrder.Completeness
import PAHF.AckermannHFCore

namespace SetTheory

/-! ## Shallow PA models and the PA-in-HF round trip -/

namespace PA

universe u v

/-- A raw first-order arithmetic structure in the language `0, S, +, *`.
No arithmetic axioms are built in.  In particular, this is the semantic type
needed for models of finite PA fragments, which need not satisfy every
induction instance. -/
structure PreModel (α : Type u) where
  zero : α
  succ : α → α
  add : α → α → α
  mul : α → α → α

/-- A shallow model of full first-order Peano arithmetic.  It equips the raw
arithmetic operations with the six displayed non-induction laws and induction
for every Lean predicate.  The operations remain separate fields here so the
public positional constructor keeps its original shape. -/
structure Model (α : Type u) where
  zero : α
  succ : α → α
  add : α → α → α
  mul : α → α → α
  succ_injective : ∀ {a b}, succ a = succ b → a = b
  zero_not_succ : ∀ a, succ a ≠ zero
  induction :
    ∀ P : α → Prop, P zero → (∀ a, P a → P (succ a)) → ∀ a, P a
  add_zero : ∀ a, add a zero = a
  add_succ : ∀ a b, add a (succ b) = succ (add a b)
  mul_zero : ∀ a, mul a zero = zero
  mul_succ : ∀ a b, mul a (succ b) = add (mul a b) a

/-- Forget the PA laws and retain only the interpreted arithmetic language. -/
abbrev Model.toPreModel {α : Type u} (M : Model α) : PreModel α where
  zero := M.zero
  succ := M.succ
  add := M.add
  mul := M.mul

@[simp] theorem Model.toPreModel_zero {α : Type u} (M : Model α) :
    M.toPreModel.zero = M.zero := rfl

@[simp] theorem Model.toPreModel_succ {α : Type u} (M : Model α) :
    M.toPreModel.succ = M.succ := rfl

@[simp] theorem Model.toPreModel_add {α : Type u} (M : Model α) :
    M.toPreModel.add = M.add := rfl

@[simp] theorem Model.toPreModel_mul {α : Type u} (M : Model α) :
    M.toPreModel.mul = M.mul := rfl

instance { α : Type u } : Coe (Model α) (PreModel α) :=
  ⟨Model.toPreModel⟩

/-- Isomorphism of shallow PA models, preserving the arithmetic operations. -/
structure Iso {α : Type u} {β : Type v} (M : Model α) (N : Model β) where
  toFun : α → β
  invFun : β → α
  left_inv : ∀ a, invFun (toFun a) = a
  right_inv : ∀ b, toFun (invFun b) = b
  map_zero : toFun M.zero = N.zero
  map_succ : ∀ a, toFun (M.succ a) = N.succ (toFun a)
  map_add : ∀ a b, toFun (M.add a b) = N.add (toFun a) (toFun b)
  map_mul : ∀ a b, toFun (M.mul a b) = N.mul (toFun a) (toFun b)

/-- The standard model of PA on Lean's natural numbers. -/
def natModel : Model Nat where
  zero := 0
  succ := Nat.succ
  add := Nat.add
  mul := Nat.mul
  succ_injective := by
    intro a b h
    exact Nat.succ.inj h
  zero_not_succ := by
    intro a h
    exact Nat.succ_ne_zero a h
  induction := by
    intro P h0 hs a
    induction a with
    | zero => exact h0
    | succ n ih => exact hs n ih
  add_zero := Nat.add_zero
  add_succ := Nat.add_succ
  mul_zero := Nat.mul_zero
  mul_succ := Nat.mul_succ

/-! ### First-order PA syntax and semantics -/

inductive Term : Type
  | var : Nat → Term
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  deriving Repr, DecidableEq

inductive Formula : Type
  | eq : Term → Term → Formula
  | bot : Formula
  | imp : Formula → Formula → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | all : Formula → Formula
  | ex : Formula → Formula
  deriving Repr, DecidableEq

namespace Term

def rename (r : Nat → Nat) : Term → Term
  | var n => var (r n)
  | zero => zero
  | succ t => succ (rename r t)
  | add a b => add (rename r a) (rename r b)
  | mul a b => mul (rename r a) (rename r b)

def upSubst (σ : Nat → Term) : Nat → Term
  | 0 => var 0
  | n+1 => rename Nat.succ (σ n)

def subst (σ : Nat → Term) : Term → Term
  | var n => σ n
  | zero => zero
  | succ t => succ (subst σ t)
  | add a b => add (subst σ a) (subst σ b)
  | mul a b => mul (subst σ a) (subst σ b)

def eval {α : Type u} (M : PreModel α) (e : Nat → α) : Term → α
  | var n => e n
  | zero => M.zero
  | succ t => M.succ (eval M e t)
  | add a b => M.add (eval M e a) (eval M e b)
  | mul a b => M.mul (eval M e a) (eval M e b)

def numeral : Nat → Term
  | 0 => zero
  | n+1 => succ (numeral n)

/-- The PA term obtained by adding a fixed left term to a standard numeral on
the right, unfolded using the PA recursion equation for addition. -/
def addRightNumeral (t : Term) : Nat → Term
  | 0 => t
  | n+1 => succ (addRightNumeral t n)

/-- The PA term obtained by multiplying a fixed left term by a standard numeral
on the right, unfolded using the PA recursion equation for multiplication. -/
def mulRightNumeral (t : Term) : Nat → Term
  | 0 => zero
  | n+1 => add (mulRightNumeral t n) t

def numeralValue {α : Type u} (M : PreModel α) : Nat → α
  | 0 => M.zero
  | n+1 => M.succ (numeralValue M n)

@[simp] theorem rename_numeral (r : Nat → Nat) :
    ∀ n, rename r (numeral n) = numeral n
  | 0 => rfl
  | n+1 => by simp [numeral, rename, rename_numeral r n]

@[simp] theorem subst_numeral (σ : Nat → Term) :
    ∀ n, subst σ (numeral n) = numeral n
  | 0 => rfl
  | n+1 => by simp [numeral, subst, subst_numeral σ n]

@[simp] theorem numeral_succ (n : Nat) :
    numeral (n + 1) = succ (numeral n) := by
  rfl

theorem addRightNumeral_numeral (m n : Nat) :
    addRightNumeral (numeral m) n = numeral (m + n) := by
  induction n with
  | zero =>
      simp [addRightNumeral]
  | succ n ih =>
      rw [Nat.add_succ]
      simp [addRightNumeral, numeral, ih]

theorem eval_numeral {α : Type u} (M : PreModel α) (e : Nat → α) :
    ∀ n, eval M e (numeral n) = numeralValue M n
  | 0 => rfl
  | n+1 => by
      simp only [numeral, numeralValue, eval, eval_numeral M e n]

theorem numeralValue_natModel : ∀ n, numeralValue natModel n = n
  | 0 => rfl
  | n+1 => by
      change Nat.succ (numeralValue natModel n) = n + 1
      rw [numeralValue_natModel n]

theorem eval_numeral_natModel (e : Nat → Nat) (n : Nat) :
    eval natModel e (numeral n) = n := by
  rw [eval_numeral, numeralValue_natModel]

def bound : Term → Nat
  | var n => n + 1
  | zero => 0
  | succ t => bound t
  | add a b => bound a + bound b
  | mul a b => bound a + bound b

def Free : Nat → Term → Prop
  | n, var k => n = k
  | _, zero => False
  | n, succ t => Free n t
  | n, add a b => Free n a ∨ Free n b
  | n, mul a b => Free n a ∨ Free n b

theorem free_lt_bound (t : Term) : ∀ n, Free n t → n < bound t := by
  induction t with
  | var k =>
      intro n hn
      simp only [Free] at hn
      subst hn
      simp [bound]
  | zero =>
      intro n hn
      cases hn
  | succ t ih =>
      intro n hn
      exact ih n hn
  | add a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega
  | mul a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega

theorem eval_ext {α : Type u} (M : PreModel α) (t : Term)
    {e e' : Nat → α} (h : ∀ n, e n = e' n) :
    eval M e t = eval M e' t := by
  induction t with
  | var n => exact h n
  | zero => rfl
  | succ t ih => simp only [eval, ih]
  | add a b iha ihb => simp only [eval, iha, ihb]
  | mul a b iha ihb => simp only [eval, iha, ihb]

theorem eval_ext_free {α : Type u} (M : PreModel α) (t : Term)
    {e e' : Nat → α} (h : ∀ n, Free n t → e n = e' n) :
    eval M e t = eval M e' t := by
  induction t generalizing e e' with
  | var n => exact h n rfl
  | zero => rfl
  | succ t ih =>
      simp only [eval]
      rw [ih h]
  | add a b iha ihb =>
      simp only [eval]
      rw [iha (fun n hn => h n (Or.inl hn)),
        ihb (fun n hn => h n (Or.inr hn))]
  | mul a b iha ihb =>
      simp only [eval]
      rw [iha (fun n hn => h n (Or.inl hn)),
        ihb (fun n hn => h n (Or.inr hn))]

theorem eval_rename {α : Type u} (M : PreModel α) (t : Term)
    (r : Nat → Nat) (e : Nat → α) :
    eval M e (rename r t) = eval M (fun n => e (r n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp only [rename, eval, ih]
  | add a b iha ihb => simp only [rename, eval, iha, ihb]
  | mul a b iha ihb => simp only [rename, eval, iha, ihb]

theorem rename_ext (t : Term) (r r' : Nat → Nat) (h : ∀ n, r n = r' n) :
    rename r t = rename r' t := by
  induction t with
  | var n => simp [rename, h n]
  | zero => rfl
  | succ t ih => simp [rename, ih]
  | add a b iha ihb => simp [rename, iha, ihb]
  | mul a b iha ihb => simp [rename, iha, ihb]

theorem rename_ext_free (t : Term) :
    ∀ r r', (∀ n, Free n t → r n = r' n) → rename r t = rename r' t := by
  induction t with
  | var n =>
      intro r r' h
      simp [rename, h n rfl]
  | zero =>
      intro r r' h
      rfl
  | succ t ih =>
      intro r r' h
      simp [rename, ih r r' h]
  | add a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]
  | mul a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]

theorem rename_id (t : Term) : rename (fun n : Nat => n) t = t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [rename, ih]
  | add a b iha ihb => simp [rename, iha, ihb]
  | mul a b iha ihb => simp [rename, iha, ihb]

theorem rename_comp (t : Term) (r r' : Nat → Nat) :
    rename r (rename r' t) = rename (fun n => r (r' n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [rename, ih]
  | add a b iha ihb => simp [rename, iha, ihb]
  | mul a b iha ihb => simp [rename, iha, ihb]

theorem eval_upSubst {α : Type u} (M : PreModel α) (σ : Nat → Term)
    (e : Nat → α) (d : α) (n : Nat) :
    eval M (SetTheory.scons d e) (upSubst σ n) =
      SetTheory.scons d (fun k => eval M e (σ k)) n := by
  cases n with
  | zero => rfl
  | succ n =>
      simp only [upSubst, SetTheory.scons]
      rw [eval_rename]
      rfl

theorem eval_subst {α : Type u} (M : PreModel α) (t : Term)
    (σ : Nat → Term) (e : Nat → α) :
    eval M e (subst σ t) = eval M (fun n => eval M e (σ n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp only [subst, eval, ih]
  | add a b iha ihb => simp only [subst, eval, iha, ihb]
  | mul a b iha ihb => simp only [subst, eval, iha, ihb]

theorem subst_ext (t : Term) (σ τ : Nat → Term) (h : ∀ n, σ n = τ n) :
    subst σ t = subst τ t := by
  induction t with
  | var n => exact h n
  | zero => rfl
  | succ t ih => simp [subst, ih]
  | add a b iha ihb => simp [subst, iha, ihb]
  | mul a b iha ihb => simp [subst, iha, ihb]

theorem subst_rename (t : Term) (σ : Nat → Term) (r : Nat → Nat) :
    subst σ (rename r t) = subst (fun n => σ (r n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [rename, subst, ih]
  | add a b iha ihb => simp [rename, subst, iha, ihb]
  | mul a b iha ihb => simp [rename, subst, iha, ihb]

theorem rename_subst (t : Term) (r : Nat → Nat) (σ : Nat → Term) :
    rename r (subst σ t) =
      subst (fun n => rename r (σ n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [rename, subst, ih]
  | add a b iha ihb => simp [rename, subst, iha, ihb]
  | mul a b iha ihb => simp [rename, subst, iha, ihb]

theorem subst_comp (t : Term) (σ τ : Nat → Term) :
    subst τ (subst σ t) =
      subst (fun n => subst τ (σ n)) t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [subst, ih]
  | add a b iha ihb => simp [subst, iha, ihb]
  | mul a b iha ihb => simp [subst, iha, ihb]

theorem subst_rename_succ_up (t : Term) (σ : Nat → Term) :
    subst (upSubst σ) (rename Nat.succ t) =
      rename Nat.succ (subst σ t) := by
  rw [subst_rename, rename_subst]
  exact subst_ext t _ _ (fun n => by rfl)

theorem upSubst_comp (σ τ : Nat → Term) :
    upSubst (fun n => subst τ (σ n)) =
      fun n => subst (upSubst τ) (upSubst σ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp [upSubst, subst_rename_succ_up]

theorem subst_ext_free (t : Term) :
    ∀ σ τ, (∀ n, Free n t → σ n = τ n) → subst σ t = subst τ t := by
  induction t with
  | var n =>
      intro σ τ h
      exact h n rfl
  | zero =>
      intro σ τ h
      rfl
  | succ t ih =>
      intro σ τ h
      simp [subst, ih σ τ h]
  | add a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]
  | mul a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]

theorem subst_id (t : Term) :
    subst (fun n => var n) t = t := by
  induction t with
  | var n => rfl
  | zero => rfl
  | succ t ih => simp [subst, ih]
  | add a b iha ihb => simp [subst, iha, ihb]
  | mul a b iha ihb => simp [subst, iha, ihb]

end Term

namespace Formula

def iffForm (a b : Formula) : Formula := and (imp a b) (imp b a)

def rename (r : Nat → Nat) : Formula → Formula
  | eq a b => eq (Term.rename r a) (Term.rename r b)
  | bot => bot
  | imp a b => imp (rename r a) (rename r b)
  | and a b => and (rename r a) (rename r b)
  | or a b => or (rename r a) (rename r b)
  | all a => all (rename (SetTheory.up r) a)
  | ex a => ex (rename (SetTheory.up r) a)

def subst (σ : Nat → Term) : Formula → Formula
  | eq a b => eq (Term.subst σ a) (Term.subst σ b)
  | bot => bot
  | imp a b => imp (subst σ a) (subst σ b)
  | and a b => and (subst σ a) (subst σ b)
  | or a b => or (subst σ a) (subst σ b)
  | all a => all (subst (Term.upSubst σ) a)
  | ex a => ex (subst (Term.upSubst σ) a)

def Sat {α : Type u} (M : PreModel α) : (Nat → α) → Formula → Prop
  | e, eq a b => Term.eval M e a = Term.eval M e b
  | _, bot => False
  | e, imp a b => Sat M e a → Sat M e b
  | e, and a b => Sat M e a ∧ Sat M e b
  | e, or a b => Sat M e a ∨ Sat M e b
  | e, all a => ∀ d, Sat M (SetTheory.scons d e) a
  | e, ex a => ∃ d, Sat M (SetTheory.scons d e) a

theorem Sat_iffForm {α : Type u} (M : PreModel α) (e : Nat → α) (a b : Formula) :
    Sat M e (iffForm a b) ↔ (Sat M e a ↔ Sat M e b) := by
  constructor
  · intro h
    exact ⟨h.1, h.2⟩
  · intro h
    exact ⟨h.1, h.2⟩

def bound : Formula → Nat
  | eq a b => Term.bound a + Term.bound b
  | bot => 0
  | imp a b => bound a + bound b
  | and a b => bound a + bound b
  | or a b => bound a + bound b
  | all a => bound a
  | ex a => bound a

def Free : Nat → Formula → Prop
  | n, eq a b => Term.Free n a ∨ Term.Free n b
  | _, bot => False
  | n, imp a b => Free n a ∨ Free n b
  | n, and a b => Free n a ∨ Free n b
  | n, or a b => Free n a ∨ Free n b
  | n, all a => Free (n+1) a
  | n, ex a => Free (n+1) a

def Sentence (phi : Formula) : Prop := ∀ n, ¬ Free n phi

def Sentences (B : Formula → Prop) : Prop := ∀ phi, B phi → Sentence phi

theorem free_lt_bound (phi : Formula) : ∀ n, Free n phi → n < bound phi := by
  induction phi with
  | eq a b =>
      intro n hn
      rcases hn with hn | hn
      · have := Term.free_lt_bound a n hn
        simp [bound]
        omega
      · have := Term.free_lt_bound b n hn
        simp [bound]
        omega
  | bot =>
      intro n hn
      cases hn
  | imp a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega
  | and a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega
  | or a b iha ihb =>
      intro n hn
      rcases hn with hn | hn
      · have := iha n hn
        simp [bound]
        omega
      · have := ihb n hn
        simp [bound]
        omega
  | all a ih =>
      intro n hn
      have := ih (n+1) hn
      simp [bound]
      omega
  | ex a ih =>
      intro n hn
      have := ih (n+1) hn
      simp [bound]
      omega

def closeN : Nat → Formula → Formula
  | 0, phi => phi
  | n+1, phi => closeN n (all phi)

def sealPA (phi : Formula) : Formula := closeN (bound phi) phi

theorem Free_closeN : ∀ (k : Nat) (phi : Formula) (n : Nat),
    Free n (closeN k phi) → Free (k + n) phi := by
  intro k
  induction k with
  | zero =>
      intro phi n h
      rw [Nat.zero_add]
      exact h
  | succ k ih =>
      intro phi n h
      have h1 : Free (k + n) (all phi) := ih (all phi) n h
      have h2 : Free (k + n + 1) phi := h1
      have harg : k + 1 + n = k + n + 1 := by omega
      rw [harg]
      exact h2

theorem sealPA_sentence (phi : Formula) : Sentence (sealPA phi) := by
  intro n h
  have h1 := Free_closeN (bound phi) phi n h
  have h2 := free_lt_bound phi _ h1
  omega

theorem Sat_ext {α : Type u} (M : PreModel α) (phi : Formula)
    {e e' : Nat → α} (h : ∀ n, e n = e' n) :
    Sat M e phi ↔ Sat M e' phi := by
  induction phi generalizing e e' with
  | eq a b =>
      simp only [Sat]
      rw [Term.eval_ext M a h, Term.eval_ext M b h]
  | bot => exact Iff.rfl
  | imp a b iha ihb =>
      simp only [Sat]
      exact ⟨fun hab ha => (ihb h).mp (hab ((iha h).mpr ha)),
             fun hab ha => (ihb h).mpr (hab ((iha h).mp ha))⟩
  | and a b iha ihb =>
      simp only [Sat]
      exact and_congr (iha h) (ihb h)
  | or a b iha ihb =>
      simp only [Sat]
      exact or_congr (iha h) (ihb h)
  | all a ih =>
      simp only [Sat]
      constructor
      · intro hall d
        exact (ih (fun n => by cases n <;> simp [SetTheory.scons, h])).mp (hall d)
      · intro hall d
        exact (ih (fun n => by cases n <;> simp [SetTheory.scons, h])).mpr (hall d)
  | ex a ih =>
      simp only [Sat]
      constructor
      · intro ⟨d, hd⟩
        exact ⟨d, (ih (fun n => by cases n <;> simp [SetTheory.scons, h])).mp hd⟩
      · intro ⟨d, hd⟩
        exact ⟨d, (ih (fun n => by cases n <;> simp [SetTheory.scons, h])).mpr hd⟩

theorem Sat_ext_free {α : Type u} (M : PreModel α) (phi : Formula)
    {e e' : Nat → α} (h : ∀ n, Free n phi → e n = e' n) :
    Sat M e phi ↔ Sat M e' phi := by
  induction phi generalizing e e' with
  | eq a b =>
      simp only [Sat]
      rw [Term.eval_ext_free M a (fun n hn => h n (Or.inl hn)),
        Term.eval_ext_free M b (fun n hn => h n (Or.inr hn))]
  | bot => exact Iff.rfl
  | imp a b iha ihb =>
      simp only [Sat]
      have hleft : ∀ n, Free n a → e n = e' n :=
        fun n hn => h n (Or.inl hn)
      have hright : ∀ n, Free n b → e n = e' n :=
        fun n hn => h n (Or.inr hn)
      exact ⟨
        fun hab ha => (ihb hright).mp (hab ((iha hleft).mpr ha)),
        fun hab ha => (ihb hright).mpr (hab ((iha hleft).mp ha))⟩
  | and a b iha ihb =>
      simp only [Sat]
      exact and_congr
        (iha (fun n hn => h n (Or.inl hn)))
        (ihb (fun n hn => h n (Or.inr hn)))
  | or a b iha ihb =>
      simp only [Sat]
      exact or_congr
        (iha (fun n hn => h n (Or.inl hn)))
        (ihb (fun n hn => h n (Or.inr hn)))
  | all a ih =>
      simp only [Sat]
      constructor
      · intro hall d
        apply (ih (e := SetTheory.scons d e) (e' := SetTheory.scons d e')
          (fun n hn => by
            cases n with
            | zero => rfl
            | succ k => exact h k hn)).mp
        exact hall d
      · intro hall d
        apply (ih (e := SetTheory.scons d e) (e' := SetTheory.scons d e')
          (fun n hn => by
            cases n with
            | zero => rfl
            | succ k => exact h k hn)).mpr
        exact hall d
  | ex a ih =>
      simp only [Sat]
      constructor
      · intro hex
        rcases hex with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        apply (ih (e := SetTheory.scons d e) (e' := SetTheory.scons d e')
          (fun n hn => by
            cases n with
            | zero => rfl
            | succ k => exact h k hn)).mp
        exact hd
      · intro hex
        rcases hex with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        apply (ih (e := SetTheory.scons d e) (e' := SetTheory.scons d e')
          (fun n hn => by
            cases n with
            | zero => rfl
            | succ k => exact h k hn)).mpr
        exact hd

theorem Sat_subst {α : Type u} (M : PreModel α) (phi : Formula)
    (σ : Nat → Term) (e : Nat → α) :
    Sat M e (subst σ phi) ↔
      Sat M (fun n => Term.eval M e (σ n)) phi := by
  induction phi generalizing e σ with
  | eq a b =>
      simp only [subst, Sat, Term.eval_subst]
  | bot => exact Iff.rfl
  | imp a b iha ihb =>
      simp only [subst, Sat]
      exact ⟨fun hab ha => (ihb σ e).mp (hab ((iha σ e).mpr ha)),
             fun hab ha => (ihb σ e).mpr (hab ((iha σ e).mp ha))⟩
  | and a b iha ihb =>
      simp only [subst, Sat]
      exact and_congr (iha σ e) (ihb σ e)
  | or a b iha ihb =>
      simp only [subst, Sat]
      exact or_congr (iha σ e) (ihb σ e)
  | all a ih =>
      simp only [subst, Sat]
      constructor
      · intro hall d
        have h1 := (ih (Term.upSubst σ) (SetTheory.scons d e)).mp (hall d)
        exact (Sat_ext M a (Term.eval_upSubst M σ e d)).mp h1
      · intro hall d
        have h1 : Sat M (fun n => Term.eval M (SetTheory.scons d e) (Term.upSubst σ n)) a :=
          (Sat_ext M a (Term.eval_upSubst M σ e d)).mpr (hall d)
        exact (ih (Term.upSubst σ) (SetTheory.scons d e)).mpr h1
  | ex a ih =>
      simp only [subst, Sat]
      constructor
      · intro ⟨d, hd⟩
        have h1 := (ih (Term.upSubst σ) (SetTheory.scons d e)).mp hd
        exact ⟨d, (Sat_ext M a (Term.eval_upSubst M σ e d)).mp h1⟩
      · intro ⟨d, hd⟩
        have h1 : Sat M (fun n => Term.eval M (SetTheory.scons d e) (Term.upSubst σ n)) a :=
          (Sat_ext M a (Term.eval_upSubst M σ e d)).mpr hd
        exact ⟨d, (ih (Term.upSubst σ) (SetTheory.scons d e)).mpr h1⟩

theorem closeN_valid {α : Type u} (M : PreModel α) (k : Nat) :
    ∀ phi : Formula, (∀ e : Nat → α, Sat M e (closeN k phi)) ↔
      (∀ e, Sat M e phi) := by
  induction k with
  | zero =>
      intro phi
      exact Iff.rfl
  | succ k ih =>
      intro phi
      show (∀ e, Sat M e (closeN k (all phi))) ↔ _
      rw [ih (all phi)]
      constructor
      · intro h e'
        have pf : ∀ n, SetTheory.scons (e' 0) (fun n => e' (n+1)) n = e' n := by
          intro n
          cases n <;> rfl
        exact (Sat_ext M phi pf).mp (h (fun n => e' (n+1)) (e' 0))
      · intro h e d
        exact h _

theorem seal_valid {α : Type u} (M : PreModel α) (phi : Formula) :
    (∀ e : Nat → α, Sat M e (sealPA phi)) ↔ (∀ e, Sat M e phi) :=
  closeN_valid M (bound phi) phi

/-! ### PA proof calculus -/

def instTerm (t : Term) : Nat → Term
  | 0 => t
  | n+1 => Term.var n

/-- PA-term substitution by variables is just PA-term renaming. -/
theorem term_subst_var_rename (t : Term) (r : Nat → Nat) :
    Term.subst (fun n => Term.var (r n)) t = Term.rename r t := by
  induction t with
  | var n =>
      rfl
  | zero =>
      rfl
  | succ t ih =>
      simp [Term.subst, Term.rename, ih]
  | add a b iha ihb =>
      simp [Term.subst, Term.rename, iha, ihb]
  | mul a b iha ihb =>
      simp [Term.subst, Term.rename, iha, ihb]

/-- Substituting PA de Bruijn 0 by a variable is just PA-term renaming by the
corresponding variable-instantiation map. -/
theorem term_subst_instTerm_var (t : Term) (k : Nat) :
    Term.subst (instTerm (Term.var k)) t = Term.rename (SetTheory.inst k) t := by
  rw [← term_subst_var_rename t (SetTheory.inst k)]
  exact Term.subst_ext t _ _ (fun n => by cases n <;> rfl)

theorem Sat_rename {α : Type u} (M : PreModel α) (phi : Formula)
    (r : Nat → Nat) (e : Nat → α) :
    Sat M e (rename r phi) ↔ Sat M (fun n => e (r n)) phi := by
  induction phi generalizing r e with
  | eq a b =>
      simp only [rename, Sat, Term.eval_rename]
  | bot =>
      exact Iff.rfl
  | imp a b iha ihb =>
      simp only [rename, Sat]
      exact ⟨fun hab ha => (ihb r e).mp (hab ((iha r e).mpr ha)),
        fun hab ha => (ihb r e).mpr (hab ((iha r e).mp ha))⟩
  | and a b iha ihb =>
      simp only [rename, Sat]
      exact and_congr (iha r e) (ihb r e)
  | or a b iha ihb =>
      simp only [rename, Sat]
      exact or_congr (iha r e) (ihb r e)
  | all a ih =>
      simp only [rename, Sat]
      constructor
      · intro h d
        have hbody := (ih (SetTheory.up r) (SetTheory.scons d e)).mp (h d)
        exact (Sat_ext M a (fun n => by cases n <;> rfl)).mp hbody
      · intro h d
        have hbody : Sat M (fun n => SetTheory.scons d e (SetTheory.up r n)) a :=
          (Sat_ext M a (fun n => by cases n <;> rfl)).mpr (h d)
        exact (ih (SetTheory.up r) (SetTheory.scons d e)).mpr hbody
  | ex a ih =>
      simp only [rename, Sat]
      constructor
      · intro ⟨d, hd⟩
        have hbody := (ih (SetTheory.up r) (SetTheory.scons d e)).mp hd
        exact ⟨d, (Sat_ext M a (fun n => by cases n <;> rfl)).mp hbody⟩
      · intro ⟨d, hd⟩
        have hbody : Sat M (fun n => SetTheory.scons d e (SetTheory.up r n)) a :=
          (Sat_ext M a (fun n => by cases n <;> rfl)).mpr hd
        exact ⟨d, (ih (SetTheory.up r) (SetTheory.scons d e)).mpr hbody⟩

theorem Sat_rename_succ {α : Type u} (M : PreModel α) (phi : Formula)
    (e : Nat → α) (d : α) :
    Sat M (SetTheory.scons d e) (rename Nat.succ phi) ↔ Sat M e phi := by
  rw [Sat_rename]
  exact Sat_ext M phi (fun n => rfl)

theorem rename_ext (phi : Formula) (r r' : Nat → Nat) (h : ∀ n, r n = r' n) :
    rename r phi = rename r' phi := by
  induction phi generalizing r r' with
  | eq a b =>
      simp [rename, Term.rename_ext a r r' h, Term.rename_ext b r r' h]
  | bot => rfl
  | imp a b iha ihb => simp [rename, iha r r' h, ihb r r' h]
  | and a b iha ihb => simp [rename, iha r r' h, ihb r r' h]
  | or a b iha ihb => simp [rename, iha r r' h, ihb r r' h]
  | all a ih =>
      simp [rename, ih (SetTheory.up r) (SetTheory.up r') (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [SetTheory.up, h n])]
  | ex a ih =>
      simp [rename, ih (SetTheory.up r) (SetTheory.up r') (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [SetTheory.up, h n])]

theorem rename_ext_free (phi : Formula) :
    ∀ r r', (∀ n, Free n phi → r n = r' n) →
      rename r phi = rename r' phi := by
  induction phi with
  | eq a b =>
      intro r r' h
      simp [rename,
        Term.rename_ext_free a r r' (fun n hn => h n (Or.inl hn)),
        Term.rename_ext_free b r r' (fun n hn => h n (Or.inr hn))]
  | bot =>
      intro r r' h
      rfl
  | imp a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]
  | and a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]
  | or a b iha ihb =>
      intro r r' h
      simp [rename, iha r r' (fun n hn => h n (Or.inl hn)),
        ihb r r' (fun n hn => h n (Or.inr hn))]
  | all a ih =>
      intro r r' h
      simp [rename, ih (SetTheory.up r) (SetTheory.up r') (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [SetTheory.up, h n hn])]
  | ex a ih =>
      intro r r' h
      simp [rename, ih (SetTheory.up r) (SetTheory.up r') (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [SetTheory.up, h n hn])]

theorem rename_id (phi : Formula) : rename (fun n : Nat => n) phi = phi := by
  induction phi with
  | eq a b =>
      simp [rename, Term.rename_id]
  | bot =>
      rfl
  | imp a b iha ihb =>
      simp [rename, iha, ihb]
  | and a b iha ihb =>
      simp [rename, iha, ihb]
  | or a b iha ihb =>
      simp [rename, iha, ihb]
  | all a ih =>
      simp only [rename]
      apply congrArg all
      calc
        rename (SetTheory.up (fun n : Nat => n)) a =
            rename (fun n : Nat => n) a := by
          apply rename_ext
          intro n
          cases n <;> rfl
        _ = a := ih
  | ex a ih =>
      simp only [rename]
      apply congrArg ex
      calc
        rename (SetTheory.up (fun n : Nat => n)) a =
            rename (fun n : Nat => n) a := by
          apply rename_ext
          intro n
          cases n <;> rfl
        _ = a := ih

theorem rename_eq_of_sentence {phi : Formula} (hphi : Sentence phi)
    (r : Nat → Nat) : rename r phi = phi := by
  calc
    rename r phi = rename (fun n : Nat => n) phi := by
      apply rename_ext_free
      intro n hn
      exact False.elim (hphi n hn)
    _ = phi := rename_id phi

theorem rename_comp (phi : Formula) (r r' : Nat → Nat) :
    rename r (rename r' phi) = rename (fun n => r (r' n)) phi := by
  induction phi generalizing r r' with
  | eq a b =>
      simp [rename, Term.rename_comp]
  | bot => rfl
  | imp a b iha ihb => simp [rename, iha, ihb]
  | and a b iha ihb => simp [rename, iha, ihb]
  | or a b iha ihb => simp [rename, iha, ihb]
  | all a ih =>
      simp only [rename]
      rw [ih]
      exact congrArg all (rename_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n => rfl))
  | ex a ih =>
      simp only [rename]
      rw [ih]
      exact congrArg ex (rename_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n => rfl))

theorem rename_up_succ (phi : Formula) (r : Nat → Nat) :
    rename (SetTheory.up r) (rename Nat.succ phi) =
      rename Nat.succ (rename r phi) := by
  rw [rename_comp, rename_comp]
  exact rename_ext phi _ _ (fun n => by rfl)

theorem subst_ext (phi : Formula) (σ τ : Nat → Term) (h : ∀ n, σ n = τ n) :
    subst σ phi = subst τ phi := by
  induction phi generalizing σ τ with
  | eq a b =>
      simp [subst, Term.subst_ext a σ τ h, Term.subst_ext b σ τ h]
  | bot => rfl
  | imp a b iha ihb => simp [subst, iha σ τ h, ihb σ τ h]
  | and a b iha ihb => simp [subst, iha σ τ h, ihb σ τ h]
  | or a b iha ihb => simp [subst, iha σ τ h, ihb σ τ h]
  | all a ih =>
      simp [subst, ih (Term.upSubst σ) (Term.upSubst τ) (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [Term.upSubst, h n])]
  | ex a ih =>
      simp [subst, ih (Term.upSubst σ) (Term.upSubst τ) (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [Term.upSubst, h n])]

theorem subst_rename (phi : Formula) (σ : Nat → Term) (r : Nat → Nat) :
    subst σ (rename r phi) = subst (fun n => σ (r n)) phi := by
  induction phi generalizing σ r with
  | eq a b =>
      simp [rename, subst, Term.subst_rename]
  | bot => rfl
  | imp a b iha ihb => simp [rename, subst, iha, ihb]
  | and a b iha ihb => simp [rename, subst, iha, ihb]
  | or a b iha ihb => simp [rename, subst, iha, ihb]
  | all a ih =>
      simp only [rename, subst]
      rw [ih]
      exact congrArg all (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n => rfl))
  | ex a ih =>
      simp only [rename, subst]
      rw [ih]
      exact congrArg ex (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n => rfl))

theorem rename_subst (phi : Formula) (r : Nat → Nat) (σ : Nat → Term) :
    rename r (subst σ phi) =
      subst (fun n => Term.rename r (σ n)) phi := by
  induction phi generalizing r σ with
  | eq a b =>
      simp [rename, subst, Term.rename_subst]
  | bot => rfl
  | imp a b iha ihb => simp [rename, subst, iha, ihb]
  | and a b iha ihb => simp [rename, subst, iha, ihb]
  | or a b iha ihb => simp [rename, subst, iha, ihb]
  | all a ih =>
      simp only [rename, subst]
      rw [ih]
      exact congrArg all (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst]
            rw [Term.rename_comp, Term.rename_comp]
            exact Term.rename_ext (σ n) _ _ (fun k => rfl)))
  | ex a ih =>
      simp only [rename, subst]
      rw [ih]
      exact congrArg ex (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst]
            rw [Term.rename_comp, Term.rename_comp]
            exact Term.rename_ext (σ n) _ _ (fun k => rfl)))

theorem subst_comp (phi : Formula) (σ τ : Nat → Term) :
    subst τ (subst σ phi) =
      subst (fun n => Term.subst τ (σ n)) phi := by
  induction phi generalizing σ τ with
  | eq a b =>
      simp [subst, Term.subst_comp]
  | bot =>
      rfl
  | imp a b iha ihb =>
      simp [subst, iha, ihb]
  | and a b iha ihb =>
      simp [subst, iha, ihb]
  | or a b iha ihb =>
      simp [subst, iha, ihb]
  | all a ih =>
      simp only [subst]
      rw [ih]
      exact congrArg all (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst, Term.subst_rename_succ_up]))
  | ex a ih =>
      simp only [subst]
      rw [ih]
      exact congrArg ex (subst_ext a _ _ (fun n => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst, Term.subst_rename_succ_up]))

theorem subst_rename_succ_up (phi : Formula) (σ : Nat → Term) :
    subst (Term.upSubst σ) (rename Nat.succ phi) =
      rename Nat.succ (subst σ phi) := by
  rw [subst_rename, rename_subst]
  exact subst_ext phi _ _ (fun n => by rfl)

theorem subst_ext_free (phi : Formula) :
    ∀ σ τ, (∀ n, Free n phi → σ n = τ n) → subst σ phi = subst τ phi := by
  induction phi with
  | eq a b =>
      intro σ τ h
      simp [subst,
        Term.subst_ext_free a σ τ (fun n hn => h n (Or.inl hn)),
        Term.subst_ext_free b σ τ (fun n hn => h n (Or.inr hn))]
  | bot =>
      intro σ τ h
      rfl
  | imp a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]
  | and a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]
  | or a b iha ihb =>
      intro σ τ h
      simp [subst, iha σ τ (fun n hn => h n (Or.inl hn)),
        ihb σ τ (fun n hn => h n (Or.inr hn))]
  | all a ih =>
      intro σ τ h
      simp only [subst]
      apply congrArg all
      exact ih (Term.upSubst σ) (Term.upSubst τ) (fun n hn => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst, h n hn])
  | ex a ih =>
      intro σ τ h
      simp only [subst]
      apply congrArg ex
      exact ih (Term.upSubst σ) (Term.upSubst τ) (fun n hn => by
        cases n with
        | zero => rfl
        | succ n =>
            simp [Term.upSubst, h n hn])

/-- PA-formula substitution by variables is just PA-formula renaming. -/
theorem subst_var_rename (phi : Formula) (r : Nat → Nat) :
    subst (fun n => Term.var (r n)) phi = rename r phi := by
  induction phi generalizing r with
  | eq a b =>
      simp [subst, rename, term_subst_var_rename]
  | bot =>
      rfl
  | imp a b iha ihb =>
      simp [subst, rename, iha, ihb]
  | and a b iha ihb =>
      simp [subst, rename, iha, ihb]
  | or a b iha ihb =>
      simp [subst, rename, iha, ihb]
  | all a ih =>
      simp only [subst, rename]
      apply congrArg all
      have hsubst :
          subst (Term.upSubst (fun n => Term.var (r n))) a =
            subst (fun n => Term.var (SetTheory.up r n)) a := by
        exact subst_ext a _ _ (fun n => by cases n <;> rfl)
      rw [hsubst]
      exact ih (SetTheory.up r)
  | ex a ih =>
      simp only [subst, rename]
      apply congrArg ex
      have hsubst :
          subst (Term.upSubst (fun n => Term.var (r n))) a =
            subst (fun n => Term.var (SetTheory.up r n)) a := by
        exact subst_ext a _ _ (fun n => by cases n <;> rfl)
      rw [hsubst]
      exact ih (SetTheory.up r)

/-- Substituting PA de Bruijn 0 by a variable is just PA-formula renaming by the
corresponding variable-instantiation map. -/
theorem subst_instTerm_var (phi : Formula) (k : Nat) :
    subst (instTerm (Term.var k)) phi =
      rename (SetTheory.inst k) phi := by
  rw [← subst_var_rename phi (SetTheory.inst k)]
  exact subst_ext phi _ _ (fun n => by cases n <;> rfl)

theorem subst_id (phi : Formula) :
    subst (fun n => Term.var n) phi = phi := by
  rw [subst_var_rename, rename_id]

theorem subst_eq_of_sentence {phi : Formula} (hphi : Sentence phi)
    (σ : Nat → Term) : subst σ phi = phi := by
  calc
    subst σ phi = subst (fun n => Term.var n) phi := by
      apply subst_ext_free
      intro n hn
      exact False.elim (hphi n hn)
    _ = phi := subst_id phi

theorem subst_instTerm_rename_up (phi : Formula) (r : Nat → Nat) (t : Term) :
    subst (instTerm (Term.rename r t)) (rename (SetTheory.up r) phi) =
      rename r (subst (instTerm t) phi) := by
  rw [subst_rename, rename_subst]
  exact subst_ext phi _ _ (fun n => by
    cases n with
    | zero => rfl
    | succ n => rfl)

/-- Instantiating the newest variable after shifting a term through one binder
leaves that term unchanged. -/
theorem term_subst_instTerm_rename_succ (t u : Term) :
    Term.subst (instTerm u) (Term.rename Nat.succ t) = t := by
  rw [Term.subst_rename]
  simpa [instTerm, Term.rename_id] using
    (term_subst_var_rename t (fun n : Nat => n))

/-- Iterate lifting of a term substitution through `k` binders. -/
def iterUpSubst (k : Nat) (σ : Nat → Term) : Nat → Term :=
  Nat.rec σ (fun _ τ => Term.upSubst τ) k

/-- Iterated lifted substitution commutes with the matching variable shift. -/
theorem term_subst_iterUpSubst_rename_add
    (k : Nat) (σ : Nat → Term) (t : Term) :
    Term.subst (iterUpSubst k σ)
        (Term.rename (fun n => n+k) t) =
      Term.rename (fun n => n+k) (Term.subst σ t) := by
  induction k with
  | zero =>
      change Term.subst σ (Term.rename (fun n => n) t) =
        Term.rename (fun n => n) (Term.subst σ t)
      rw [Term.rename_id, Term.rename_id]
  | succ k ih =>
      have hrename :
          Term.rename (fun n => n+(k+1)) t =
            Term.rename Nat.succ (Term.rename (fun n => n+k) t) := by
        rw [Term.rename_comp]
        exact Term.rename_ext t _ _ (fun n => by omega)
      rw [iterUpSubst, hrename, Term.subst_rename_succ_up]
      change Term.rename Nat.succ
          (Term.subst (iterUpSubst k σ)
            (Term.rename (fun n => n+k) t)) =
        Term.rename (fun n => n+(k+1)) (Term.subst σ t)
      rw [ih]
      rw [Term.rename_comp]
      exact Term.rename_ext (Term.subst σ t)
        (fun n => Nat.succ (n+k))
        (fun n => n+(k+1)) (fun n => by omega)

/-- Instantiating below an arbitrary block of unused variables removes the
newest variable of that block. -/
theorem term_subst_instTerm_rename_add_succ
    (d : Nat) (t u : Term) :
    Term.subst (instTerm u)
        (Term.rename (fun n : Nat => n + d + 1) t) =
      Term.rename (fun n : Nat => n + d) t := by
  have hrename :
      Term.rename (fun n : Nat => n + d + 1) t =
        Term.rename Nat.succ (Term.rename (fun n : Nat => n + d) t) := by
    rw [Term.rename_comp]
  rw [hrename]
  exact term_subst_instTerm_rename_succ
    (Term.rename (fun n : Nat => n + d) t) u

/-- Transport instantiation through `k` surrounding binders and an additional
block of `d` variables. -/
theorem term_subst_iterUpSubst_instTerm_rename_add_succ_offset
    (k d : Nat) (t u : Term) :
    Term.subst (iterUpSubst k (instTerm u))
        (Term.rename (fun n : Nat => n + k + d + 1) t) =
      Term.rename (fun n : Nat => n + k + d) t := by
  have hinput :
      Term.rename (fun n : Nat => n + k + d + 1) t =
        Term.rename (fun n : Nat => n + k)
          (Term.rename (fun n : Nat => n + d + 1) t) := by
    rw [Term.rename_comp]
    exact Term.rename_ext t _ _ (fun n => by omega)
  rw [hinput, term_subst_iterUpSubst_rename_add]
  rw [term_subst_instTerm_rename_add_succ]
  rw [Term.rename_comp]
  exact Term.rename_ext t _ _ (fun n => by omega)

/-- The variable exposed at lift depth `k` is replaced by the witness shifted
through those `k` binders. -/
theorem term_subst_iterUpSubst_instTerm_var_depth
    (k : Nat) (u : Term) :
    Term.subst (iterUpSubst k (instTerm u)) (Term.var k) =
      Term.rename (fun n : Nat => n + k) u := by
  induction k with
  | zero =>
      change u = Term.rename (fun n : Nat => n + 0) u
      exact (Term.rename_id u).symm
  | succ k ih =>
      rw [iterUpSubst]
      change Term.rename Nat.succ
          (Term.subst (iterUpSubst k (instTerm u)) (Term.var k)) =
        Term.rename (fun n : Nat => n + (k+1)) u
      rw [ih, Term.rename_comp]
      exact Term.rename_ext u _ _ (fun n => by omega)

/-- Instantiating the newest variable after shifting a term through two binders
removes the outer shift and leaves the term shifted through one binder. -/
theorem term_subst_instTerm_rename_two_succ (t u : Term) :
    Term.subst (instTerm u) (Term.rename (fun n : Nat => n + 1 + 1) t) =
      Term.rename Nat.succ t := by
  change Term.subst (iterUpSubst 0 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1) t) =
    Term.rename Nat.succ t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 0 1 t u

/-- Substituting under one lifted binder after shifting a term through two
binders removes the newest shift and leaves the single shift. -/
theorem term_subst_upSubst_instTerm_rename_two_succ (t u : Term) :
    Term.subst (Term.upSubst (instTerm u))
        (Term.rename (fun n : Nat => n + 1 + 1) t) =
      Term.rename Nat.succ t := by
  change Term.subst (iterUpSubst 1 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1) t) =
    Term.rename Nat.succ t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 1 0 t u

/-- Substituting under one lifted binder after shifting a term through three
binders removes the newest shift and leaves the double shift. -/
theorem term_subst_upSubst_instTerm_rename_three_succ (t u : Term) :
    Term.subst (Term.upSubst (instTerm u))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1) t := by
  change Term.subst (iterUpSubst 1 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 1 1 t u

/-- Substituting under two lifted binders after shifting a term through three
binders removes the newest shift and leaves the double shift. -/
theorem term_subst_up_up_instTerm_rename_three_succ (t u : Term) :
    Term.subst (Term.upSubst (Term.upSubst (instTerm u)))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1) t := by
  change Term.subst (iterUpSubst 2 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 2 0 t u

/-- The newest variable shifted through two binders is instantiated by the
doubly shifted witness. -/
theorem term_subst_up_up_instTerm_rename_two_var_zero (u : Term) :
    Term.subst (Term.upSubst (Term.upSubst (instTerm u)))
        (Term.rename (fun n : Nat => n + 1 + 1) (Term.var 0)) =
      Term.rename (fun n : Nat => n + 1 + 1) u := by
  change Term.subst (iterUpSubst 2 (instTerm u)) (Term.var 2) =
    Term.rename (fun n : Nat => n + 1 + 1) u
  exact term_subst_iterUpSubst_instTerm_var_depth 2 u

/-- Substituting under two lifted binders after shifting a term through four
binders removes the newest shift and leaves the triple shift. -/
theorem term_subst_up_up_instTerm_rename_four_succ (t u : Term) :
    Term.subst (Term.upSubst (Term.upSubst (instTerm u)))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1 + 1) t := by
  change Term.subst (iterUpSubst 2 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 2 1 t u

/-- Substituting under three lifted binders after shifting a term through four
binders removes the newest shift and leaves the triple shift. -/
theorem term_subst_up_up_up_instTerm_rename_four_succ (t u : Term) :
    Term.subst (Term.upSubst (Term.upSubst (Term.upSubst (instTerm u))))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1 + 1) t := by
  change Term.subst (iterUpSubst 3 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 3 0 t u

/-- Substituting under three lifted binders after shifting a term through five
binders removes the newest shift and leaves the quadruple shift. -/
theorem term_subst_up_up_up_instTerm_rename_five_succ (t u : Term) :
    Term.subst (Term.upSubst (Term.upSubst (Term.upSubst (instTerm u))))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1) t := by
  change Term.subst (iterUpSubst 3 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 3 1 t u

/-- Substituting under four lifted binders after shifting a term through five
binders removes the newest shift and leaves the quadruple shift. -/
theorem term_subst_up_up_up_up_instTerm_rename_five_succ (t u : Term) :
    Term.subst
        (Term.upSubst
          (Term.upSubst (Term.upSubst (Term.upSubst (instTerm u)))))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1) t := by
  change Term.subst (iterUpSubst 4 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 4 0 t u

/-- Substituting under four lifted binders after shifting a term through six
binders removes the newest shift and leaves the quintuple shift. -/
theorem term_subst_up_up_up_up_instTerm_rename_six_succ (t u : Term) :
    Term.subst
        (Term.upSubst
          (Term.upSubst (Term.upSubst (Term.upSubst (instTerm u)))))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1) t := by
  change Term.subst (iterUpSubst 4 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 4 1 t u

/-- Substituting under five lifted binders after shifting a term through six
binders removes the newest shift and leaves the quintuple shift. -/
theorem term_subst_up_up_up_up_up_instTerm_rename_six_succ (t u : Term) :
    Term.subst
        (Term.upSubst
          (Term.upSubst
            (Term.upSubst (Term.upSubst (Term.upSubst (instTerm u))))))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1) t := by
  change Term.subst (iterUpSubst 5 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 5 0 t u

/-- Substituting under six lifted binders after shifting a term through seven
binders removes the newest shift and leaves the sextuple shift. -/
theorem term_subst_up_up_up_up_up_up_instTerm_rename_seven_succ
    (t u : Term) :
    Term.subst
        (Term.upSubst
          (Term.upSubst
            (Term.upSubst
              (Term.upSubst (Term.upSubst (Term.upSubst (instTerm u)))))))
        (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1 + 1 + 1) t) =
      Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1 + 1) t := by
  change Term.subst (iterUpSubst 6 (instTerm u))
      (Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1 + 1 + 1) t) =
    Term.rename (fun n : Nat => n + 1 + 1 + 1 + 1 + 1 + 1) t
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset 6 0 t u

/-- Two lifted substitutions commute with the matching two-variable shift. -/
theorem term_subst_up_up_rename_add_two
    (σ : Nat → Term) (t : Term) :
    Term.subst (Term.upSubst (Term.upSubst σ))
        (Term.rename (fun n => n + 2) t) =
      Term.rename (fun n => n + 2) (Term.subst σ t) := by
  exact term_subst_iterUpSubst_rename_add 2 σ t

/-- General de Bruijn bookkeeping lemma: substituting a variable under `k`
lifted binders through a term renamed by `k+1` successors removes exactly the
newest shift. -/
theorem term_subst_iterUpSubst_instTerm_var_rename_add_succ
    (k elem : Nat) (t : Term) :
    Term.subst (iterUpSubst k (instTerm (Term.var elem)))
        (Term.rename (fun n : Nat => n + k + 1) t) =
      Term.rename (fun n : Nat => n + k) t := by
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset
    k 0 t (Term.var elem)

/-- General de Bruijn bookkeeping lemma: substituting an arbitrary term under
`k` lifted binders through a term renamed by `k+1` successors removes exactly
the newest shift. -/
theorem term_subst_iterUpSubst_instTerm_rename_add_succ
    (k : Nat) (t u : Term) :
    Term.subst (iterUpSubst k (instTerm u))
        (Term.rename (fun n : Nat => n + k + 1) t) =
      Term.rename (fun n : Nat => n + k) t := by
  exact term_subst_iterUpSubst_instTerm_rename_add_succ_offset k 0 t u

/-- Renaming below one binder commutes with first shifting a term through that
binder. -/
theorem term_rename_up_rename_succ (r : Nat → Nat) (t : Term) :
    Term.rename (SetTheory.up r) (Term.rename Nat.succ t) =
      Term.rename Nat.succ (Term.rename r t) := by
  rw [Term.rename_comp, Term.rename_comp]
  exact Term.rename_ext t _ _ (fun n => rfl)

/-- Lift a variable renaming through `k` surrounding binders. -/
def iterUpRenaming (k : Nat) (r : Nat → Nat) : Nat → Nat :=
  Nat.rec r (fun _ s => SetTheory.up s) k

/-- Shift every free variable of a term through `k` surrounding binders. -/
def iterTermRenameSucc (k : Nat) (t : Term) : Term :=
  Nat.rec t (fun _ u => Term.rename Nat.succ u) k

/-- An iterated lifted renaming acts as the original renaming above the block
of `k` newly bound variables, preserving the block offset. -/
theorem iterUpRenaming_add (k : Nat) (r : Nat → Nat) (n : Nat) :
    iterUpRenaming k r (n + k) = r n + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change SetTheory.up (iterUpRenaming k r) (n + (k + 1)) =
        r n + (k + 1)
      rw [show n + (k + 1) = (n + k) + 1 by omega]
      simp only [SetTheory.up]
      rw [ih]
      omega

/-- An iterated lifted renaming commutes with shifting a term through the same
number of surrounding binders. -/
theorem term_rename_iterUpRenaming_iterTermRenameSucc
    (k : Nat) (r : Nat → Nat) (t : Term) :
    Term.rename (iterUpRenaming k r) (iterTermRenameSucc k t) =
      iterTermRenameSucc k (Term.rename r t) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change Term.rename (SetTheory.up (iterUpRenaming k r))
          (Term.rename Nat.succ (iterTermRenameSucc k t)) =
        Term.rename Nat.succ (iterTermRenameSucc k (Term.rename r t))
      rw [term_rename_up_rename_succ, ih]

/-- Renaming by addition of `k` is the canonical `k`-fold successor shift. -/
theorem term_rename_add_eq_iterTermRenameSucc (k : Nat) (t : Term) :
    Term.rename (fun n => n + k) t = iterTermRenameSucc k t := by
  induction k with
  | zero =>
      change Term.rename (fun n => n + 0) t = t
      simpa using Term.rename_id t
  | succ k ih =>
      have hrename :
          Term.rename (fun n => n + (k + 1)) t =
            Term.rename Nat.succ (Term.rename (fun n => n + k) t) := by
        rw [Term.rename_comp]
        exact Term.rename_ext t _ _ (fun n => by omega)
      rw [hrename, ih]
      simp [iterTermRenameSucc]

/-- Renaming below `k` binders commutes with shifting a term through those
binders. -/
theorem term_rename_iterUpRenaming_rename_add
    (k : Nat) (r : Nat → Nat) (t : Term) :
    Term.rename (iterUpRenaming k r)
        (Term.rename (fun n => n + k) t) =
      Term.rename (fun n => n + k) (Term.rename r t) := by
  calc
    _ = Term.rename (iterUpRenaming k r)
        (iterTermRenameSucc k t) :=
      congrArg (Term.rename (iterUpRenaming k r))
        (term_rename_add_eq_iterTermRenameSucc k t)
    _ = iterTermRenameSucc k (Term.rename r t) :=
      term_rename_iterUpRenaming_iterTermRenameSucc k r t
    _ = _ :=
      (term_rename_add_eq_iterTermRenameSucc k (Term.rename r t)).symm

/-- Extensional form of `term_rename_add_eq_iterTermRenameSucc`, for the
syntactically varied fixed shifts that arise in opened formulas. -/
theorem term_rename_eq_iterTermRenameSucc
    (k : Nat) (t : Term) (r : Nat → Nat) (hr : ∀ n, r n = n + k) :
    Term.rename r t = iterTermRenameSucc k t := by
  rw [Term.rename_ext t r (fun n => n + k) hr]
  exact term_rename_add_eq_iterTermRenameSucc k t

/-- Renaming a term already shifted through one binder by the lifted successor
renaming is the same as shifting it through one more ordinary binder. -/
theorem term_rename_up_succ_rename_succ (t : Term) :
    Term.rename (SetTheory.up Nat.succ) (Term.rename Nat.succ t) =
      Term.rename Nat.succ (Term.rename Nat.succ t) := by
  exact term_rename_up_rename_succ Nat.succ t

/-- Instantiating the newest variable after two lifted successor renamings of
an already shifted term removes the newest binder and leaves the double shift. -/
theorem term_subst_instTerm_rename_up_up_succ
    (t u : Term) :
    Term.subst (instTerm u)
      (Term.rename (SetTheory.up Nat.succ)
        (Term.rename (SetTheory.up Nat.succ) (Term.rename Nat.succ t))) =
      Term.rename Nat.succ (Term.rename Nat.succ t) := by
  rw [term_rename_up_succ_rename_succ t]
  rw [term_rename_up_succ_rename_succ (Term.rename Nat.succ t)]
  exact term_subst_instTerm_rename_succ
    (Term.rename Nat.succ (Term.rename Nat.succ t)) u

/-- Instantiating the newest variable after shifting a formula through one
binder leaves that formula unchanged. -/
theorem subst_instTerm_rename_succ (phi : Formula) (t : Term) :
    subst (instTerm t) (rename Nat.succ phi) = phi := by
  rw [subst_rename]
  simpa [instTerm, rename_id] using
    (subst_var_rename phi (fun n : Nat => n))

/-- Instantiating the newest variable with the currently opened variable after
shifting a formula through one binder recovers the original formula. -/
theorem subst_instTerm_var_zero_rename_up_succ (phi : Formula) :
    subst (instTerm (Term.var 0))
      (rename (SetTheory.up Nat.succ) phi) = phi := by
  rw [subst_rename]
  exact Eq.trans
    (subst_ext phi _ _ (fun n => by
      cases n with
      | zero => rfl
      | succ n => rfl))
    (subst_id phi)

theorem subst_instTerm_subst_up (phi : Formula) (σ : Nat → Term) (t : Term) :
    subst (instTerm (Term.subst σ t)) (subst (Term.upSubst σ) phi) =
      subst σ (subst (instTerm t) phi) := by
  rw [subst_comp, subst_comp]
  exact subst_ext phi _ _ (fun n => by
    cases n with
    | zero => rfl
    | succ n =>
        simp [instTerm, Term.subst, Term.upSubst,
          term_subst_instTerm_rename_succ])

/-- Instantiating the two newest variables with the two currently opened
variables after shifting a formula through two surrounding binders twice
recovers the original formula.

This is the two-witness analogue of `subst_instTerm_rename_succ`, and is useful
when a proof has opened one pair of existential witnesses and must repackage
another pair using the same current de Bruijn slots. -/
theorem subst_instTerm_var_zero_up_var_one_rename_up_up_succ_twice
    (phi : Formula) :
    subst (instTerm (Term.var 0))
      (subst (Term.upSubst (instTerm (Term.var 1)))
        (rename (SetTheory.up (SetTheory.up Nat.succ))
          (rename (SetTheory.up (SetTheory.up Nat.succ)) phi))) = phi := by
  rw [subst_comp, subst_rename, subst_rename]
  exact Eq.trans
    (subst_ext phi _ _ (fun n => by
      cases n with
      | zero =>
          rfl
      | succ n =>
          cases n with
          | zero =>
              rfl
          | succ n =>
              rfl))
    (subst_id phi)

theorem Sat_instTerm {α : Type u} (M : PreModel α) (phi : Formula)
    (t : Term) (e : Nat → α) :
    Sat M e (subst (instTerm t) phi) ↔
      Sat M (SetTheory.scons (Term.eval M e t) e) phi := by
  rw [Sat_subst]
  exact Sat_ext M phi (fun n => by cases n <;> rfl)

/-- Natural deduction for PA formulas.  This is deliberately proof-theoretic:
terms are genuine PA terms, quantifier rules use de Bruijn substitution, and
equality elimination is the Leibniz rule for a one-variable formula context. -/
inductive Prov : List Formula → Formula → Prop
  | P_ass    : ∀ G a, a ∈ G → Prov G a
  | P_impI   : ∀ G a b, Prov (a :: G) b → Prov G (imp a b)
  | P_impE   : ∀ G a b, Prov G (imp a b) → Prov G a → Prov G b
  | P_botE   : ∀ G a, Prov G bot → Prov G a
  | P_lem    : ∀ G a, Prov G (or a (imp a bot))
  | P_andI   : ∀ G a b, Prov G a → Prov G b → Prov G (and a b)
  | P_andE1  : ∀ G a b, Prov G (and a b) → Prov G a
  | P_andE2  : ∀ G a b, Prov G (and a b) → Prov G b
  | P_orI1   : ∀ G a b, Prov G a → Prov G (or a b)
  | P_orI2   : ∀ G a b, Prov G b → Prov G (or a b)
  | P_orE    : ∀ G a b c, Prov G (or a b) → Prov (a :: G) c →
               Prov (b :: G) c → Prov G c
  | P_allI   : ∀ G a, Prov (G.map (rename Nat.succ)) a → Prov G (all a)
  | P_allE   : ∀ G a t, Prov G (all a) → Prov G (subst (instTerm t) a)
  | P_exI    : ∀ G a t, Prov G (subst (instTerm t) a) → Prov G (ex a)
  | P_exE    : ∀ G a c, Prov G (ex a) →
               Prov (a :: G.map (rename Nat.succ)) (rename Nat.succ c) →
               Prov G c
  | P_eqRefl : ∀ G t, Prov G (eq t t)
  | P_eqElim : ∀ G s t a,
      Prov G (eq s t) → Prov G (subst (instTerm s) a) →
      Prov G (subst (instTerm t) a)

/-- Context inclusion is preserved by consing the same PA formula. -/
theorem cons_sub {a : Formula} {G G' : List Formula}
    (hsub : ∀ x, x ∈ G → x ∈ G') :
    ∀ x, x ∈ a :: G → x ∈ a :: G' := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact List.mem_cons.mpr (Or.inl rfl)
  · exact List.mem_cons.mpr (Or.inr (hsub x hx))

/-- Context inclusion is preserved by mapping a PA formula transformer. -/
theorem mem_map_sub {f : Formula → Formula} {G G' : List Formula}
    (hsub : ∀ x, x ∈ G → x ∈ G') :
    ∀ x, x ∈ G.map f → x ∈ G'.map f := by
  intro x hx
  rw [List.mem_map] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨y, hsub y hy, rfl⟩

/-- Weakening for the PA calculus: enlarging the context preserves proofs. -/
theorem Prov_weaken {G : List Formula} {a : Formula} (h : Prov G a) :
    ∀ G', (∀ x, x ∈ G → x ∈ G') → Prov G' a := by
  induction h with
  | P_ass G a hin =>
      intro G' hsub
      exact .P_ass _ _ (hsub a hin)
  | P_impI G a b _ ih =>
      intro G' hsub
      exact .P_impI _ _ _ (ih _ (cons_sub hsub))
  | P_impE G a b _ _ ihab iha =>
      intro G' hsub
      exact .P_impE _ a b (ihab _ hsub) (iha _ hsub)
  | P_botE G a _ ih =>
      intro G' hsub
      exact .P_botE _ a (ih _ hsub)
  | P_lem G a =>
      intro G' hsub
      exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro G' hsub
      exact .P_andI _ _ _ (iha _ hsub) (ihb _ hsub)
  | P_andE1 G a b _ ih =>
      intro G' hsub
      exact .P_andE1 _ a b (ih _ hsub)
  | P_andE2 G a b _ ih =>
      intro G' hsub
      exact .P_andE2 _ a b (ih _ hsub)
  | P_orI1 G a b _ ih =>
      intro G' hsub
      exact .P_orI1 _ _ _ (ih _ hsub)
  | P_orI2 G a b _ ih =>
      intro G' hsub
      exact .P_orI2 _ _ _ (ih _ hsub)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro G' hsub
      exact .P_orE _ a b c (ihor _ hsub)
        (iha _ (cons_sub hsub)) (ihb _ (cons_sub hsub))
  | P_allI G a _ ih =>
      intro G' hsub
      exact .P_allI _ _ (ih _ (mem_map_sub hsub))
  | P_allE G a t _ ih =>
      intro G' hsub
      exact .P_allE _ a t (ih _ hsub)
  | P_exI G a t _ ih =>
      intro G' hsub
      exact .P_exI _ a t (ih _ hsub)
  | P_exE G a c _ _ ihex ihbody =>
      intro G' hsub
      exact .P_exE _ a c (ihex _ hsub)
        (ihbody _ (cons_sub (mem_map_sub hsub)))
  | P_eqRefl G t =>
      intro G' hsub
      exact .P_eqRefl _ t
  | P_eqElim G s t a _ _ iheq iha =>
      intro G' hsub
      exact .P_eqElim _ s t a (iheq _ hsub) (iha _ hsub)

/-- A handy corollary: prepend an additional PA hypothesis. -/
theorem Prov_cons {G : List Formula} {a b : Formula} (h : Prov G b) :
    Prov (a :: G) b :=
  Prov_weaken h _ (fun _ hx => List.mem_cons.mpr (Or.inr hx))

theorem map_rename_up_succ (r : Nat → Nat) (G : List Formula) :
    (G.map (rename Nat.succ)).map (rename (SetTheory.up r)) =
      (G.map (rename r)).map (rename Nat.succ) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro phi _
  exact rename_up_succ phi r

theorem map_subst_rename_succ_up (σ : Nat → Term) (G : List Formula) :
    (G.map (rename Nat.succ)).map (subst (Term.upSubst σ)) =
      (G.map (subst σ)).map (rename Nat.succ) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro phi _
  exact subst_rename_succ_up phi σ

theorem Prov_rename {G : List Formula} {phi : Formula} (h : Prov G phi) :
    ∀ r, Prov (G.map (rename r)) (rename r phi) := by
  induction h with
  | P_ass G a hin =>
      intro r
      exact .P_ass _ _ (List.mem_map_of_mem (f := rename r) hin)
  | P_impI G a b _ ih =>
      intro r
      exact .P_impI _ _ _ (ih r)
  | P_impE G a b _ _ ihab iha =>
      intro r
      exact .P_impE _ (rename r a) (rename r b) (ihab r) (iha r)
  | P_botE G a _ ih =>
      intro r
      exact .P_botE _ (rename r a) (ih r)
  | P_lem G a =>
      intro r
      exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro r
      exact .P_andI _ _ _ (iha r) (ihb r)
  | P_andE1 G a b _ ih =>
      intro r
      exact .P_andE1 _ (rename r a) (rename r b) (ih r)
  | P_andE2 G a b _ ih =>
      intro r
      exact .P_andE2 _ (rename r a) (rename r b) (ih r)
  | P_orI1 G a b _ ih =>
      intro r
      exact .P_orI1 _ _ _ (ih r)
  | P_orI2 G a b _ ih =>
      intro r
      exact .P_orI2 _ _ _ (ih r)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro r
      exact .P_orE _ (rename r a) (rename r b) (rename r c)
        (ihor r) (iha r) (ihb r)
  | P_allI G a _ ih =>
      intro r
      apply Prov.P_allI
      rw [← map_rename_up_succ r G]
      exact ih (SetTheory.up r)
  | P_allE G a t _ ih =>
      intro r
      have hAll : Prov (G.map (rename r)) (all (rename (SetTheory.up r) a)) := by
        simpa [rename] using ih r
      have hInst := Prov.P_allE _ (rename (SetTheory.up r) a) (Term.rename r t) hAll
      simpa [subst_instTerm_rename_up] using hInst
  | P_exI G a t _ ih =>
      intro r
      apply Prov.P_exI _ (rename (SetTheory.up r) a) (Term.rename r t)
      simpa [subst_instTerm_rename_up] using ih r
  | P_exE G a c _ _ ihex ihbody =>
      intro r
      have hEx : Prov (G.map (rename r)) (ex (rename (SetTheory.up r) a)) := by
        simpa [rename] using ihex r
      have hctx :
          (a :: G.map (rename Nat.succ)).map (rename (SetTheory.up r)) =
            rename (SetTheory.up r) a :: (G.map (rename r)).map (rename Nat.succ) := by
        simp only [List.map_cons]
        rw [map_rename_up_succ r G]
      have hbody' :
          Prov (rename (SetTheory.up r) a :: (G.map (rename r)).map (rename Nat.succ))
            (rename Nat.succ (rename r c)) := by
        rw [← hctx, ← rename_up_succ c r]
        exact ihbody (SetTheory.up r)
      exact .P_exE _ (rename (SetTheory.up r) a) (rename r c) hEx hbody'
  | P_eqRefl G t =>
      intro r
      exact .P_eqRefl _ (Term.rename r t)
  | P_eqElim G s t a _ _ iheq iha =>
      intro r
      have hEq : Prov (G.map (rename r)) (eq (Term.rename r s) (Term.rename r t)) := by
        simpa [rename] using iheq r
      have hA :
          Prov (G.map (rename r))
            (subst (instTerm (Term.rename r s)) (rename (SetTheory.up r) a)) := by
        simpa [subst_instTerm_rename_up] using iha r
      have hElim := Prov.P_eqElim _ (Term.rename r s) (Term.rename r t)
        (rename (SetTheory.up r) a) hEq hA
      simpa [subst_instTerm_rename_up] using hElim

/-- Simultaneous substitution of PA terms through a derivation. -/
theorem Prov_subst {G : List Formula} {phi : Formula} (h : Prov G phi) :
    ∀ σ, Prov (G.map (subst σ)) (subst σ phi) := by
  induction h with
  | P_ass G a hin =>
      intro σ
      exact .P_ass _ _ (List.mem_map_of_mem (f := subst σ) hin)
  | P_impI G a b _ ih =>
      intro σ
      exact .P_impI _ _ _ (ih σ)
  | P_impE G a b _ _ ihab iha =>
      intro σ
      exact .P_impE _ (subst σ a) (subst σ b) (ihab σ) (iha σ)
  | P_botE G a _ ih =>
      intro σ
      exact .P_botE _ (subst σ a) (ih σ)
  | P_lem G a =>
      intro σ
      exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro σ
      exact .P_andI _ _ _ (iha σ) (ihb σ)
  | P_andE1 G a b _ ih =>
      intro σ
      exact .P_andE1 _ (subst σ a) (subst σ b) (ih σ)
  | P_andE2 G a b _ ih =>
      intro σ
      exact .P_andE2 _ (subst σ a) (subst σ b) (ih σ)
  | P_orI1 G a b _ ih =>
      intro σ
      exact .P_orI1 _ _ _ (ih σ)
  | P_orI2 G a b _ ih =>
      intro σ
      exact .P_orI2 _ _ _ (ih σ)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro σ
      exact .P_orE _ (subst σ a) (subst σ b) (subst σ c)
        (ihor σ) (iha σ) (ihb σ)
  | P_allI G a _ ih =>
      intro σ
      apply Prov.P_allI
      rw [← map_subst_rename_succ_up σ G]
      exact ih (Term.upSubst σ)
  | P_allE G a t _ ih =>
      intro σ
      have hAll : Prov (G.map (subst σ)) (all (subst (Term.upSubst σ) a)) := by
        simpa [subst] using ih σ
      have hInst := Prov.P_allE _ (subst (Term.upSubst σ) a)
        (Term.subst σ t) hAll
      simpa [subst, subst_instTerm_subst_up] using hInst
  | P_exI G a t _ ih =>
      intro σ
      apply Prov.P_exI _ (subst (Term.upSubst σ) a) (Term.subst σ t)
      simpa [subst_instTerm_subst_up] using ih σ
  | P_exE G a c _ _ ihex ihbody =>
      intro σ
      have hEx : Prov (G.map (subst σ)) (ex (subst (Term.upSubst σ) a)) := by
        simpa [subst] using ihex σ
      have hctx :
          (a :: G.map (rename Nat.succ)).map (subst (Term.upSubst σ)) =
            subst (Term.upSubst σ) a :: (G.map (subst σ)).map (rename Nat.succ) := by
        simp only [List.map_cons]
        rw [map_subst_rename_succ_up σ G]
      have hbody' :
          Prov (subst (Term.upSubst σ) a ::
              (G.map (subst σ)).map (rename Nat.succ))
            (rename Nat.succ (subst σ c)) := by
        rw [← hctx, ← subst_rename_succ_up c σ]
        exact ihbody (Term.upSubst σ)
      exact .P_exE _ (subst (Term.upSubst σ) a) (subst σ c) hEx hbody'
  | P_eqRefl G t =>
      intro σ
      exact .P_eqRefl _ (Term.subst σ t)
  | P_eqElim G s t a _ _ iheq iha =>
      intro σ
      have hEq : Prov (G.map (subst σ))
          (eq (Term.subst σ s) (Term.subst σ t)) := by
        simpa [subst] using iheq σ
      have hA :
          Prov (G.map (subst σ))
            (subst (instTerm (Term.subst σ s))
              (subst (Term.upSubst σ) a)) := by
        simpa [subst_instTerm_subst_up] using iha σ
      have hElim := Prov.P_eqElim _ (Term.subst σ s) (Term.subst σ t)
        (subst (Term.upSubst σ) a) hEq hA
      simpa [subst_instTerm_subst_up] using hElim

theorem Prov_cut {G : List Formula} {phi : Formula} (h : Prov G phi) :
    ∀ De, (∀ x, x ∈ G → Prov De x) → Prov De phi := by
  induction h with
  | P_ass G a hin =>
      intro De hD
      exact hD a hin
  | P_impI G a b _ ih =>
      intro De hD
      apply Prov.P_impI
      apply ih
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))
      · exact Prov_cons (hD x hx)
  | P_impE G a b _ _ ihab iha =>
      intro De hD
      exact .P_impE _ a b (ihab De hD) (iha De hD)
  | P_botE G a _ ih =>
      intro De hD
      exact .P_botE _ a (ih De hD)
  | P_lem G a =>
      intro De hD
      exact .P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro De hD
      exact .P_andI _ _ _ (iha De hD) (ihb De hD)
  | P_andE1 G a b _ ih =>
      intro De hD
      exact .P_andE1 _ a b (ih De hD)
  | P_andE2 G a b _ ih =>
      intro De hD
      exact .P_andE2 _ a b (ih De hD)
  | P_orI1 G a b _ ih =>
      intro De hD
      exact .P_orI1 _ _ _ (ih De hD)
  | P_orI2 G a b _ ih =>
      intro De hD
      exact .P_orI2 _ _ _ (ih De hD)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro De hD
      apply Prov.P_orE _ a b c (ihor De hD)
      · apply iha
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))
        · exact Prov_cons (hD x hx)
      · apply ihb
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))
        · exact Prov_cons (hD x hx)
  | P_allI G a _ ih =>
      intro De hD
      apply Prov.P_allI
      apply ih
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨x0, hx0, rfl⟩
      exact Prov_rename (hD x0 hx0) Nat.succ
  | P_allE G a t _ ih =>
      intro De hD
      exact .P_allE _ a t (ih De hD)
  | P_exI G a t _ ih =>
      intro De hD
      exact .P_exI _ a t (ih De hD)
  | P_exE G a c _ _ ihex ihbody =>
      intro De hD
      apply Prov.P_exE _ a c (ihex De hD)
      apply ihbody
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact .P_ass _ _ (List.mem_cons.mpr (Or.inl rfl))
      · rw [List.mem_map] at hx
        rcases hx with ⟨x0, hx0, rfl⟩
        exact Prov_cons (Prov_rename (hD x0 hx0) Nat.succ)
  | P_eqRefl G t =>
      intro De hD
      exact .P_eqRefl _ t
  | P_eqElim G s t a _ _ iheq iha =>
      intro De hD
      exact .P_eqElim _ s t a (iheq De hD) (iha De hD)

theorem soundness {α : Type u} (M : PreModel α) {G : List Formula} {a : Formula}
    (h : Prov G a) :
    ∀ e : Nat → α, (∀ x, x ∈ G → Sat M e x) → Sat M e a := by
  induction h with
  | P_ass G a hin =>
      intro e hG
      exact hG a hin
  | P_impI G a b _ ih =>
      intro e hG ha
      exact ih e (fun x hx => by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hG x hx)
  | P_impE G a b _ _ ihab iha =>
      intro e hG
      exact ihab e hG (iha e hG)
  | P_botE G a _ ih =>
      intro e hG
      exact False.elim (ih e hG)
  | P_lem G a =>
      intro e hG
      exact Classical.em (Sat M e a)
  | P_andI G a b _ _ iha ihb =>
      intro e hG
      exact ⟨iha e hG, ihb e hG⟩
  | P_andE1 G a b _ ih =>
      intro e hG
      exact (ih e hG).1
  | P_andE2 G a b _ ih =>
      intro e hG
      exact (ih e hG).2
  | P_orI1 G a b _ ih =>
      intro e hG
      exact Or.inl (ih e hG)
  | P_orI2 G a b _ ih =>
      intro e hG
      exact Or.inr (ih e hG)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro e hG
      rcases ihor e hG with ha | hb
      · exact iha e (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ha
          · exact hG x hx)
      · exact ihb e (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hb
          · exact hG x hx)
  | P_allI G a _ ih =>
      intro e hG d
      exact ih (SetTheory.scons d e) (fun x hx => by
        rw [List.mem_map] at hx
        rcases hx with ⟨g, hg, rfl⟩
        exact (Sat_rename_succ M g e d).mpr (hG g hg))
  | P_allE G a t _ ih =>
      intro e hG
      exact (Sat_instTerm M a t e).mpr (ih e hG (Term.eval M e t))
  | P_exI G a t _ ih =>
      intro e hG
      exact ⟨Term.eval M e t, (Sat_instTerm M a t e).mp (ih e hG)⟩
  | P_exE G a c _ _ ihex ihbody =>
      intro e hG
      rcases ihex e hG with ⟨d, hd⟩
      have hc_shift : Sat M (SetTheory.scons d e) (rename Nat.succ c) :=
        ihbody (SetTheory.scons d e) (fun x hx => by
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hd
          · rw [List.mem_map] at hx
            rcases hx with ⟨g, hg, rfl⟩
            exact (Sat_rename_succ M g e d).mpr (hG g hg))
      exact (Sat_rename_succ M c e d).mp hc_shift
  | P_eqRefl G t =>
      intro e hG
      rfl
  | P_eqElim G s t a _ _ iheq iha =>
      intro e hG
      have heq : Term.eval M e s = Term.eval M e t := iheq e hG
      have ha : Sat M (SetTheory.scons (Term.eval M e s) e) a :=
        (Sat_instTerm M a s e).mp (iha e hG)
      have henv :
          ∀ n, SetTheory.scons (Term.eval M e s) e n =
            SetTheory.scons (Term.eval M e t) e n := by
        intro n
        cases n with
        | zero => exact heq
        | succ n => rfl
      exact (Sat_instTerm M a t e).mpr ((Sat_ext M a henv).mp ha)

def BProv (B : Formula → Prop) (G : List Formula) (phi : Formula) : Prop :=
  ∃ L, (∀ x ∈ L, B x) ∧ Prov (L ++ G) phi

/-- Enlarging the finite PA context preserves relative provability. -/
theorem BProv_mono (B : Formula → Prop) (G G' : List Formula) (phi : Formula)
    (hsub : ∀ x, x ∈ G → x ∈ G') (h : BProv B G phi) :
    BProv B G' phi := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  exact Prov_weaken hp _ (fun x hx => by
    rw [List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact Or.inl hx
    · exact Or.inr (hsub x hx))

/-- A closed relative PA proof may be used under any finite PA context. -/
theorem BProv_weaken_nil {B : Formula → Prop} {G : List Formula}
    {phi : Formula} (h : BProv B [] phi) :
    BProv B G phi :=
  BProv_mono B [] G phi (fun _ hx => by cases hx) h

/-- A PA theory axiom is relatively provable from that theory. -/
theorem BProv_ax {B : Formula → Prop} {G : List Formula} {phi : Formula}
    (hphi : B phi) : BProv B G phi := by
  refine ⟨[phi], ?_, ?_⟩
  · intro x hx
    rw [List.mem_singleton] at hx
    subst x
    exact hphi
  · exact Prov.P_ass _ _ (by simp)

/-- A bare PA proof is also a proof relative to any PA theory. -/
theorem BProv_of_Prov {B : Formula → Prop} {G : List Formula} {phi : Formula}
    (h : Prov G phi) : BProv B G phi := by
  refine ⟨[], ?_, ?_⟩
  · intro x hx
    cases hx
  · simpa using h

/-- A finite-context assumption is relatively provable. -/
theorem BProv_ass {B : Formula → Prop} {G : List Formula} {phi : Formula}
    (hphi : phi ∈ G) : BProv B G phi :=
  BProv_of_Prov (Prov.P_ass G phi hphi)

/-- The head of a finite context is available without a membership subproof. -/
theorem BProv_ass_head {B : Formula → Prop} {G : List Formula}
    {phi : Formula} : BProv B (phi :: G) phi :=
  BProv_ass List.mem_cons_self

/-- Rename every finite-context assumption in a relative PA proof.  The
background theory is preserved when its axioms are sentences, since renaming a
sentence is syntactically equal to itself. -/
theorem BProv_rename_of_sentences {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {phi : Formula}
    (h : BProv B G phi) (r : Nat → Nat) :
    BProv B (G.map (rename r)) (rename r phi) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (rename r) = L := by
    calc
      L.map (rename r) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (hB x (hL x hx)) r
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  have hpRen : Prov ((L ++ G).map (rename r)) (rename r phi) :=
    Prov_rename hp r
  apply Prov_weaken hpRen
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Substitute PA terms through every finite-context assumption of a relative
PA proof.  Sentence axioms of the background theory are unchanged by the
substitution. -/
theorem BProv_subst_of_sentences {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {phi : Formula}
    (h : BProv B G phi) (σ : Nat → Term) :
    BProv B (G.map (subst σ)) (subst σ phi) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (subst σ) = L := by
    calc
      L.map (subst σ) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact subst_eq_of_sentence (hB x (hL x hx)) σ
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  have hpSub : Prov ((L ++ G).map (subst σ)) (subst σ phi) :=
    Prov_subst hp σ
  apply Prov_weaken hpSub
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Relative PA provability is closed under modus ponens. -/
theorem BProv_mp (B : Formula → Prop) (G : List Formula) (a b : Formula)
    (himp : BProv B G (imp a b)) (ha : BProv B G a) : BProv B G b := by
  rcases himp with ⟨L₁, hL₁, hpimp⟩
  rcases ha with ⟨L₂, hL₂, hpa⟩
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hL₁ x hx
    · exact hL₂ x hx
  · apply Prov.P_impE _ a b
    · exact Prov_weaken hpimp _ (fun x hx => by
        rw [List.mem_append] at hx ⊢
        grind)
    · exact Prov_weaken hpa _ (fun x hx => by
        rw [List.mem_append] at hx ⊢
        grind)

/-- A finite list of PA relative proofs can be put over one shared finite list
of theory axioms. -/
theorem BProv_bound_list (B : Formula → Prop) (D : List Formula) :
    ∀ L : List Formula, (∀ x, x ∈ L → BProv B D x) →
      ∃ Lb, (∀ x, x ∈ Lb → B x) ∧
        ∀ x, x ∈ L → Prov (Lb ++ D) x := by
  intro L
  induction L with
  | nil =>
      intro _hL
      refine ⟨[], ?_, ?_⟩
      · intro x hx
        cases hx
      · intro x hx
        cases hx
  | cons a L ih =>
      intro hL
      rcases hL a (by simp) with ⟨La, hLa, hpa⟩
      rcases ih (fun x hx => hL x (by simp [hx])) with ⟨Lb, hLb, hpL⟩
      refine ⟨La ++ Lb, ?_, ?_⟩
      · intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hLa x hx
        · exact hLb x hx
      · intro x hx
        rw [List.mem_cons] at hx
        rcases hx with rfl | hx
        · apply Prov_weaken hpa
          intro y hy
          rw [List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inl (List.mem_append.mpr (Or.inl hy))
          · exact Or.inr hy
        · apply Prov_weaken (hpL x hx)
          intro y hy
          rw [List.mem_append] at hy ⊢
          rcases hy with hy | hy
          · exact Or.inl (List.mem_append.mpr (Or.inr hy))
          · exact Or.inr hy

/-- Transport a PA relative proof to another PA theory/context once every used
source axiom and every finite-context assumption has been proved in the target. -/
theorem BProv_lift {B C : Formula → Prop} {G D : List Formula} {phi : Formula}
    (h : BProv B G phi)
    (hB : ∀ b, B b → BProv C D b)
    (hG : ∀ g, g ∈ G → BProv C D g) : BProv C D phi := by
  rcases h with ⟨Lb, hLb, hp⟩
  have hctx : ∀ x, x ∈ Lb ++ G → BProv C D x := by
    intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hB x (hLb x hx)
    · exact hG x hx
  rcases BProv_bound_list C D (Lb ++ G) hctx with ⟨Lc, hLc, hpctx⟩
  refine ⟨Lc, hLc, ?_⟩
  exact Prov_cut hp (Lc ++ D) hpctx

/-- PA relative provability is closed under cutting in proofs of the finite
context. -/
theorem BProv_cut {B : Formula → Prop} {G D : List Formula} {phi : Formula}
    (h : BProv B G phi)
    (hG : ∀ g, g ∈ G → BProv B D g) : BProv B D phi :=
  BProv_lift h (fun _ hb => BProv_ax (G := D) hb) hG

/-- Enlarging the PA background theory preserves relative provability. -/
theorem BProv_theory_mono {B C : Formula → Prop} {G : List Formula} {phi : Formula}
    (hBC : ∀ b, B b → C b) (h : BProv B G phi) : BProv C G phi :=
  BProv_lift h
    (fun b hb => BProv_ax (G := G) (hBC b hb))
    (fun g hg => BProv_of_Prov (B := C) (Prov.P_ass G g hg))

/-- PA relative provability is closed under PA equality elimination.  The
formula `a` is the one-variable PA context, instantiated first by term `s` and
then by term `t`. -/
theorem BProv_eqElim {B : Formula → Prop} {G : List Formula} {s t : Term}
    {a : Formula}
    (heq : BProv B G (eq s t))
    (ha : BProv B G (subst (instTerm s) a)) :
    BProv B G (subst (instTerm t) a) := by
  have hbare : BProv B [eq s t, subst (instTerm s) a]
      (subst (instTerm t) a) := by
    apply BProv_of_Prov
    apply Prov.P_eqElim [eq s t, subst (instTerm s) a] s t a
    · exact Prov.P_ass _ _ (by simp)
    · exact Prov.P_ass _ _ (by simp)
  exact BProv_lift hbare
    (fun _ hb => BProv_ax (G := G) hb)
    (fun g hg => by
      simp only [List.mem_cons, List.not_mem_nil] at hg
      rcases hg with rfl | hg
      · exact heq
      · rcases hg with rfl | hnil
        · exact ha
        · cases hnil)

/-- PA relative provability proves reflexivity of equality for every term. -/
theorem BProv_eqRefl {B : Formula → Prop} {G : List Formula} (t : Term) :
    BProv B G (eq t t) :=
  BProv_of_Prov (Prov.P_eqRefl G t)

/-- PA relative provability is closed under symmetry of term equality. -/
theorem BProv_eqSym {B : Formula → Prop} {G : List Formula} {s t : Term}
    (heq : BProv B G (eq s t)) :
    BProv B G (eq t s) := by
  have hrefl : BProv B G (eq s s) := BProv_eqRefl s
  have ha : BProv B G
      (subst (instTerm s) (eq (Term.var 0) (Term.rename Nat.succ s))) := by
    simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ]
      using hrefl
  have h := BProv_eqElim (B := B) (G := G) (s := s) (t := t)
    (a := eq (Term.var 0) (Term.rename Nat.succ s)) heq ha
  simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ] using h

/-- PA relative provability is closed under transitivity of term equality. -/
theorem BProv_eqTrans {B : Formula → Prop} {G : List Formula}
    {s t u : Term}
    (hst : BProv B G (eq s t)) (htu : BProv B G (eq t u)) :
    BProv B G (eq s u) := by
  have ha : BProv B G
      (subst (instTerm t) (eq (Term.rename Nat.succ s) (Term.var 0))) := by
    simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ]
      using hst
  have h := BProv_eqElim (B := B) (G := G) (s := t) (t := u)
    (a := eq (Term.rename Nat.succ s) (Term.var 0)) htu ha
  simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ] using h

/-- PA equality is congruent through an arbitrary one-hole term context.  The
hole is de Bruijn variable `0`; other ambient variables are represented by the
usual shifted indices of the context term. -/
theorem BProv_eq_congr_term {B : Formula → Prop} {G : List Formula}
    {s t : Term} (c : Term) (heq : BProv B G (eq s t)) :
    BProv B G (eq
      (Term.subst (instTerm s) c)
      (Term.subst (instTerm t) c)) := by
  have hrefl : BProv B G
      (eq (Term.subst (instTerm s) c)
        (Term.subst (instTerm s) c)) :=
    BProv_eqRefl (Term.subst (instTerm s) c)
  have ha : BProv B G
      (subst (instTerm s)
        (eq (Term.rename Nat.succ (Term.subst (instTerm s) c)) c)) := by
    simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ]
      using hrefl
  have h := BProv_eqElim (B := B) (G := G) (s := s) (t := t)
    (a := eq
      (Term.rename Nat.succ (Term.subst (instTerm s) c)) c)
    heq ha
  simpa [subst, instTerm, Term.subst, term_subst_instTerm_rename_succ] using h

/-- PA equality is congruent under successor. -/
theorem BProv_eq_congr_succ {B : Formula → Prop} {G : List Formula}
    {s t : Term} (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.succ s) (Term.succ t)) := by
  simpa [Term.subst, instTerm] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t) (Term.succ (Term.var 0)) heq

/-- PA equality is congruent in the left argument of addition. -/
theorem BProv_eq_congr_add_left {B : Formula → Prop} {G : List Formula}
    {s t : Term} (u : Term) (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.add s u) (Term.add t u)) := by
  simpa [Term.subst, instTerm, term_subst_instTerm_rename_succ] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t)
      (Term.add (Term.var 0) (Term.rename Nat.succ u)) heq

/-- PA equality is congruent in the right argument of addition. -/
theorem BProv_eq_congr_add_right {B : Formula → Prop} {G : List Formula}
    (u : Term) {s t : Term} (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.add u s) (Term.add u t)) := by
  simpa [Term.subst, instTerm, term_subst_instTerm_rename_succ] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t)
      (Term.add (Term.rename Nat.succ u) (Term.var 0)) heq

/-- PA equality is congruent in both arguments of addition. -/
theorem BProv_eq_congr_add {B : Formula → Prop} {G : List Formula}
    {s t u v : Term}
    (hst : BProv B G (eq s t)) (huv : BProv B G (eq u v)) :
    BProv B G (eq (Term.add s u) (Term.add t v)) :=
  BProv_eqTrans (BProv_eq_congr_add_left u hst)
    (BProv_eq_congr_add_right t huv)

/-- PA equality is congruent in the left argument of multiplication. -/
theorem BProv_eq_congr_mul_left {B : Formula → Prop} {G : List Formula}
    {s t : Term} (u : Term) (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.mul s u) (Term.mul t u)) := by
  simpa [Term.subst, instTerm, term_subst_instTerm_rename_succ] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t)
      (Term.mul (Term.var 0) (Term.rename Nat.succ u)) heq

/-- PA equality is congruent in the right argument of multiplication. -/
theorem BProv_eq_congr_mul_right {B : Formula → Prop} {G : List Formula}
    (u : Term) {s t : Term} (heq : BProv B G (eq s t)) :
    BProv B G (eq (Term.mul u s) (Term.mul u t)) := by
  simpa [Term.subst, instTerm, term_subst_instTerm_rename_succ] using
    BProv_eq_congr_term (B := B) (G := G)
      (s := s) (t := t)
      (Term.mul (Term.rename Nat.succ u) (Term.var 0)) heq

/-- PA equality is congruent in both arguments of multiplication. -/
theorem BProv_eq_congr_mul {B : Formula → Prop} {G : List Formula}
    {s t u v : Term}
    (hst : BProv B G (eq s t)) (huv : BProv B G (eq u v)) :
    BProv B G (eq (Term.mul s u) (Term.mul t v)) :=
  BProv_eqTrans (BProv_eq_congr_mul_left u hst)
    (BProv_eq_congr_mul_right t huv)

/-- A relative PA proof may ignore one extra finite-context assumption. -/
theorem BProv_context_cons {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (h : BProv B G b) : BProv B (a :: G) b :=
  BProv_mono B G (a :: G) b
    (fun _ hx => List.mem_cons.mpr (Or.inr hx)) h

/-- Open one binder in the surrounding context: rename a relative proof by
successor and add the freshly opened body as an assumption. -/
theorem BProv_rename_succ_context_cons_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a b : Formula}
    (h : BProv B G b) :
    BProv B (a :: G.map (rename Nat.succ)) (rename Nat.succ b) :=
  BProv_context_cons (B := B)
    (BProv_rename_of_sentences hB h Nat.succ)

/-- Add an ordinary assumption, then open one binder around the enlarged
context.  Only the binder opening shifts the transported formula. -/
theorem BProv_lift_context_cons_then_open_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {outer inner phi : Formula}
    (hphi : BProv B G phi) :
    BProv B
      (inner :: (outer :: G).map (rename Nat.succ))
      (rename Nat.succ phi) :=
  BProv_rename_succ_context_cons_of_sentences
    (B := B) hB (a := inner)
    (BProv_context_cons (B := B) (a := outer) hphi)

/-- Relative PA provability is closed under implication introduction. -/
theorem BProv_impI {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (h : BProv B (a :: G) b) :
    BProv B G (imp a b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  rw [List.mem_append] at hx
  rcases hx with hx | hx
  · exact List.mem_cons.mpr
      (Or.inr (List.mem_append.mpr (Or.inl hx)))
  · rw [List.mem_cons] at hx
    rcases hx with hx | hx
    · exact List.mem_cons.mpr (Or.inl hx)
    · exact List.mem_cons.mpr
        (Or.inr (List.mem_append.mpr (Or.inr hx)))

/-- Implication introduction with a fixed prefix of PA assumptions. -/
theorem BProv_impI_after_prefix {B : Formula → Prop}
    {Γ Δ : List Formula} {a b : Formula}
    (h : BProv B (Γ ++ a :: Δ) b) :
    BProv B (Γ ++ Δ) (imp a b) := by
  rcases h with ⟨L, hL, hp⟩
  refine ⟨L, hL, ?_⟩
  apply Prov.P_impI
  apply Prov_weaken hp
  intro x hx
  simp only [List.mem_append, List.mem_cons] at hx ⊢
  grind

/-- Relative PA provability is closed under conjunction introduction. -/
theorem BProv_andI {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (ha : BProv B G a) (hb : BProv B G b) :
    BProv B G (and a b) := by
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨La ++ Lb, ?_, ?_⟩
  · intro x hx
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hLa x hx
    · exact hLb x hx
  · apply Prov.P_andI
    · apply Prov_weaken hpa
      intro x hx
      rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.mem_append.mpr (Or.inl hx))
      · exact Or.inr hx
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx ⊢
      rcases hx with hx | hx
      · exact Or.inl (List.mem_append.mpr (Or.inr hx))
      · exact Or.inr hx

/-- Relative PA provability is closed under bottom elimination. -/
theorem BProv_botE {B : Formula → Prop} {G : List Formula} {a : Formula}
    (hbot : BProv B G bot) : BProv B G a := by
  rcases hbot with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_botE _ a hp⟩

/-- Relative PA provability is closed under the first conjunction projection. -/
theorem BProv_andE1 {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (h : BProv B G (and a b)) : BProv B G a := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_andE1 _ a b hp⟩

/-- Relative PA provability is closed under the second conjunction projection. -/
theorem BProv_andE2 {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (h : BProv B G (and a b)) : BProv B G b := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_andE2 _ a b hp⟩

/-- Relative PA provability is closed under left disjunction introduction. -/
theorem BProv_orI1 {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (ha : BProv B G a) : BProv B G (or a b) := by
  rcases ha with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_orI1 _ a b hp⟩

/-- Relative PA provability is closed under right disjunction introduction. -/
theorem BProv_orI2 {B : Formula → Prop} {G : List Formula}
    {a b : Formula} (hb : BProv B G b) : BProv B G (or a b) := by
  rcases hb with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_orI2 _ a b hp⟩

/-- Relative PA provability is closed under disjunction elimination. -/
theorem BProv_orE {B : Formula → Prop} {G : List Formula}
    {a b c : Formula}
    (hor : BProv B G (or a b))
    (ha : BProv B (a :: G) c)
    (hb : BProv B (b :: G) c) : BProv B G c := by
  rcases hor with ⟨Lo, hLo, hpo⟩
  rcases ha with ⟨La, hLa, hpa⟩
  rcases hb with ⟨Lb, hLb, hpb⟩
  refine ⟨Lo ++ La ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_orE _ a b c
    · apply Prov_weaken hpo
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpa
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      grind

/-- Relative PA provability is closed under universal elimination. -/
theorem BProv_allE {B : Formula → Prop} {G : List Formula}
    {a : Formula} {t : Term} (h : BProv B G (all a)) :
    BProv B G (subst (instTerm t) a) := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_allE _ _ t hp⟩

/-- Relative PA provability is closed under existential introduction. -/
theorem BProv_exI {B : Formula → Prop} {G : List Formula}
    {a : Formula} {t : Term}
    (h : BProv B G (subst (instTerm t) a)) :
    BProv B G (ex a) := by
  rcases h with ⟨L, hL, hp⟩
  exact ⟨L, hL, Prov.P_exI _ _ t hp⟩

/-- Universal introduction for relative PA proofs whose theory axioms are
sentences. -/
theorem BProv_allI_of_sentences {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a : Formula}
    (h : BProv B (G.map (rename Nat.succ)) a) :
    BProv B G (all a) := by
  rcases h with ⟨L, hL, hp⟩
  have hLmap : L.map (rename Nat.succ) = L := by
    calc
      L.map (rename Nat.succ) = L.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (hB x (hL x hx)) Nat.succ
      _ = L := by simp
  refine ⟨L, hL, ?_⟩
  apply Prov.P_allI
  apply Prov_weaken hp
  intro x hx
  simp only [List.map_append, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · exact Or.inl (by simpa [hLmap] using hx)
  · exact Or.inr hx

/-- Introduce a finite universal closure from a closed-context relative PA
proof.  This is the `BProv` companion to `closeN`, and is useful when a
sealed formula contains more outer closures than the mathematically relevant
body. -/
theorem BProv_closeN_nil_of_sentences {B : Formula → Prop} (hB : Sentences B) :
    ∀ n {phi : Formula}, BProv B [] phi → BProv B [] (closeN n phi) := by
  intro n
  induction n with
  | zero =>
      intro phi h
      simpa [closeN] using h
  | succ n ih =>
      intro phi h
      exact ih (phi := all phi)
        (BProv_allI_of_sentences (B := B) hB (G := []) (a := phi)
          (by simpa using h))

/-- Existential elimination for relative PA proofs whose theory axioms are
sentences. -/
theorem BProv_exE_of_sentences {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {a c : Formula}
    (hex : BProv B G (ex a))
    (hbody : BProv B (a :: G.map (rename Nat.succ)) (rename Nat.succ c)) :
    BProv B G c := by
  rcases hex with ⟨Le, hLe, hpe⟩
  rcases hbody with ⟨Lb, hLb, hpb⟩
  have hLbmap : Lb.map (rename Nat.succ) = Lb := by
    calc
      Lb.map (rename Nat.succ) = Lb.map (fun x => x) := by
        apply List.map_congr_left
        intro x hx
        exact rename_eq_of_sentence (hB x (hLb x hx)) Nat.succ
      _ = Lb := by simp
  refine ⟨Le ++ Lb, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_append] at hx
    grind
  · apply Prov.P_exE _ a c
    · apply Prov_weaken hpe
      intro x hx
      simp only [List.mem_append] at hx ⊢
      grind
    · apply Prov_weaken hpb
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · apply List.mem_cons.mpr
        apply Or.inr
        simp only [List.map_append, List.mem_append]
        apply Or.inl
        exact Or.inr (by simpa [hLbmap] using hx)
      · rw [List.mem_cons] at hx
        rcases hx with hx | hx
        · exact List.mem_cons.mpr (Or.inl hx)
        · apply List.mem_cons.mpr
          apply Or.inr
          simp only [List.map_append, List.mem_append]
          exact Or.inr hx

/-- Instantiate every quantifier in a finite universal closure by a PA-variable
renaming.

The side condition says that `k` really closes all free variables of `phi`.
This is the syntactic counterpart of the semantic `seal_valid` lemma and is
the workhorse for using sealed PA axiom-schema instances without hiding the
de Bruijn bookkeeping. -/
theorem BProv_closeN_allE_rename {B : Formula → Prop} {G : List Formula} :
    ∀ (k : Nat) (phi : Formula) (r : Nat → Nat),
      (∀ n, Free n phi → n < k) →
      BProv B G (closeN k phi) →
      BProv B G (rename r phi) := by
  intro k
  induction k with
  | zero =>
      intro phi r hfree h
      have hsent : Sentence phi := by
        intro n hn
        have hlt := hfree n hn
        omega
      simpa [closeN, rename_eq_of_sentence hsent r] using h
  | succ k ih =>
      intro phi r hfree h
      let tail : Nat → Nat := fun n => r (n+1)
      have hclosed : BProv B G (rename tail (all phi)) := by
        apply ih (all phi) tail
        · intro n hn
          have hlt := hfree (n+1) hn
          omega
        · simpa [closeN] using h
      have hAll : BProv B G (all (rename (SetTheory.up tail) phi)) := by
        simpa [rename, tail] using hclosed
      have hInst : BProv B G
          (subst (instTerm (Term.var (r 0)))
            (rename (SetTheory.up tail) phi)) :=
        BProv_allE (B := B) (G := G)
          (a := rename (SetTheory.up tail) phi)
          (t := Term.var (r 0)) hAll
      have htarget :
          subst (instTerm (Term.var (r 0)))
              (rename (SetTheory.up tail) phi) =
            rename r phi := by
        calc
          subst (instTerm (Term.var (r 0)))
              (rename (SetTheory.up tail) phi) =
              rename (SetTheory.inst (r 0))
                (rename (SetTheory.up tail) phi) := by
                exact subst_instTerm_var
                  (rename (SetTheory.up tail) phi) (r 0)
          _ = rename
              (fun n => SetTheory.inst (r 0) (SetTheory.up tail n)) phi := by
                exact rename_comp phi (SetTheory.inst (r 0))
                  (SetTheory.up tail)
          _ = rename r phi := by
                apply rename_ext
                intro n
                cases n with
                | zero => rfl
                | succ n => rfl
      simpa [htarget] using hInst

/-- Use a sealed PA formula at any variable-renamed instance of its body. -/
theorem BProv_sealPA_allE_rename {B : Formula → Prop} {G : List Formula}
    (phi : Formula) (r : Nat → Nat)
    (h : BProv B G (sealPA phi)) :
    BProv B G (rename r phi) :=
  BProv_closeN_allE_rename (bound phi) phi r
    (fun n hn => free_lt_bound phi n hn) h

theorem soundness_BProv {α : Type u} (M : PreModel α) {B : Formula → Prop}
    {G : List Formula} {phi : Formula} (h : BProv B G phi) :
    ∀ e : Nat → α, (∀ b, B b → Sat M e b) →
      (∀ g, g ∈ G → Sat M e g) → Sat M e phi := by
  intro e hB hG
  rcases h with ⟨L, hL, hprov⟩
  exact soundness M hprov e (fun x hx => by
    rw [List.mem_append] at hx
    rcases hx with hx | hx
    · exact hB x (hL x hx)
    · exact hG x hx)

/-- A relative derivation remains valid after prepending any finite block of
local assumptions.  This packages repeated `BProv_context_cons` chains. -/
theorem BProv_context_prefix {B : Formula → Prop}
    (pre : List Formula) {G : List Formula} {phi : Formula}
    (hphi : BProv B G phi) : BProv B (pre ++ G) phi := by
  induction pre with
  | nil => exact hphi
  | cons head tail ih =>
      exact BProv_context_cons (a := head) ih

/-- Inference-friendly specialization for the frequent two-assumption case. -/
theorem BProv_context_two {B : Formula → Prop}
    {G : List Formula} {first second phi : Formula}
    (hphi : BProv B G phi) : BProv B (first :: second :: G) phi :=
  BProv_context_prefix [first, second] hphi

/-- Inference-friendly specialization for three opened assumptions. -/
theorem BProv_context_three {B : Formula → Prop}
    {G : List Formula} {first second third phi : Formula}
    (hphi : BProv B G phi) :
    BProv B (first :: second :: third :: G) phi :=
  BProv_context_prefix [first, second, third] hphi

/-- Add `n` existential binders around `body`. -/
def iterEx : Nat → Formula → Formula
  | 0, body => body
  | n + 1, body => ex (iterEx n body)

/-- Rename a formula once for every witness binder that has been opened. -/
def iterRenameSucc : Nat → Formula → Formula
  | 0, phi => phi
  | n + 1, phi => iterRenameSucc n (rename Nat.succ phi)

/-- Rename an entire context once for every newly opened binder.  Its
recursive shape matches repeated applications of
`BProv_rename_of_sentences`. -/
def iterRenameContextSucc : Nat → List Formula → List Formula
  | 0, G => G
  | n + 1, G => iterRenameContextSucc n (G.map (rename Nat.succ))

/-- Iterated admissibility of successor renaming.  This packages the common
pattern of naming two or three consecutive one-step renamed derivations. -/
theorem BProv_iterRenameSucc_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    (n : Nat) {G : List Formula} {phi : Formula}
    (hphi : BProv B G phi) :
    BProv B (iterRenameContextSucc n G) (iterRenameSucc n phi) := by
  induction n generalizing G phi with
  | zero => exact hphi
  | succ n ih =>
      simp only [iterRenameContextSucc, iterRenameSucc]
      exact ih (BProv_rename_of_sentences (B := B) hB hphi Nat.succ)

/-- Add freshly opened assumptions in outside-in order.  In particular,
`openedContext [outer, inner] G` is
`inner :: (outer :: G.map (rename Nat.succ)).map (rename Nat.succ)`. -/
def openedContext : List Formula → List Formula → List Formula
  | [], G => G
  | body :: rest, G =>
      openedContext rest (body :: G.map (rename Nat.succ))

/-- Lift through any sequence of freshly opened assumptions.  The bodies may
come from different existential theorems; only their opening order matters. -/
theorem BProv_lift_openedContext_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    (bodies : List Formula) {G : List Formula} {phi : Formula}
    (hphi : BProv B G phi) :
    BProv B (openedContext bodies G)
      (iterRenameSucc bodies.length phi) := by
  induction bodies generalizing G phi with
  | nil => exact hphi
  | cons body rest ih =>
      simp only [openedContext, List.length_cons, iterRenameSucc]
      apply ih
      exact BProv_rename_succ_context_cons_of_sentences
        (B := B) hB (a := body) hphi

/-- The finite context visible after eliminating `iterEx n body` over `G`.

For example, opening two witnesses yields
`body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ)`.
The recursive definition follows the actual outside-in elimination order, so
clients do not have to reconstruct the shifts by hand. -/
def openedExContext : Nat → Formula → List Formula → List Formula
  | 0, _, G => G
  | n + 1, body, G =>
      openedExContext n body
        (iterEx n body :: G.map (rename Nat.succ))

/-- Eliminate an arbitrary finite block of existential witnesses in one
step.  All de Bruijn shifting is exposed by `openedExContext` and
`iterRenameSucc`, rather than hidden in a client-specific proof. -/
theorem BProv_iterExE_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    (n : Nat) {G : List Formula} {body target : Formula}
    (hex : BProv B G (iterEx n body))
    (hopened : BProv B (openedExContext n body G)
      (iterRenameSucc n target)) :
    BProv B G target := by
  induction n generalizing G target with
  | zero => exact hopened
  | succ n ih =>
      let C : List Formula :=
        iterEx n body :: G.map (rename Nat.succ)
      have hinner : BProv B C (iterEx n body) :=
        BProv_ass (B := B) (G := C) (by simp [C])
      have htargetC : BProv B C (rename Nat.succ target) :=
        ih (G := C) (target := rename Nat.succ target) hinner
          (by simpa [openedExContext, iterRenameSucc, C] using hopened)
      exact BProv_exE_of_sentences (B := B) hB
        (by simpa [iterEx] using hex)
        (by simpa [C] using htargetC)

/-- Two-witness specialization used by paired graph witnesses. -/
theorem BProv_two_exE_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {body target : Formula}
    (hex : BProv B G (ex (ex body)))
    (hopened : BProv B
      (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
      (rename Nat.succ (rename Nat.succ target))) :
    BProv B G target := by
  exact BProv_iterExE_of_sentences (B := B) hB 2 hex hopened

/-- Three-witness specialization used by multiplication graphs. -/
theorem BProv_three_exE_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {body target : Formula}
    (hex : BProv B G (ex (ex (ex body))))
    (hopened : BProv B
      (body :: List.map (rename Nat.succ)
        (ex body :: List.map (rename Nat.succ)
          (ex (ex body) :: List.map (rename Nat.succ) G)))
      (rename Nat.succ (rename Nat.succ (rename Nat.succ target)))) :
    BProv B G target := by
  exact BProv_iterExE_of_sentences (B := B) hB 3 hex hopened

/-- Lift through the two binders of a paired existential witness. -/
theorem BProv_lift_two_opened_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {body phi : Formula}
    (hphi : BProv B G phi) :
    BProv B
      (body :: (ex body :: G.map (rename Nat.succ)).map (rename Nat.succ))
      (rename Nat.succ (rename Nat.succ phi)) := by
  exact BProv_lift_openedContext_of_sentences
    (B := B) hB [ex body, body] hphi

/-- Two-step specialization for distinct outer and inner witness bodies. -/
theorem BProv_lift_two_contexts_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {outer inner phi : Formula}
    (hphi : BProv B G phi) :
    BProv B
      (inner :: (outer :: G.map (rename Nat.succ)).map (rename Nat.succ))
      (rename Nat.succ (rename Nat.succ phi)) := by
  exact BProv_lift_openedContext_of_sentences
    (B := B) hB [outer, inner] hphi

/-- Three-step specialization for distinct witness bodies. -/
theorem BProv_lift_three_contexts_of_sentences
    {B : Formula → Prop} (hB : Sentences B)
    {G : List Formula} {outer middle inner phi : Formula}
    (hphi : BProv B G phi) :
    BProv B
      (inner :: List.map (rename Nat.succ)
        (middle :: List.map (rename Nat.succ)
          (outer :: List.map (rename Nat.succ) G)))
      (rename Nat.succ (rename Nat.succ (rename Nat.succ phi))) := by
  exact BProv_lift_openedContext_of_sentences
    (B := B) hB [outer, middle, inner] hphi

/-- Substituting the three freshly opened witness variables cancels the three
binder-aware successor renamings.  The statement is formula-generic and is
shared by multiplication graph constructions. -/
theorem subst_three_witnesses_rename_three_succ
    (phi : Formula) :
    subst (instTerm (Term.var 0))
        (subst (Term.upSubst (instTerm (Term.var 1)))
          (subst
            (Term.upSubst
              (Term.upSubst (instTerm (Term.var 2))))
            (rename
              (SetTheory.up (SetTheory.up (SetTheory.up Nat.succ)))
              (rename
                (SetTheory.up (SetTheory.up (SetTheory.up Nat.succ)))
                (rename
                  (SetTheory.up (SetTheory.up (SetTheory.up Nat.succ)))
                  phi))))) =
      phi := by
  rw [subst_comp, subst_comp, subst_rename, subst_rename, subst_rename]
  calc
    _ = subst (fun n ↦ Term.var n) phi := by
      apply subst_ext_free
      intro n hn
      rcases n with _ | _ | _ | n <;> rfl
    _ = phi := subst_id phi

/-! ### Arithmetic relation macros for the reverse interpretation -/

def leAt (a b : Nat) : Formula :=
  ex (eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.var (b+1)))

/-- Term-parametric non-strict order.  This is the same relation as `leAt`,
but the compared values may be arbitrary PA terms in the ambient context. -/
def leTermAt (a b : Term) : Formula :=
  ex (eq (Term.add (Term.rename Nat.succ a) (Term.var 0))
    (Term.rename Nat.succ b))

theorem subst_leTermAt (σ : Nat → Term) (a b : Term) :
    subst σ (leTermAt a b) =
      leTermAt (Term.subst σ a) (Term.subst σ b) := by
  simp [leTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_leTermAt
    (r : Nat → Nat) (a b : Term) :
    rename r (leTermAt a b) =
      leTermAt (Term.rename r a) (Term.rename r b) := by
  rw [← subst_var_rename, subst_leTermAt]
  simp only [term_subst_var_rename]

/-- Bounded order against a closed standard numeral.  This is intentionally only
the formula macro; PA proofs that relate it to `leAt` are kept as separate
lemmas. -/
def leConstAt (a n : Nat) : Formula :=
  ex (eq (Term.add (Term.var (a+1)) (Term.var 0)) (Term.numeral n))

def ltAt (a b : Nat) : Formula :=
  ex (eq (Term.add (Term.var (a+1)) (Term.succ (Term.var 0))) (Term.var (b+1)))

/-- Term-parametric strict order.  This is the same relation as `ltAt`, but
the compared values may be arbitrary PA terms in the ambient context. -/
def ltTermAt (a b : Term) : Formula :=
  ex (eq (Term.add (Term.rename Nat.succ a) (Term.succ (Term.var 0)))
    (Term.rename Nat.succ b))

theorem subst_ltTermAt (σ : Nat → Term) (a b : Term) :
    subst σ (ltTermAt a b) =
      ltTermAt (Term.subst σ a) (Term.subst σ b) := by
  simp [ltTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_ltTermAt
    (r : Nat → Nat) (a b : Term) :
    rename r (ltTermAt a b) =
      ltTermAt (Term.rename r a) (Term.rename r b) := by
  rw [← subst_var_rename, subst_ltTermAt]
  simp only [term_subst_var_rename]

def dvdAt (a b : Nat) : Formula :=
  ex (eq (Term.mul (Term.var (a+1)) (Term.var 0)) (Term.var (b+1)))

/-- Fully term-parametric divisibility.  The existential witness is an
ordinary quotient satisfying `divisor * quotient = value`. -/
def dvdTermTermAt (divisor value : Term) : Formula :=
  ex (eq
    (Term.mul (Term.rename Nat.succ divisor) (Term.var 0))
    (Term.rename Nat.succ value))

theorem subst_dvdTermTermAt
    (σ : Nat → Term) (divisor value : Term) :
    subst σ (dvdTermTermAt divisor value) =
      dvdTermTermAt
        (Term.subst σ divisor)
        (Term.subst σ value) := by
  simp [dvdTermTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_dvdTermTermAt
    (r : Nat → Nat) (divisor value : Term) :
    rename r (dvdTermTermAt divisor value) =
      dvdTermTermAt
        (Term.rename r divisor)
        (Term.rename r value) := by
  rw [← subst_var_rename, subst_dvdTermTermAt]
  simp only [term_subst_var_rename]

/-- A term is divisible by every positive value through a term bound.

The bound variable is represented as a predecessor: for every `q < bound`,
the successor `q + 1` divides `multiple`.  This avoids a spurious divisibility
obligation at zero and is the induction-facing common-multiple invariant used
for beta-modulus gaps. -/
def commonMultipleThroughTermAt (bound multiple : Term) : Formula :=
  all (imp
    (ltTermAt (Term.var 0) (Term.rename Nat.succ bound))
    (dvdTermTermAt (Term.succ (Term.var 0))
      (Term.rename Nat.succ multiple)))

theorem subst_commonMultipleThroughTermAt
    (σ : Nat → Term) (bound multiple : Term) :
    subst σ (commonMultipleThroughTermAt bound multiple) =
      commonMultipleThroughTermAt
        (Term.subst σ bound)
        (Term.subst σ multiple) := by
  simp [commonMultipleThroughTermAt, subst_ltTermAt,
    subst_dvdTermTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_commonMultipleThroughTermAt
    (r : Nat → Nat) (bound multiple : Term) :
    rename r (commonMultipleThroughTermAt bound multiple) =
      commonMultipleThroughTermAt
        (Term.rename r bound)
        (Term.rename r multiple) := by
  rw [← subst_var_rename, subst_commonMultipleThroughTermAt]
  simp only [term_subst_var_rename]

/-- Existence of a common multiple for all positive values through a term
bound.  The witness is explicit and the body is exactly
`commonMultipleThroughTermAt`; no construction is built into the relation. -/
def commonMultipleExistsTermAt (bound : Term) : Formula :=
  ex (commonMultipleThroughTermAt
    (Term.rename Nat.succ bound) (Term.var 0))

/-- Body exposed after opening `commonMultipleExistsTermAt`. -/
def commonMultipleExistsTermAtBody (bound : Term) : Formula :=
  commonMultipleThroughTermAt
    (Term.rename Nat.succ bound) (Term.var 0)

/-- Common-multiple invariant with positivity stated explicitly. -/
def positiveCommonMultipleThroughTermAt
    (bound multiple : Term) : Formula :=
  and (ltTermAt Term.zero multiple)
    (commonMultipleThroughTermAt bound multiple)

theorem subst_positiveCommonMultipleThroughTermAt
    (σ : Nat → Term) (bound multiple : Term) :
    subst σ (positiveCommonMultipleThroughTermAt bound multiple) =
      positiveCommonMultipleThroughTermAt
        (Term.subst σ bound) (Term.subst σ multiple) := by
  simp [positiveCommonMultipleThroughTermAt, subst, subst_ltTermAt,
    Term.subst,
    subst_commonMultipleThroughTermAt]

theorem rename_positiveCommonMultipleThroughTermAt
    (r : Nat → Nat) (bound multiple : Term) :
    rename r (positiveCommonMultipleThroughTermAt bound multiple) =
      positiveCommonMultipleThroughTermAt
        (Term.rename r bound) (Term.rename r multiple) := by
  rw [← subst_var_rename, subst_positiveCommonMultipleThroughTermAt]
  simp only [term_subst_var_rename]

/-- Existence of a positive common multiple through a term bound. -/
def positiveCommonMultipleExistsTermAt (bound : Term) : Formula :=
  ex (positiveCommonMultipleThroughTermAt
    (Term.rename Nat.succ bound) (Term.var 0))

/-- Body exposed after opening `positiveCommonMultipleExistsTermAt`. -/
def positiveCommonMultipleExistsTermAtBody (bound : Term) : Formula :=
  positiveCommonMultipleThroughTermAt
    (Term.rename Nat.succ bound) (Term.var 0)

theorem subst_positiveCommonMultipleExistsTermAt
    (σ : Nat → Term) (bound : Term) :
    subst σ (positiveCommonMultipleExistsTermAt bound) =
      positiveCommonMultipleExistsTermAt (Term.subst σ bound) := by
  simp [positiveCommonMultipleExistsTermAt,
    subst_positiveCommonMultipleThroughTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_positiveCommonMultipleExistsTermAt
    (r : Nat → Nat) (bound : Term) :
    rename r (positiveCommonMultipleExistsTermAt bound) =
      positiveCommonMultipleExistsTermAt (Term.rename r bound) := by
  rw [← subst_var_rename, subst_positiveCommonMultipleExistsTermAt]
  simp only [term_subst_var_rename]

/-- A fixed beta-coding step for copying remainders from `sourceCode` below
`bound`: it carries every required common divisor and is larger than every
possible source remainder. -/
def betaCodingStepTermAt
    (bound sourceCode step : Term) : Formula :=
  and (commonMultipleThroughTermAt bound step)
    (leTermAt (Term.succ sourceCode) step)

theorem subst_betaCodingStepTermAt
    (σ : Nat → Term) (bound sourceCode step : Term) :
    subst σ (betaCodingStepTermAt bound sourceCode step) =
      betaCodingStepTermAt
        (Term.subst σ bound) (Term.subst σ sourceCode)
        (Term.subst σ step) := by
  simp [betaCodingStepTermAt, subst, subst_commonMultipleThroughTermAt,
    Term.subst,
    subst_leTermAt]

theorem rename_betaCodingStepTermAt
    (r : Nat → Nat) (bound sourceCode step : Term) :
    rename r (betaCodingStepTermAt bound sourceCode step) =
      betaCodingStepTermAt
        (Term.rename r bound) (Term.rename r sourceCode)
        (Term.rename r step) := by
  rw [← subst_var_rename, subst_betaCodingStepTermAt]
  simp only [term_subst_var_rename]

/-- Existence of a fixed beta-coding step. -/
def betaCodingStepExistsTermAt
    (bound sourceCode : Term) : Formula :=
  ex (betaCodingStepTermAt
    (Term.rename Nat.succ bound)
    (Term.rename Nat.succ sourceCode)
    (Term.var 0))

/-- Body exposed after opening a fixed beta-coding step witness. -/
def betaCodingStepExistsTermAtBody
    (bound sourceCode : Term) : Formula :=
  betaCodingStepTermAt
    (Term.rename Nat.succ bound)
    (Term.rename Nat.succ sourceCode)
    (Term.var 0)

theorem subst_betaCodingStepExistsTermAt
    (σ : Nat → Term) (bound sourceCode : Term) :
    subst σ (betaCodingStepExistsTermAt bound sourceCode) =
      betaCodingStepExistsTermAt
        (Term.subst σ bound) (Term.subst σ sourceCode) := by
  simp [betaCodingStepExistsTermAt, subst_betaCodingStepTermAt,
    subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_betaCodingStepExistsTermAt
    (r : Nat → Nat) (bound sourceCode : Term) :
    rename r (betaCodingStepExistsTermAt bound sourceCode) =
      betaCodingStepExistsTermAt
        (Term.rename r bound) (Term.rename r sourceCode) := by
  rw [← subst_var_rename, subst_betaCodingStepExistsTermAt]
  simp only [term_subst_var_rename]

/-- A fixed beta-coding step for prepending one entry to a copied source
prefix.  Besides the common-divisor invariant, it separately bounds the
source code and the new head output. -/
def betaPrependCodingStepTermAt
    (bound sourceCode head step : Term) : Formula :=
  and (commonMultipleThroughTermAt bound step)
    (and (leTermAt (Term.succ sourceCode) step)
      (leTermAt (Term.succ head) step))

theorem subst_betaPrependCodingStepTermAt
    (σ : Nat → Term) (bound sourceCode head step : Term) :
    subst σ (betaPrependCodingStepTermAt bound sourceCode head step) =
      betaPrependCodingStepTermAt
        (Term.subst σ bound) (Term.subst σ sourceCode)
        (Term.subst σ head) (Term.subst σ step) := by
  simp [betaPrependCodingStepTermAt, subst,
    subst_commonMultipleThroughTermAt, subst_leTermAt, Term.subst]

theorem rename_betaPrependCodingStepTermAt
    (r : Nat → Nat) (bound sourceCode head step : Term) :
    rename r (betaPrependCodingStepTermAt bound sourceCode head step) =
      betaPrependCodingStepTermAt
        (Term.rename r bound) (Term.rename r sourceCode)
        (Term.rename r head) (Term.rename r step) := by
  rw [← subst_var_rename, subst_betaPrependCodingStepTermAt]
  simp only [term_subst_var_rename]

/-- Existence of a fixed beta-prepend coding step. -/
def betaPrependCodingStepExistsTermAt
    (bound sourceCode head : Term) : Formula :=
  ex (betaPrependCodingStepTermAt
    (Term.rename Nat.succ bound)
    (Term.rename Nat.succ sourceCode)
    (Term.rename Nat.succ head)
    (Term.var 0))

/-- Body exposed after opening a beta-prepend coding-step witness. -/
def betaPrependCodingStepExistsTermAtBody
    (bound sourceCode head : Term) : Formula :=
  betaPrependCodingStepTermAt
    (Term.rename Nat.succ bound)
    (Term.rename Nat.succ sourceCode)
    (Term.rename Nat.succ head)
    (Term.var 0)

theorem subst_betaPrependCodingStepExistsTermAt
    (σ : Nat → Term) (bound sourceCode head : Term) :
    subst σ (betaPrependCodingStepExistsTermAt bound sourceCode head) =
      betaPrependCodingStepExistsTermAt
        (Term.subst σ bound) (Term.subst σ sourceCode)
        (Term.subst σ head) := by
  simp [betaPrependCodingStepExistsTermAt,
    subst_betaPrependCodingStepTermAt,
    subst, Term.subst, Term.upSubst, Term.subst_rename_succ_up]

theorem rename_betaPrependCodingStepExistsTermAt
    (r : Nat → Nat) (bound sourceCode head : Term) :
    rename r (betaPrependCodingStepExistsTermAt bound sourceCode head) =
      betaPrependCodingStepExistsTermAt
        (Term.rename r bound) (Term.rename r sourceCode)
        (Term.rename r head) := by
  rw [← subst_var_rename, subst_betaPrependCodingStepExistsTermAt]
  simp only [term_subst_var_rename]

def eqConstAt (a n : Nat) : Formula :=
  eq (Term.var a) (Term.numeral n)

/-- PA proves that some value is equal to any fixed standard numeral.  This is
the small syntactic witness used when a later proof wants to temporarily open a
fresh variable with a closed value. -/
theorem BProv_exists_eqConstAt {B : Formula → Prop} {G : List Formula}
    (n : Nat) : BProv B G (ex (eqConstAt 0 n)) := by
  have hbody : BProv B G
      (subst (instTerm (Term.numeral n)) (eqConstAt 0 n)) := by
    simpa [eqConstAt, subst, instTerm, Term.subst] using
      (BProv_eqRefl (B := B) (G := G) (Term.numeral n))
  exact BProv_exI (B := B) (G := G) hbody

def zeroAt (a : Nat) : Formula := eqConstAt a 0

def oneAt (a : Nat) : Formula := eqConstAt a 1

def twoAt (a : Nat) : Formula := eqConstAt a 2

def nonzeroAt (a : Nat) : Formula :=
  ex (eq (Term.succ (Term.var 0)) (Term.var (a+1)))

/-- Slot `a` is the successor of some predecessor. -/
def succPredAt (a : Nat) : Formula :=
  ex (eq (Term.var (a+1)) (Term.succ (Term.var 0)))

/-- The elementary PA case split for a number: zero or a successor. -/
def zeroOrSuccPredAt (a : Nat) : Formula :=
  or (zeroAt a) (succPredAt a)

def boolAt (a : Nat) : Formula :=
  or (zeroAt a) (oneAt a)

/-- Term-parametric boolean predicate: the term is `0` or `1`. -/
def boolTermAt (a : Term) : Formula :=
  or (eq a Term.zero) (eq a (Term.numeral 1))

def doubleEqAt (value half : Nat) : Formula :=
  eq (Term.var value) (Term.add (Term.var half) (Term.var half))

def oddDoubleEqAt (value half : Nat) : Formula :=
  eq (Term.var value) (Term.succ (Term.add (Term.var half) (Term.var half)))

def div2StepAt (value half bit : Nat) : Formula :=
  and (boolAt bit)
    (eq (Term.var value)
      (Term.add (Term.add (Term.var half) (Term.var half)) (Term.var bit)))

/-- Term-parametric binary-halving step: `value = half + half + bit` and
`bit` is boolean. -/
def div2StepTermAt (value half bit : Term) : Formula :=
  and (boolTermAt bit)
    (eq value (Term.add (Term.add half half) bit))

/-- Term-parametric totality predicate for binary halving:
`value` has some half and some boolean output bit satisfying the halving step.

This is only the object-language relation shape; all arithmetic work remains
in the accompanying proof theorems. -/
def div2TotalTermAt (value : Term) : Formula :=
  ex (ex
    (div2StepTermAt (Term.rename (fun n => n+1+1) value)
      (Term.var 1) (Term.var 0)))

def div2TotalAt (value : Nat) : Formula :=
  div2TotalTermAt (Term.var value)

theorem boolTermAt_var (a : Nat) :
    boolTermAt (Term.var a) = boolAt a := by
  simp [boolTermAt, boolAt, zeroAt, oneAt, eqConstAt, Term.numeral]

theorem div2StepTermAt_var (value half bit : Nat) :
    div2StepTermAt (Term.var value) (Term.var half) (Term.var bit) =
      div2StepAt value half bit := by
  simp [div2StepTermAt, div2StepAt, boolTermAt_var]

def remAt (rem value modulus : Nat) : Formula :=
  ex (and
    (ltAt (rem+1) (modulus+1))
    (eq (Term.var (value+1))
      (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
        (Term.var (rem+1)))))

/-- Term-parametric remainder relation.  The remainder may be an arbitrary PA
term, while the dividend and modulus remain slots. -/
def remTermAt (rem : Term) (value modulus : Nat) : Formula :=
  ex (and
    (ltTermAt (Term.rename Nat.succ rem) (Term.var (modulus+1)))
    (eq (Term.var (value+1))
      (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
        (Term.rename Nat.succ rem))))

/-- Fully term-parametric remainder relation.  It is the same bounded
division graph as `remTermAt`, but the remainder, dividend, and modulus are
all PA terms. -/
def remTermTermAt (rem value modulus : Term) : Formula :=
  ex (and
    (ltTermAt (Term.rename Nat.succ rem) (Term.rename Nat.succ modulus))
    (eq (Term.rename Nat.succ value)
      (Term.add (Term.mul (Term.var 0) (Term.rename Nat.succ modulus))
        (Term.rename Nat.succ rem))))

theorem subst_remTermTermAt
    (σ : Nat → Term) (rem value modulus : Term) :
    subst σ (remTermTermAt rem value modulus) =
      remTermTermAt
        (Term.subst σ rem)
        (Term.subst σ value)
        (Term.subst σ modulus) := by
  simp [remTermTermAt, subst_ltTermAt, subst, Term.subst,
    Term.upSubst, Term.subst_rename_succ_up]

theorem rename_remTermTermAt
    (r : Nat → Nat) (rem value modulus : Term) :
    rename r (remTermTermAt rem value modulus) =
      remTermTermAt
        (Term.rename r rem)
        (Term.rename r value)
        (Term.rename r modulus) := by
  rw [← subst_var_rename, subst_remTermTermAt]
  simp only [term_subst_var_rename]

theorem rename_remTermAt
    (r : Nat → Nat) (rem : Term) (value modulus : Nat) :
    rename r (remTermAt rem value modulus) =
      remTermAt (Term.rename r rem) (r value) (r modulus) := by
  simp [remTermAt, rename_ltTermAt, rename, Term.rename,
    Term.rename_comp, SetTheory.up]

theorem ltTermAt_var (a b : Nat) :
    ltTermAt (Term.var a) (Term.var b) = ltAt a b := by
  simp [ltTermAt, ltAt, Term.rename]

theorem leTermAt_var (a b : Nat) :
    leTermAt (Term.var a) (Term.var b) = leAt a b := by
  simp [leTermAt, leAt, Term.rename]

theorem remTermAt_var (rem value modulus : Nat) :
    remTermAt (Term.var rem) value modulus = remAt rem value modulus := by
  simp [remTermAt, remAt, ltTermAt_var, Term.rename]

def remEqAt (rem value modulus : Nat) : Formula :=
  ex (eq (Term.var (value+1))
    (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
      (Term.var (rem+1))))

/-- Term-parametric remainder equation, forgetting the strict bound but keeping
the same quotient witness. -/
def remTermEqAt (rem : Term) (value modulus : Nat) : Formula :=
  ex (eq (Term.var (value+1))
    (Term.add (Term.mul (Term.var 0) (Term.var (modulus+1)))
      (Term.rename Nat.succ rem)))

def betaModTerm (step idx : Nat) : Term :=
  Term.succ (Term.mul (Term.succ (Term.var idx)) (Term.var step))

/-- Fully term-parametric beta modulus term `1 + (idx + 1) * step`. -/
def betaModTermTerm (step idx : Term) : Term :=
  Term.succ (Term.mul (Term.succ idx) step)

theorem term_rename_betaModTermTerm
    (r : Nat → Nat) (step idx : Term) :
    Term.rename r (betaModTermTerm step idx) =
      betaModTermTerm (Term.rename r step) (Term.rename r idx) := by
  rfl

/-- A product is divisible by every beta modulus at an index strictly below a
term bound.  This states only the factor property; construction and inverse
certificates remain separate. -/
def betaPrefixDividesTermAt
    (step bound product : Term) : Formula :=
  all (imp
    (ltTermAt (Term.var 0) (Term.rename Nat.succ bound))
    (dvdTermTermAt
      (betaModTermTerm (Term.rename Nat.succ step) (Term.var 0))
      (Term.rename Nat.succ product)))

theorem subst_betaPrefixDividesTermAt
    (σ : Nat → Term) (step bound product : Term) :
    subst σ (betaPrefixDividesTermAt step bound product) =
      betaPrefixDividesTermAt
        (Term.subst σ step) (Term.subst σ bound)
        (Term.subst σ product) := by
  simp [betaPrefixDividesTermAt, betaModTermTerm,
    subst_ltTermAt, subst_dvdTermTermAt, subst, Term.subst,
    Term.upSubst, Term.subst_rename_succ_up]

theorem rename_betaPrefixDividesTermAt
    (r : Nat → Nat) (step bound product : Term) :
    rename r (betaPrefixDividesTermAt step bound product) =
      betaPrefixDividesTermAt
        (Term.rename r step) (Term.rename r bound)
        (Term.rename r product) := by
  rw [← subst_var_rename, subst_betaPrefixDividesTermAt]
  simp only [term_subst_var_rename]

theorem rename_succ_twice_betaPrefixDividesTermAt
    (step bound product : Term) :
    rename Nat.succ (rename Nat.succ
        (betaPrefixDividesTermAt step bound product)) =
      betaPrefixDividesTermAt
        (Term.rename (fun n => n + 2) step)
        (Term.rename (fun n => n + 2) bound)
        (Term.rename (fun n => n + 2) product) := by
  rw [rename_betaPrefixDividesTermAt, rename_betaPrefixDividesTermAt]
  simp only [Term.rename_comp]

def betaAt (out code step idx : Nat) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
    (remAt (out+1) (code+1) 0))

/-- Term-parametric beta entry.  This is `betaAt` with the output slot allowed
to be an arbitrary PA term. -/
def betaTermAt (out : Term) (code step idx : Nat) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.rename Nat.succ (betaModTerm step idx)))
    (remTermAt (Term.rename Nat.succ out) (code+1) 0))

/-- Fully term-parametric beta entry.  This is the open-term analogue of
`betaTermAt`: output, code, step, and index are all PA terms. -/
def betaTermTermAt (out code step idx : Term) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.rename Nat.succ (betaModTermTerm step idx)))
    (remTermTermAt (Term.rename Nat.succ out)
      (Term.rename Nat.succ code) (Term.var 0)))

theorem subst_betaTermTermAt
    (sigma : Nat → Term) (out code step index : Term) :
    subst sigma (betaTermTermAt out code step index) =
      betaTermTermAt
        (Term.subst sigma out)
        (Term.subst sigma code)
        (Term.subst sigma step)
        (Term.subst sigma index) := by
  simp [betaTermTermAt, betaModTermTerm, remTermTermAt,
    ltTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_betaTermTermAt
    (r : Nat → Nat) (out code step index : Term) :
    rename r (betaTermTermAt out code step index) =
      betaTermTermAt
        (Term.rename r out)
        (Term.rename r code)
        (Term.rename r step)
        (Term.rename r index) := by
  rw [← subst_var_rename, subst_betaTermTermAt]
  simp only [term_subst_var_rename]

/-- Existence of some output for a fully term-parametric beta entry.  This is
only the quantified relation; no division-totality theorem is built into it.
-/
def betaEntryExistsTermAt (code step idx : Term) : Formula :=
  ex (betaTermTermAt (Term.var 0)
    (Term.rename Nat.succ code)
    (Term.rename Nat.succ step)
    (Term.rename Nat.succ idx))

/-- Body exposed after opening a beta-entry output witness. -/
def betaEntryExistsTermAtBody (code step idx : Term) : Formula :=
  betaTermTermAt (Term.var 0)
    (Term.rename Nat.succ code)
    (Term.rename Nat.succ step)
    (Term.rename Nat.succ idx)

theorem betaTermAt_var (out code step idx : Nat) :
    betaTermAt (Term.var out) code step idx = betaAt out code step idx := by
  simp [betaTermAt, betaAt, remTermAt_var, Term.rename]

/-- The term-output beta entry is the fully term-parametric beta entry
specialized to variable code, step, and index slots. -/
theorem betaTermAt_eq_betaTermTermAt_var
    (out : Term) (code step idx : Nat) :
    betaTermAt out code step idx =
      betaTermTermAt out (Term.var code) (Term.var step) (Term.var idx) := by
  simp [betaTermAt, betaTermTermAt, betaModTerm, betaModTermTerm,
    remTermAt, remTermTermAt, ltTermAt, Term.rename]

/-- Term-output beta entry whose sequence index is itself specified by a PA
term.  This generalizes the constant/successor-index wrappers without changing
the raw beta relation: the index term is represented by an explicit witness
slot and an equality proof. -/
def betaTermAtTermIdx (out : Term) (code step : Nat) (idx : Term) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.rename Nat.succ idx))
    (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0))

def betaAtConstIdx (out code step idxValue : Nat) : Formula :=
  ex (and (eqConstAt 0 idxValue) (betaAt (out+1) (code+1) (step+1) 0))

/-- Constant-index beta entry with a term-parametric output. -/
def betaTermAtConstIdx (out : Term) (code step idxValue : Nat) : Formula :=
  ex (and (eqConstAt 0 idxValue)
    (betaTermAt (Term.rename Nat.succ out) (code+1) (step+1) 0))

/-- Constant-index wrapper for a fully term-parametric beta entry. -/
def betaTermTermAtConstIdx
    (out code step : Term) (idxValue : Nat) : Formula :=
  ex (and (eqConstAt 0 idxValue)
    (betaTermTermAt (Term.rename Nat.succ out)
      (Term.rename Nat.succ code) (Term.rename Nat.succ step)
      (Term.var 0)))

/-- Successor-index wrapper for a fully term-parametric beta entry.  This is
the term-code/output analogue of `betaAtSuccIdx`: the outer witness is the
successor index, and the raw term-parametric beta entry is stated at that
witness. -/
def betaTermTermAtSuccIdx (out code step : Term) (idx : Nat) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
    (betaTermTermAt (Term.rename Nat.succ out)
      (Term.rename Nat.succ code) (Term.rename Nat.succ step)
      (Term.var 0)))

theorem betaTermAtConstIdx_var (out code step idxValue : Nat) :
    betaTermAtConstIdx (Term.var out) code step idxValue =
      betaAtConstIdx out code step idxValue := by
  simp [betaTermAtConstIdx, betaAtConstIdx, betaTermAt_var, Term.rename]

def betaAtSuccIdx (out code step idx : Nat) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.succ (Term.var (idx+1))))
    (betaAt (out+1) (code+1) (step+1) 0))

/-- The modulus used by Gödel's beta function at sequence index `idx`. -/
def BetaModulus (step idx : Nat) : Nat :=
  1 + (idx + 1) * step

/-- The semantic relation expressed by `betaAt`: `value` is the `idx`-th
entry of a beta-coded sequence with ambient parameters `code` and `step`. -/
def BetaEntry (code step idx value : Nat) : Prop :=
  ∃ q, code = q * BetaModulus step idx + value ∧
    value < BetaModulus step idx

/-- A simple positive beta step large enough to code two adjacent entries. -/
def twoEntryBetaStep (cur next : Nat) : Nat :=
  cur + next + 1

/-- Explicit two-entry beta code for entries `0 ↦ cur` and `1 ↦ next`.

For `s = cur + next + 1`, the beta moduli are `s+1` and `2*s+1`, which are
coprime with the useful identity `2*(s+1) ≡ 1 [MOD 2*s+1]`.  The code below
uses only addition and multiplication, avoiding any subtraction or hidden
bounded search. -/
def twoEntryBetaCode (cur next : Nat) : Nat :=
  let s := twoEntryBetaStep cur next
  cur + (s + 1) * (2 * next + 4 * s * cur)

theorem BetaEntry_twoEntry_zero (cur next : Nat) :
    BetaEntry (twoEntryBetaCode cur next) (twoEntryBetaStep cur next) 0 cur := by
  let s := twoEntryBetaStep cur next
  refine ⟨2 * next + 4 * s * cur, ?_, ?_⟩
  · simp [twoEntryBetaCode, twoEntryBetaStep, BetaModulus, s, Nat.add_comm,
      Nat.mul_comm]
  · simp [twoEntryBetaStep, BetaModulus]
    omega

theorem BetaEntry_twoEntry_one (cur next : Nat) :
    BetaEntry (twoEntryBetaCode cur next) (twoEntryBetaStep cur next) 1 next := by
  let s := twoEntryBetaStep cur next
  refine ⟨next + (2 * s + 1) * cur, ?_, ?_⟩
  · simp [twoEntryBetaCode, twoEntryBetaStep, BetaModulus, s]
    grind
  · simp [twoEntryBetaStep, BetaModulus]
    omega

/-- A tiny local factorial, kept here to avoid adding a dependency just for
the Gödel beta coding lemma. -/
def betaFact : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * betaFact n

/-- Product of the first `n` Gödel-beta moduli for a fixed step. -/
def BetaModuliProduct (step : Nat) : Nat → Nat
  | 0 => 1
  | n+1 => BetaModuliProduct step n * BetaModulus step n

/-- Semantic mirror of a beta-coded binary-halving step. -/
def BetaDiv2Step (code step idx cur next bit : Nat) : Prop :=
  BetaEntry code step idx cur ∧
    BetaEntry code step (idx + 1) next ∧
      (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit

/-- Semantic mirror of a beta-coded halving trace through `last`. -/
def BetaDiv2StepsThrough (code step last : Nat) : Prop :=
  ∀ k, k ≤ last → ∃ cur next bit, BetaDiv2Step code step k cur next bit

/-- Semantic shifted-tail relation between beta-coded traces.

The new trace copies the old trace one position down: for every `k <= last`,
each old beta entry at index `k+1` is a new beta entry at index `k`. -/
def BetaShiftTailThrough
    (oldCode oldStep newCode newStep last : Nat) : Prop :=
  ∀ k, k ≤ last → ∀ value,
    BetaEntry oldCode oldStep (k + 1) value →
      BetaEntry newCode newStep k value

/-- Semantic mirror of the bit read from a beta-coded halving trace. -/
def BetaDiv2Bit (code step idx bit : Nat) : Prop :=
  ∃ cur next, BetaDiv2Step code step idx cur next bit

/-- Semantic trace predicate used by the PA interpretation of HF membership. -/
def HFMemTrace (elem set code step : Nat) : Prop :=
  BetaEntry code step 0 set ∧
    BetaDiv2StepsThrough code step elem ∧
      BetaDiv2Bit code step elem 1

theorem BetaDiv2Step_twoEntry {cur next bit : Nat}
    (hbit : bit = 0 ∨ bit = 1)
    (hcur : cur = next + next + bit) :
    BetaDiv2Step (twoEntryBetaCode cur next) (twoEntryBetaStep cur next)
      0 cur next bit := by
  exact ⟨BetaEntry_twoEntry_zero cur next,
    BetaEntry_twoEntry_one cur next, hbit, hcur⟩

theorem BetaDiv2StepsThrough_zero_twoEntry {cur next bit : Nat}
    (hbit : bit = 0 ∨ bit = 1)
    (hcur : cur = next + next + bit) :
    BetaDiv2StepsThrough (twoEntryBetaCode cur next)
      (twoEntryBetaStep cur next) 0 := by
  intro k hk
  have hk0 : k = 0 := by omega
  subst hk0
  exact ⟨cur, next, bit, BetaDiv2Step_twoEntry hbit hcur⟩

theorem HFMemTrace_zero_exists_of_one_step {set half : Nat}
    (hset : set = half + half + 1) :
    ∃ code step, HFMemTrace 0 set code step := by
  refine ⟨twoEntryBetaCode set half, twoEntryBetaStep set half, ?_⟩
  exact ⟨BetaEntry_twoEntry_zero set half,
    BetaDiv2StepsThrough_zero_twoEntry (Or.inr rfl) hset,
    ⟨set, half, BetaDiv2Step_twoEntry (Or.inr rfl) hset⟩⟩

/-- Term-parametric counterpart of `twoEntryBetaStep`.

It is only the candidate beta step `S (cur + next)`; its adequacy for the two
entries is established by separate PA proofs. -/
def twoEntryBetaStepTerm (cur next : Term) : Term :=
  Term.succ (Term.add cur next)

/-- Term-parametric counterpart of `twoEntryBetaCode`.

The expression mirrors the semantic CRT witness exactly.  In particular, the
definition contains no beta-entry or boundedness proof; those are supplied by
the term-level exactness theorems below. -/
def twoEntryBetaCodeTerm (cur next : Term) : Term :=
  let s := twoEntryBetaStepTerm cur next
  Term.add cur
    (Term.mul (Term.succ s)
      (Term.add
        (Term.mul (Term.numeral 2) next)
        (Term.mul (Term.mul (Term.numeral 4) s) cur)))

/-- Generic natural-number CRT update term.

If `product * inverse = 1 (mod modulus)` and `delta` corrects the old residue
to the desired new residue, adding `product * (inverse * delta)` preserves all
congruences whose moduli divide `product` while establishing the new one.
Those facts are proof obligations of the theorems below, not part of this
arithmetic definition. -/
def crtExtendCodeTerm
    (oldCode product inverse delta : Term) : Term :=
  Term.add oldCode (Term.mul product (Term.mul inverse delta))

/-- Subtraction-free correction for a successor modulus `S modulusPred`.

Adding this term to `oldCode` yields
`oldCode * S modulusPred + newRem`.  The defining expression contains only
the candidate correction; its PA equality is proved separately. -/
def crtSuccessorCorrectionTerm
    (oldCode modulusPred newRem : Term) : Term :=
  Term.add (Term.mul modulusPred oldCode) newRem

/-- Quotient term for composing two positive inverse certificates modulo the
same modulus.

If `p*u = 1 + m*q` and `r*v = 1 + m*s`, then
`(p*r)*(u*v) = 1 + m*crtInverseProductQuotTerm m q s`.  The corresponding PA
proof is separate below. -/
def crtInverseProductQuotTerm
    (modulus leftQuot rightQuot : Term) : Term :=
  Term.add
    (Term.add
      (Term.mul leftQuot (Term.mul modulus rightQuot))
      leftQuot)
    rightQuot

/-- Positive representative of a negative Bezout coefficient.

For moduli `m = S mPred`, `n = S nPred` and a certificate
`n * positiveCoeff = 1 + m * negativeCoeff`, this term is
`n * (positiveCoeff + 1) + (n - 1) * negativeCoeff`. -/
def crtPositiveInverseTerm
    (rightPred positiveCoeff negativeCoeff : Term) : Term :=
  Term.add
    (Term.mul (Term.succ rightPred) (Term.succ positiveCoeff))
    (Term.mul rightPred negativeCoeff)

/-- Nonnegative quotient paired with `crtPositiveInverseTerm`.

Under the same negative Bezout certificate, this is
`m * (negativeCoeff + 1) + (m - 1) * positiveCoeff`. -/
def crtPositiveInverseQuotTerm
    (leftPred positiveCoeff negativeCoeff : Term) : Term :=
  Term.add
    (Term.mul (Term.succ leftPred) (Term.succ negativeCoeff))
    (Term.mul leftPred positiveCoeff)

/-- Positive coefficient in the beta-modulus negative Bezout identity.

For successor indices `L = leftIdx + 1`, `R = rightIdx + 1`, this is
`1 + R * (L * scale)`. -/
def betaPairBezoutPositiveCoeffTerm
    (leftIdx rightIdx scale : Term) : Term :=
  Term.succ
    (Term.mul (Term.succ rightIdx)
      (Term.mul (Term.succ leftIdx) scale))

/-- Negative coefficient in the beta-modulus negative Bezout identity.

With `R = rightIdx + 1`, this is `R * (R * scale)`. -/
def betaPairBezoutNegativeCoeffTerm
    (rightIdx scale : Term) : Term :=
  Term.mul (Term.succ rightIdx)
    (Term.mul (Term.succ rightIdx) scale)

/-- An explicit positive inverse certificate:
`product * inverse = 1 + modulus * quotient`. -/
def crtInverseTermAt
    (product modulus inverse quotient : Term) : Formula :=
  eq (Term.mul product inverse)
    (Term.succ (Term.mul modulus quotient))

theorem rename_crtInverseTermAt
    (r : Nat → Nat) (product modulus inverse quotient : Term) :
    rename r (crtInverseTermAt product modulus inverse quotient) =
      crtInverseTermAt
        (Term.rename r product)
        (Term.rename r modulus)
        (Term.rename r inverse)
        (Term.rename r quotient) := by
  simp [crtInverseTermAt, rename, Term.rename]

/-- Existence of a positive inverse certificate, with inverse and quotient as
separate existential witnesses. -/
def crtInverseExistsTermAt (product modulus : Term) : Formula :=
  ex (ex (crtInverseTermAt
    (Term.rename (fun n => n + 2) product)
    (Term.rename (fun n => n + 2) modulus)
    (Term.var 1) (Term.var 0)))

theorem rename_crtInverseExistsTermAt
    (r : Nat → Nat) (product modulus : Term) :
    rename r (crtInverseExistsTermAt product modulus) =
      crtInverseExistsTermAt
        (Term.rename r product) (Term.rename r modulus) := by
  simp [crtInverseExistsTermAt, rename_crtInverseTermAt, rename,
    Term.rename, Term.rename_comp, SetTheory.up, Nat.add_assoc]

/-- Inner quotient existential exposed after opening the inverse witness. -/
def crtInverseExistsTermAtQuotEx
    (product modulus : Term) : Formula :=
  ex (crtInverseTermAt
    (Term.rename (fun n => n + 2) product)
    (Term.rename (fun n => n + 2) modulus)
    (Term.var 1) (Term.var 0))

/-- Equation exposed after opening both inverse-certificate witnesses. -/
def crtInverseExistsTermAtBody
    (product modulus : Term) : Formula :=
  crtInverseTermAt
    (Term.rename (fun n => n + 2) product)
    (Term.rename (fun n => n + 2) modulus)
    (Term.var 1) (Term.var 0)

/-- Context obtained after opening both witnesses of
`crtInverseExistsTermAt`. -/
def crtInverseExistsTermAtOpenedContext
    (product modulus : Term) (G : List Formula) : List Formula :=
  crtInverseExistsTermAtBody product modulus ::
    (crtInverseExistsTermAtQuotEx product modulus ::
      G.map (rename Nat.succ)).map (rename Nat.succ)

/-- An additive correction for replacing one bounded remainder by another.

The equation is deliberately the whole relation: existence of a correction
under the old-remainder bound is proved separately, rather than encoded by a
truncated-subtraction term. -/
def crtCorrectionTermAt
    (oldRem modulus newRem delta : Term) : Formula :=
  eq (Term.add oldRem delta) (Term.add modulus newRem)

/-- Existence of an additive CRT correction witness. -/
def crtCorrectionExistsTermAt
    (oldRem modulus newRem : Term) : Formula :=
  ex (crtCorrectionTermAt
    (Term.rename Nat.succ oldRem)
    (Term.rename Nat.succ modulus)
    (Term.rename Nat.succ newRem)
    (Term.var 0))

/-- Body exposed after opening an additive CRT correction witness. -/
def crtCorrectionExistsTermAtBody
    (oldRem modulus newRem : Term) : Formula :=
  crtCorrectionTermAt
    (Term.rename Nat.succ oldRem)
    (Term.rename Nat.succ modulus)
    (Term.rename Nat.succ newRem)
    (Term.var 0)

/-- Agreement of two beta codes below a term-valued bound.

The relation is intentionally extensional: for every index below `bound` and
every candidate output, an old beta entry implies the matching new beta entry.
It neither asserts a target entry nor chooses a new code. -/
def betaPrefixAgreementTermAt
    (oldCode newCode step bound : Term) : Formula :=
  all (imp
    (ltTermAt (Term.var 0) (Term.rename Nat.succ bound))
    (all (imp
      (betaTermTermAt (Term.var 0)
        (Term.rename (fun n => n + 2) oldCode)
        (Term.rename (fun n => n + 2) step)
        (Term.var 1))
      (betaTermTermAt (Term.var 0)
        (Term.rename (fun n => n + 2) newCode)
        (Term.rename (fun n => n + 2) step)
        (Term.var 1)))))

/-- A one-entry beta-code extension: preserve every entry below `target` and
establish `newOut` at `target`. -/
def betaCodeExtensionTermAt
    (oldCode step target newOut newCode : Term) : Formula :=
  and (betaPrefixAgreementTermAt oldCode newCode step target)
    (betaTermTermAt newOut newCode step target)

/-- Existence of a code witnessing one-entry beta extension. -/
def betaCodeExtensionExistsTermAt
    (oldCode step target newOut : Term) : Formula :=
  ex (betaCodeExtensionTermAt
    (Term.rename Nat.succ oldCode)
    (Term.rename Nat.succ step)
    (Term.rename Nat.succ target)
    (Term.rename Nat.succ newOut)
    (Term.var 0))

/-- Body exposed after opening a one-entry beta-extension code witness. -/
def betaCodeExtensionExistsTermAtBody
    (oldCode step target newOut : Term) : Formula :=
  betaCodeExtensionTermAt
    (Term.rename Nat.succ oldCode)
    (Term.rename Nat.succ step)
    (Term.rename Nat.succ target)
    (Term.rename Nat.succ newOut)
    (Term.var 0)

/-- A beta-prefix CRT accumulator at `bound` for a fixed target modulus.

The product has every beta modulus below `bound` as a factor and separately
carries an existential positive-inverse certificate modulo the target beta
modulus. -/
def betaPrefixCRTAccumulatorTermAt
    (step target bound product : Term) : Formula :=
  and (betaPrefixDividesTermAt step bound product)
    (crtInverseExistsTermAt product (betaModTermTerm step target))

/-- Existence of the product witness for a beta-prefix CRT accumulator. -/
def betaPrefixCRTAccumulatorExistsTermAt
    (step target bound : Term) : Formula :=
  ex (betaPrefixCRTAccumulatorTermAt
    (Term.rename Nat.succ step)
    (Term.rename Nat.succ target)
    (Term.rename Nat.succ bound)
    (Term.var 0))

/-- Body exposed after opening a beta-prefix accumulator product witness. -/
def betaPrefixCRTAccumulatorExistsTermAtBody
    (step target bound : Term) : Formula :=
  betaPrefixCRTAccumulatorTermAt
    (Term.rename Nat.succ step)
    (Term.rename Nat.succ target)
    (Term.rename Nat.succ bound)
    (Term.var 0)

/-- Open beta step witness for the even branch of `0 ∈ S low`: when
`low = 2*h`, the current value `S low` is odd, so a one-step halving trace can
use `S low` itself as the beta step. -/
def evenSuccBetaStepTerm (low : Nat) : Term :=
  Term.succ (Term.var low)

/-- Open beta code witness for the even branch of `0 ∈ S low`.

For `cur = S low`, this is `cur * S cur + cur`.  Under the branch equation
`low = 2*h`, it has remainder `cur` modulo `S cur` at index `0` and remainder
`h` modulo `S (2*cur)` at index `1`; those facts are proved by separate PA
lemmas rather than hidden in this definition. -/
def evenSuccBetaCodeTerm (low : Nat) : Term :=
  let cur := evenSuccBetaStepTerm low
  Term.add (Term.mul cur (Term.succ cur)) cur

/-- Open beta step term for a generic one-step odd-current trace.

The definition deliberately records only the candidate current value.  The
fact that this current value is odd, and the identity of its half, are supplied
by the `oddDoubleEqAt` hypotheses of the later lemmas. -/
def oddCurrentBetaStepTerm (cur : Nat) : Term :=
  Term.var cur

/-- Open beta code witness for a generic one-step odd-current trace.

For a current term `cur`, this is `cur * S cur + cur`.  Under a separate proof
of `cur = S (h + h)`, it has remainders `cur` at index `0` and `h` at index
`1`; those arithmetic facts are proved by the corresponding PA lemmas below. -/
def oddCurrentBetaCodeTerm (cur : Nat) : Term :=
  let current := oddCurrentBetaStepTerm cur
  Term.add (Term.mul current (Term.succ current)) current

/-- A single adjacent beta-coded sequence step is a binary-halving step:
the current value is `2 * next + bit`, with `bit ∈ {0,1}`. -/
def betaDiv2StepWitnessAt (code step idx : Nat) : Formula :=
    (ex (ex (ex
      (and
        (betaAt 2 (code+3) (step+3) (idx+3))
        (and
          (betaAtSuccIdx 1 (code+3) (step+3) (idx+3))
          (div2StepAt 2 1 0))))))

/-- Term-indexed wrapper for a binary-halving beta step.  The raw step witness
remains the slot-indexed relation; the outer witness slot records the PA term
used as the sequence index. -/
def betaDiv2StepWitnessAtTermIdx (code step : Nat) (idx : Term) : Formula :=
  ex (and
    (eq (Term.var 0) (Term.rename Nat.succ idx))
    (betaDiv2StepWitnessAt (code+1) (step+1) 0))

/-- Fully term-parametric binary-halving step witnessed inside a beta-coded
trace.  The three existential witnesses are the current value, the next value,
and the low bit; the code, step size, and index are arbitrary PA terms. -/
def betaDiv2StepWitnessTermAt (code step idx : Term) : Formula :=
  ex (ex (ex
    (and
      (betaTermTermAt (Term.var 2)
        (Term.rename (fun n => n+3) code)
        (Term.rename (fun n => n+3) step)
        (Term.rename (fun n => n+3) idx))
      (and
        (betaTermTermAt (Term.var 1)
          (Term.rename (fun n => n+3) code)
          (Term.rename (fun n => n+3) step)
          (Term.succ (Term.rename (fun n => n+3) idx)))
        (div2StepTermAt (Term.var 2) (Term.var 1) (Term.var 0))))))

/-- Fully term-parametric binary-halving step whose successor entry is packaged
with the legacy successor-index wrapper.

This is a formula macro for the exact pointwise shape obtained when
`betaDiv2StepWitnessAt` has its code and step slots instantiated by arbitrary
terms, but its index remains a de Bruijn slot.  It separates that legacy
packing shape from the raw term-parametric witness `betaDiv2StepWitnessTermAt`.
-/
def betaDiv2StepWitnessTermSuccIdxAt
    (code step : Term) (idx : Nat) : Formula :=
  ex (ex (ex
    (and
      (betaTermTermAt (Term.var 2)
        (Term.rename (fun n => n+3) code)
        (Term.rename (fun n => n+3) step)
        (Term.var (idx+3)))
      (and
        (betaTermTermAtSuccIdx (Term.var 1)
          (Term.rename (fun n => n+3) code)
          (Term.rename (fun n => n+3) step)
          (idx+3))
        (div2StepTermAt (Term.var 2) (Term.var 1) (Term.var 0))))))

/-- Every adjacent pair below `limit` in a beta-coded sequence is one
binary-halving step. -/
def betaDiv2StepAt (code step limit : Nat) : Formula :=
  all (imp (ltAt 0 (limit+1))
    (betaDiv2StepWitnessAt (code+1) (step+1) 0))

/-- Every adjacent pair through `last` in a beta-coded sequence is one
binary-halving step. -/
def betaDiv2StepsThroughAt (code step last : Nat) : Formula :=
  all (imp (leAt 0 (last+1))
    (betaDiv2StepWitnessAt (code+1) (step+1) 0))

/-- Term-bound variant of `betaDiv2StepsThroughAt`: every adjacent pair through
the PA term `last` in a beta-coded sequence is one binary-halving step.

This is a formula macro only.  It is useful after opening existential
witnesses, where the trace bound is often a substituted term such as `S x`
rather than a bare variable slot. -/
def betaDiv2StepsThroughTermAt (code step : Nat) (last : Term) : Formula :=
  all (imp (leTermAt (Term.var 0) (Term.rename Nat.succ last))
    (betaDiv2StepWitnessAt (code+1) (step+1) 0))

/-- Fully term-parametric bounded beta-halving trace.  For every `i <= last`,
the beta-coded sequence with term code `code` and term step size `step` has an
explicit binary-halving step at index `i`. -/
def betaDiv2StepsThroughTermTermAt
    (code step last : Term) : Formula :=
  all (imp
    (leTermAt (Term.var 0) (Term.rename Nat.succ last))
    (betaDiv2StepWitnessTermAt
      (Term.rename Nat.succ code)
      (Term.rename Nat.succ step)
      (Term.var 0)))

/-- Strict-prefix form of shifted beta coding.

For every `i < bound`, every old beta entry at `S i` is copied to index `i`
of the new code.  All code and step parameters are terms so the relation can
serve as the invariant of an internal PA construction. -/
def betaShiftPrefixTermAt
    (oldCode oldStep newCode newStep bound : Term) : Formula :=
  all (imp
    (ltTermAt (Term.var 0) (Term.rename Nat.succ bound))
    (all (imp
      (betaTermTermAt (Term.var 0)
        (Term.rename (fun n => n + 2) oldCode)
        (Term.rename (fun n => n + 2) oldStep)
        (Term.succ (Term.var 1)))
      (betaTermTermAt (Term.var 0)
        (Term.rename (fun n => n + 2) newCode)
        (Term.rename (fun n => n + 2) newStep)
        (Term.var 1)))))

theorem subst_betaShiftPrefixTermAt
    (σ : Nat → Term)
    (oldCode oldStep newCode newStep bound : Term) :
    subst σ
        (betaShiftPrefixTermAt
          oldCode oldStep newCode newStep bound) =
      betaShiftPrefixTermAt
        (Term.subst σ oldCode) (Term.subst σ oldStep)
        (Term.subst σ newCode) (Term.subst σ newStep)
        (Term.subst σ bound) := by
  simp [betaShiftPrefixTermAt, subst_ltTermAt, subst_betaTermTermAt,
    subst, Term.subst, Term.rename, Term.upSubst,
    Term.subst_rename_succ_up, term_subst_up_up_rename_add_two]

theorem rename_betaShiftPrefixTermAt
    (r : Nat → Nat)
    (oldCode oldStep newCode newStep bound : Term) :
    rename r
        (betaShiftPrefixTermAt
          oldCode oldStep newCode newStep bound) =
      betaShiftPrefixTermAt
        (Term.rename r oldCode) (Term.rename r oldStep)
        (Term.rename r newCode) (Term.rename r newStep)
        (Term.rename r bound) := by
  rw [← subst_var_rename, subst_betaShiftPrefixTermAt]
  simp only [term_subst_var_rename]

/-- Existence of a code satisfying a shifted strict prefix for a fixed new
step. -/
def betaShiftPrefixCodeExistsTermAt
    (oldCode oldStep newStep bound : Term) : Formula :=
  ex (betaShiftPrefixTermAt
    (Term.rename Nat.succ oldCode)
    (Term.rename Nat.succ oldStep)
    (Term.var 0)
    (Term.rename Nat.succ newStep)
    (Term.rename Nat.succ bound))

theorem subst_betaShiftPrefixCodeExistsTermAt
    (σ : Nat → Term) (oldCode oldStep newStep bound : Term) :
    subst σ
        (betaShiftPrefixCodeExistsTermAt
          oldCode oldStep newStep bound) =
      betaShiftPrefixCodeExistsTermAt
        (Term.subst σ oldCode) (Term.subst σ oldStep)
        (Term.subst σ newStep) (Term.subst σ bound) := by
  simp [betaShiftPrefixCodeExistsTermAt,
    subst_betaShiftPrefixTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_betaShiftPrefixCodeExistsTermAt
    (r : Nat → Nat) (oldCode oldStep newStep bound : Term) :
    rename r
        (betaShiftPrefixCodeExistsTermAt
          oldCode oldStep newStep bound) =
      betaShiftPrefixCodeExistsTermAt
        (Term.rename r oldCode) (Term.rename r oldStep)
        (Term.rename r newStep) (Term.rename r bound) := by
  rw [← subst_var_rename, subst_betaShiftPrefixCodeExistsTermAt]
  simp only [term_subst_var_rename]

/-- Body exposed after opening a shifted-prefix code witness. -/
def betaShiftPrefixCodeExistsTermAtBody
    (oldCode oldStep newStep bound : Term) : Formula :=
  betaShiftPrefixTermAt
    (Term.rename Nat.succ oldCode)
    (Term.rename Nat.succ oldStep)
    (Term.var 0)
    (Term.rename Nat.succ newStep)
    (Term.rename Nat.succ bound)

/-- Strict-prefix form of beta-index successor transport.

For every `i < bound`, every source beta entry at index `i` is copied to the
target entry at index `S i`.  This is the index-direction needed when a
one-step binary predecessor is prepended to an existing halving trace. -/
def betaUnshiftPrefixTermAt
    (sourceCode sourceStep targetCode targetStep bound : Term) : Formula :=
  all (imp
    (ltTermAt (Term.var 0) (Term.rename Nat.succ bound))
    (all (imp
      (betaTermTermAt (Term.var 0)
        (Term.rename (fun n => n + 2) sourceCode)
        (Term.rename (fun n => n + 2) sourceStep)
        (Term.var 1))
      (betaTermTermAt (Term.var 0)
        (Term.rename (fun n => n + 2) targetCode)
        (Term.rename (fun n => n + 2) targetStep)
        (Term.succ (Term.var 1))))))

theorem subst_betaUnshiftPrefixTermAt
    (σ : Nat → Term)
    (sourceCode sourceStep targetCode targetStep bound : Term) :
    subst σ
        (betaUnshiftPrefixTermAt
          sourceCode sourceStep targetCode targetStep bound) =
      betaUnshiftPrefixTermAt
        (Term.subst σ sourceCode) (Term.subst σ sourceStep)
        (Term.subst σ targetCode) (Term.subst σ targetStep)
        (Term.subst σ bound) := by
  simp [betaUnshiftPrefixTermAt, subst_ltTermAt, subst_betaTermTermAt,
    subst, Term.subst, Term.rename, Term.upSubst, Term.subst_rename_succ_up,
    term_subst_up_up_rename_add_two]

theorem rename_betaUnshiftPrefixTermAt
    (r : Nat → Nat)
    (sourceCode sourceStep targetCode targetStep bound : Term) :
    rename r
        (betaUnshiftPrefixTermAt
          sourceCode sourceStep targetCode targetStep bound) =
      betaUnshiftPrefixTermAt
        (Term.rename r sourceCode) (Term.rename r sourceStep)
        (Term.rename r targetCode) (Term.rename r targetStep)
        (Term.rename r bound) := by
  rw [← subst_var_rename, subst_betaUnshiftPrefixTermAt]
  simp only [term_subst_var_rename]

/-- Existence of a code satisfying a beta-unshift strict prefix for a fixed
target step. -/
def betaUnshiftPrefixCodeExistsTermAt
    (sourceCode sourceStep targetStep bound : Term) : Formula :=
  ex (betaUnshiftPrefixTermAt
    (Term.rename Nat.succ sourceCode)
    (Term.rename Nat.succ sourceStep)
    (Term.var 0)
    (Term.rename Nat.succ targetStep)
    (Term.rename Nat.succ bound))

/-- Body exposed after opening a beta-unshift prefix code witness. -/
def betaUnshiftPrefixCodeExistsTermAtBody
    (sourceCode sourceStep targetStep bound : Term) : Formula :=
  betaUnshiftPrefixTermAt
    (Term.rename Nat.succ sourceCode)
    (Term.rename Nat.succ sourceStep)
    (Term.var 0)
    (Term.rename Nat.succ targetStep)
    (Term.rename Nat.succ bound)

/-- A head-preserving beta prepend prefix.

The target code has `head` at index `0`, while the independent unshift
relation copies every source entry below `bound` to its successor index. -/
def betaPrependPrefixTermAt
    (sourceCode sourceStep head targetCode targetStep bound : Term) : Formula :=
  and (betaTermTermAt head targetCode targetStep Term.zero)
    (betaUnshiftPrefixTermAt
      sourceCode sourceStep targetCode targetStep bound)

theorem subst_betaPrependPrefixTermAt
    (σ : Nat → Term)
    (sourceCode sourceStep head targetCode targetStep bound : Term) :
    subst σ
        (betaPrependPrefixTermAt
          sourceCode sourceStep head targetCode targetStep bound) =
      betaPrependPrefixTermAt
        (Term.subst σ sourceCode) (Term.subst σ sourceStep)
        (Term.subst σ head) (Term.subst σ targetCode)
        (Term.subst σ targetStep) (Term.subst σ bound) := by
  simp [betaPrependPrefixTermAt, subst,
    subst_betaTermTermAt, subst_betaUnshiftPrefixTermAt, Term.subst]

theorem rename_betaPrependPrefixTermAt
    (r : Nat → Nat)
    (sourceCode sourceStep head targetCode targetStep bound : Term) :
    rename r
        (betaPrependPrefixTermAt
          sourceCode sourceStep head targetCode targetStep bound) =
      betaPrependPrefixTermAt
        (Term.rename r sourceCode) (Term.rename r sourceStep)
        (Term.rename r head) (Term.rename r targetCode)
        (Term.rename r targetStep) (Term.rename r bound) := by
  rw [← subst_var_rename, subst_betaPrependPrefixTermAt]
  simp only [term_subst_var_rename]

/-- Existence of a target code satisfying a head-preserving beta prepend
prefix for one fixed target step. -/
def betaPrependPrefixCodeExistsTermAt
    (sourceCode sourceStep head targetStep bound : Term) : Formula :=
  ex (betaPrependPrefixTermAt
    (Term.rename Nat.succ sourceCode)
    (Term.rename Nat.succ sourceStep)
    (Term.rename Nat.succ head)
    (Term.var 0)
    (Term.rename Nat.succ targetStep)
    (Term.rename Nat.succ bound))

theorem subst_betaPrependPrefixCodeExistsTermAt
    (σ : Nat → Term)
    (sourceCode sourceStep head targetStep bound : Term) :
    subst σ
        (betaPrependPrefixCodeExistsTermAt
          sourceCode sourceStep head targetStep bound) =
      betaPrependPrefixCodeExistsTermAt
        (Term.subst σ sourceCode) (Term.subst σ sourceStep)
        (Term.subst σ head) (Term.subst σ targetStep)
        (Term.subst σ bound) := by
  simp [betaPrependPrefixCodeExistsTermAt,
    subst_betaPrependPrefixTermAt, subst, Term.subst, Term.upSubst,
    Term.subst_rename_succ_up]

theorem rename_betaPrependPrefixCodeExistsTermAt
    (r : Nat → Nat)
    (sourceCode sourceStep head targetStep bound : Term) :
    rename r
        (betaPrependPrefixCodeExistsTermAt
          sourceCode sourceStep head targetStep bound) =
      betaPrependPrefixCodeExistsTermAt
        (Term.rename r sourceCode) (Term.rename r sourceStep)
        (Term.rename r head) (Term.rename r targetStep)
        (Term.rename r bound) := by
  rw [← subst_var_rename, subst_betaPrependPrefixCodeExistsTermAt]
  simp only [term_subst_var_rename]

/-- Body exposed after opening a beta-prepend prefix-code witness. -/
def betaPrependPrefixCodeExistsTermAtBody
    (sourceCode sourceStep head targetStep bound : Term) : Formula :=
  betaPrependPrefixTermAt
    (Term.rename Nat.succ sourceCode)
    (Term.rename Nat.succ sourceStep)
    (Term.rename Nat.succ head)
    (Term.var 0)
    (Term.rename Nat.succ targetStep)
    (Term.rename Nat.succ bound)

/-- Existence of both a target step and target code for a head-preserving
beta prepend prefix. -/
def betaPrependExistsTermAt
    (sourceCode sourceStep head bound : Term) : Formula :=
  ex (betaPrependPrefixCodeExistsTermAt
    (Term.rename Nat.succ sourceCode)
    (Term.rename Nat.succ sourceStep)
    (Term.rename Nat.succ head)
    (Term.var 0)
    (Term.rename Nat.succ bound))

theorem subst_betaPrependExistsTermAt
    (σ : Nat → Term) (sourceCode sourceStep head bound : Term) :
    subst σ
        (betaPrependExistsTermAt sourceCode sourceStep head bound) =
      betaPrependExistsTermAt
        (Term.subst σ sourceCode) (Term.subst σ sourceStep)
        (Term.subst σ head) (Term.subst σ bound) := by
  simp [betaPrependExistsTermAt,
    subst_betaPrependPrefixCodeExistsTermAt, subst, Term.subst,
    Term.upSubst, Term.subst_rename_succ_up]

theorem rename_betaPrependExistsTermAt
    (r : Nat → Nat) (sourceCode sourceStep head bound : Term) :
    rename r
        (betaPrependExistsTermAt sourceCode sourceStep head bound) =
      betaPrependExistsTermAt
        (Term.rename r sourceCode) (Term.rename r sourceStep)
        (Term.rename r head) (Term.rename r bound) := by
  rw [← subst_var_rename, subst_betaPrependExistsTermAt]
  simp only [term_subst_var_rename]

/-- Body exposed after opening the target-step witness of a beta prepend. -/
def betaPrependExistsTermAtBody
    (sourceCode sourceStep head bound : Term) : Formula :=
  betaPrependPrefixCodeExistsTermAt
    (Term.rename Nat.succ sourceCode)
    (Term.rename Nat.succ sourceStep)
    (Term.rename Nat.succ head)
    (Term.var 0)
    (Term.rename Nat.succ bound)

/-- Source-side availability contract for beta-prefix constructions: every
index strictly below `bound` has some beta output. -/
def betaEntryExistsPrefixTermAt
    (code step bound : Term) : Formula :=
  all (imp
    (ltTermAt (Term.var 0) (Term.rename Nat.succ bound))
    (betaEntryExistsTermAt
      (Term.rename Nat.succ code)
      (Term.rename Nat.succ step)
      (Term.var 0)))

/-- A pointwise shifted-tail relation between two beta-coded traces.

The old trace is represented by the ambient code and step slots `oldCode` and
`oldStep`; the new trace is represented by arbitrary PA terms `newCode` and
`newStep`.  Up to the bound `last`, every old beta entry at successor index
`S i` is copied to the new beta entry at index `i`.

This is deliberately only the transfer relation.  A later construction must
still build witnesses for `newCode` and `newStep` and prove this formula from
the old trace; the definition does not smuggle that construction in. -/
def betaShiftTailThroughTermAt
    (oldCode oldStep : Nat) (newCode newStep last : Term) : Formula :=
  all (imp
    (leTermAt (Term.var 0) (Term.rename Nat.succ last))
    (all (imp
      (betaTermTermAt (Term.var 0)
        (Term.var (oldCode+2)) (Term.var (oldStep+2))
        (Term.succ (Term.var 1)))
      (betaTermTermAt (Term.var 0)
        (Term.rename (fun n => n+2) newCode)
        (Term.rename (fun n => n+2) newStep)
        (Term.var 1)))))

/-- Existential form of `betaShiftTailThroughTermAt`.

This states that there are fresh beta code/step witnesses copying the ambient
old trace one position down through `last`.  The two existential binders are
kept explicit: the outer one is the new code and the inner one is the new step.
-/
def betaShiftTailExistsTermAt
    (oldCode oldStep : Nat) (last : Term) : Formula :=
  ex (ex
    (betaShiftTailThroughTermAt (oldCode+2) (oldStep+2)
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n => n+2) last)))

/-- Body exposed after opening both witnesses in
`betaShiftTailExistsTermAt`. -/
def betaShiftTailExistsTermAtBody
    (oldCode oldStep : Nat) (last : Term) : Formula :=
  betaShiftTailThroughTermAt (oldCode+2) (oldStep+2)
    (Term.var 1) (Term.var 0)
    (Term.rename (fun n => n+2) last)

/-- Opening the two witnesses of `betaShiftTailExistsTermAt` recovers the
term-parametric shifted-tail relation.  The outer witness is the fresh code;
the inner witness is its fresh step. -/
theorem subst_two_instTerm_betaShiftTailExistsTermAtBody
    (oldCode oldStep : Nat) (newCode newStep last : Term) :
    subst (instTerm newStep)
        (subst (Term.upSubst (instTerm newCode))
          (betaShiftTailExistsTermAtBody oldCode oldStep last)) =
      betaShiftTailThroughTermAt
        oldCode oldStep newCode newStep last := by
  simp [betaShiftTailExistsTermAtBody, betaShiftTailThroughTermAt,
    betaTermTermAt, remTermTermAt, ltTermAt, betaModTermTerm, leTermAt,
    subst, instTerm, Term.subst, Term.upSubst, Term.rename,
    Term.rename_comp,
    term_subst_up_up_instTerm_rename_three_succ,
    term_subst_up_up_up_instTerm_rename_four_succ,
    term_subst_up_up_up_up_instTerm_rename_five_succ]

/-- Inner existential exposed after opening the new-code witness in
`betaShiftTailExistsTermAt`. -/
def betaShiftTailExistsTermAtStepEx
    (oldCode oldStep : Nat) (last : Term) : Formula :=
  ex (betaShiftTailExistsTermAtBody oldCode oldStep last)

/-- Context obtained by opening both fresh witnesses in
`betaShiftTailExistsTermAt oldCode oldStep last`.

The head assumption is the shifted-tail relation for the freshly bound code
and step variables.  The next assumption is the still-open inner existential,
as required by the standard two-step existential elimination shape. -/
def betaShiftTailExistsTermAtOpenedContext
    (oldCode oldStep : Nat) (last : Term) (G : List Formula) :
    List Formula :=
  betaShiftTailExistsTermAtBody oldCode oldStep last ::
    (betaShiftTailExistsTermAtStepEx oldCode oldStep last ::
      G.map (rename Nat.succ)).map (rename Nat.succ)

/-- Closed-bound variant of `betaShiftTailThroughTermAt`.

For every standard `i <= last`, the beta entry at old index `S i` is copied
to the new trace at index `i`.  This is only the closed formula macro; the
finite PA construction from semantic beta-entry data is proved separately. -/
def betaShiftTailThroughConstAt
    (oldCode oldStep newCode newStep last : Nat) : Formula :=
  all (imp
    (leConstAt 0 last)
    (all (imp
      (betaTermTermAt (Term.var 0)
        (Term.var (oldCode+2)) (Term.var (oldStep+2))
        (Term.succ (Term.var 1)))
      (betaTermTermAt (Term.var 0)
        (Term.var (newCode+2)) (Term.var (newStep+2))
        (Term.var 1)))))

theorem rename_betaShiftTailThroughTermAt
    (r : Nat → Nat) (oldCode oldStep : Nat)
    (newCode newStep last : Term) :
    rename r
        (betaShiftTailThroughTermAt
          oldCode oldStep newCode newStep last) =
      betaShiftTailThroughTermAt
        (r oldCode) (r oldStep)
        (Term.rename r newCode) (Term.rename r newStep)
        (Term.rename r last) := by
  have hslot (n : Nat) :
      SetTheory.up (SetTheory.up r) (n + 2) = r n + 2 := by
    change iterUpRenaming 2 r (n + 2) = r n + 2
    exact iterUpRenaming_add 2 r n
  have hshift (t : Term) :
      Term.rename (SetTheory.up (SetTheory.up r))
          (Term.rename (fun n => n + 2) t) =
        Term.rename (fun n => n + 2) (Term.rename r t) := by
    change Term.rename (iterUpRenaming 2 r)
        (Term.rename (fun n => n + 2) t) =
      Term.rename (fun n => n + 2) (Term.rename r t)
    exact term_rename_iterUpRenaming_rename_add 2 r t
  unfold betaShiftTailThroughTermAt
  simp only [rename]
  rw [rename_leTermAt]
  rw [rename_betaTermTermAt, rename_betaTermTermAt]
  simp only [Term.rename]
  rw [term_rename_up_rename_succ r last]
  rw [hslot oldCode, hslot oldStep, hshift newCode, hshift newStep]
  simp only [SetTheory.up]

theorem rename_betaShiftTailExistsTermAt
    (r : Nat → Nat) (oldCode oldStep : Nat) (last : Term) :
    rename r (betaShiftTailExistsTermAt oldCode oldStep last) =
      betaShiftTailExistsTermAt
        (r oldCode) (r oldStep) (Term.rename r last) := by
  have hslot (n : Nat) :
      SetTheory.up (SetTheory.up r) (n + 2) = r n + 2 := by
    change iterUpRenaming 2 r (n + 2) = r n + 2
    exact iterUpRenaming_add 2 r n
  have hshift (t : Term) :
      Term.rename (SetTheory.up (SetTheory.up r))
          (Term.rename (fun n => n + 2) t) =
        Term.rename (fun n => n + 2) (Term.rename r t) := by
    change Term.rename (iterUpRenaming 2 r)
        (Term.rename (fun n => n + 2) t) =
      Term.rename (fun n => n + 2) (Term.rename r t)
    exact term_rename_iterUpRenaming_rename_add 2 r t
  unfold betaShiftTailExistsTermAt
  simp only [rename]
  rw [rename_betaShiftTailThroughTermAt]
  simp only [Term.rename]
  rw [hslot oldCode, hslot oldStep, hshift last]
  simp only [SetTheory.up]

theorem rename_betaShiftTailThroughConstAt
    (r : Nat → Nat) (oldCode oldStep newCode newStep last : Nat) :
    rename r
        (betaShiftTailThroughConstAt
          oldCode oldStep newCode newStep last) =
      betaShiftTailThroughConstAt
        (r oldCode) (r oldStep) (r newCode) (r newStep) last := by
  have hslot (n : Nat) :
      SetTheory.up (SetTheory.up r) (n + 2) = r n + 2 := by
    change iterUpRenaming 2 r (n + 2) = r n + 2
    exact iterUpRenaming_add 2 r n
  unfold betaShiftTailThroughConstAt
  simp only [rename]
  unfold leConstAt
  simp only [rename]
  rw [rename_betaTermTermAt, rename_betaTermTermAt]
  simp only [Term.rename, Term.rename_numeral]
  rw [hslot oldCode, hslot oldStep, hslot newCode, hslot newStep]
  simp only [SetTheory.up]

/-- Closed-bound variant of `betaDiv2StepsThroughAt`: every adjacent pair up to
the standard numeral `last` in a beta-coded sequence is one binary-halving step.
This is only a formula macro; the PA constructors connecting it to the variable
bound form are separate lemmas. -/
def betaDiv2StepsThroughConstAt (code step last : Nat) : Formula :=
  all (imp (leConstAt 0 last)
    (betaDiv2StepWitnessAt (code+1) (step+1) 0))

/-- Read a specified bit from a beta-coded halving trace at `idx`. -/
def betaDiv2BitAt (bit code step idx : Nat) : Formula :=
  ex (ex
    (and
      (betaAt 1 (code+2) (step+2) (idx+2))
      (and
        (betaAtSuccIdx 0 (code+2) (step+2) (idx+2))
        (div2StepAt 1 0 (bit+2)))))

/-- Fully term-parametric read of a specified bit from a beta-coded halving
trace at `idx`.

This is the bit-reading companion to `betaDiv2StepWitnessTermAt`: only the
current and next beta entries are existentially opened here, while the bit,
code, step, and index are arbitrary PA terms supplied by the caller. -/
def betaDiv2BitTermAt (bit code step idx : Term) : Formula :=
  ex (ex
    (and
      (betaTermTermAt (Term.var 1)
        (Term.rename (fun n => n+2) code)
        (Term.rename (fun n => n+2) step)
        (Term.rename (fun n => n+2) idx))
      (and
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n => n+2) code)
          (Term.rename (fun n => n+2) step)
          (Term.succ (Term.rename (fun n => n+2) idx)))
        (div2StepTermAt (Term.var 1) (Term.var 0)
          (Term.rename (fun n => n+2) bit)))))

/-- Term-parametric final-bit existential for a beta-coded halving trace.

The existential bit witness is required to be `1`; the trace code, step, and
index are PA terms from the surrounding context. -/
def betaDiv2BitOneTermExAt (code step idx : Term) : Formula :=
  ex
    (and
      (oneAt 0)
      (betaDiv2BitTermAt (Term.var 0)
        (Term.rename Nat.succ code)
        (Term.rename Nat.succ step)
        (Term.rename Nat.succ idx)))

/-- PA formula for Ackermann-coded HF membership, mediated by a beta-coded
binary-halving trace. -/
def hfMemAt (elem set : Nat) : Formula :=
  ex (ex
    (and
      (betaAtConstIdx (set+2) 1 0 0)
      (and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex
          (and
            (oneAt 0)
            (betaDiv2BitAt 0 2 1 (elem+3)))))))

/-- Term-parametric variant of `hfMemAt` for the set code.  The element is
still read from a PA slot, while the initial beta entry may output an arbitrary
PA term.  This is the exact shape produced by substituting a non-variable term
for the set-code slot of `hfMemAt`. -/
def hfMemTermAt (elem : Nat) (setCode : Term) : Formula :=
  ex (ex
    (and
      (betaTermAtConstIdx (Term.rename (fun n => n+2) setCode) 1 0 0)
      (and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex
          (and
            (oneAt 0)
            (betaDiv2BitAt 0 2 1 (elem+3)))))))

/-- The actual membership formula obtained after the HF empty witness is
instantiated with the closed PA term `0`.  The element remains a slot; only the
set-code output in the initial beta entry is now a closed term. -/
def hfMemZeroSetAt (elem : Nat) : Formula :=
  ex (ex
    (and
      (betaTermAtConstIdx Term.zero 1 0 0)
      (and
        (betaDiv2StepsThroughAt 1 0 (elem+2))
        (ex
          (and
            (oneAt 0)
            (betaDiv2BitAt 0 2 1 (elem+3)))))))

/-- The term-parametric membership macro specializes to ordinary slot
membership when the set-code term is a variable. -/
theorem hfMemTermAt_var (elem set : Nat) :
    hfMemTermAt elem (Term.var set) = hfMemAt elem set := by
  simp [hfMemTermAt, hfMemAt, betaTermAtConstIdx_var, Term.rename]

/-- The term-parametric membership macro specializes to the closed-zero set
membership macro. -/
theorem hfMemTermAt_zero (elem : Nat) :
    hfMemTermAt elem Term.zero = hfMemZeroSetAt elem := by
  simp [hfMemTermAt, hfMemZeroSetAt, Term.rename]

/-- Renaming through one fresh binder shifts both the element slot and the
set-code term in a term-parametric membership atom. -/
theorem rename_hfMemTermAt_succ (elem : Nat) (setCode : Term) :
    rename Nat.succ (hfMemTermAt elem setCode) =
      hfMemTermAt (elem+1) (Term.rename Nat.succ setCode) := by
  simp [hfMemTermAt, betaTermAtConstIdx, betaTermAt, remTermAt, ltTermAt,
    betaAt, remAt, ltAt, leAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaDiv2BitAt, betaAtSuccIdx, div2StepAt,
    boolAt, zeroAt, oneAt, eqConstAt, betaModTerm, rename, Term.rename,
    SetTheory.up, Term.rename_comp]

/-- Renaming the surrounding context while preserving the distinguished
element slot acts covariantly on the set-code term of `hfMemTermAt 0`. -/
theorem rename_hfMemTermAt_zero_up (r : Nat → Nat) (setCode : Term) :
    rename (SetTheory.up r) (hfMemTermAt 0 setCode) =
      hfMemTermAt 0 (Term.rename (SetTheory.up r) setCode) := by
  simp [hfMemTermAt, betaTermAtConstIdx, betaTermAt, remTermAt, ltTermAt,
    betaAt, remAt, ltAt, leAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaDiv2BitAt, betaAtSuccIdx, div2StepAt,
    boolAt, zeroAt, oneAt, eqConstAt, betaModTerm, rename, Term.rename,
    SetTheory.up, Term.rename_comp]

/-- Instantiating the bound element variable in a term-parametric
Ackermann-membership atom.  The set-code term is renamed by `Nat.succ` because
it sits one binder outside the member variable. -/
theorem subst_instTerm_var_hfMemTermAt_zero_rename_succ
    (elem : Nat) (setCode : Term) :
    subst (instTerm (Term.var elem))
        (hfMemTermAt 0 (Term.rename Nat.succ setCode)) =
      hfMemTermAt elem setCode := by
  simp [hfMemTermAt, betaTermAtConstIdx, betaTermAt, remTermAt, ltTermAt,
    betaAt, remAt, ltAt, leAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaDiv2BitAt, betaAtSuccIdx, div2StepAt,
    boolAt, zeroAt, oneAt, eqConstAt, betaModTerm, subst, instTerm,
    Term.subst, Term.upSubst, Term.rename, Term.rename_comp]
  constructor
  · change Term.subst (iterUpSubst 6 (instTerm (Term.var elem)))
        (Term.rename (fun n : Nat => n + 6 + 1) setCode) =
        Term.rename (fun n : Nat => n + 5 + 1) setCode
    have htarget :
        Term.rename (fun n : Nat => n + 6) setCode =
          Term.rename (fun n : Nat => n + 5 + 1) setCode :=
      Term.rename_ext setCode _ _ (fun n => by omega)
    simpa [htarget] using
      (term_subst_iterUpSubst_instTerm_var_rename_add_succ 6 elem setCode)
  · change Term.subst (iterUpSubst 5 (instTerm (Term.var elem)))
        (Term.rename (fun n : Nat => n + 5 + 1) setCode) =
        Term.rename (fun n : Nat => n + 4 + 1) setCode
    have htarget :
        Term.rename (fun n : Nat => n + 5) setCode =
          Term.rename (fun n : Nat => n + 4 + 1) setCode :=
      Term.rename_ext setCode _ _ (fun n => by omega)
    simpa [htarget] using
      (term_subst_iterUpSubst_instTerm_var_rename_add_succ 5 elem setCode)

/-- Instantiating the set-code slot of `hfMemAt` by an arbitrary PA term yields
the term-parametric membership macro. -/
theorem subst_instTerm_hfMemAt_succ_zero (elem : Nat) (setCode : Term) :
    subst (instTerm setCode) (hfMemAt (elem+1) 0) =
      hfMemTermAt elem setCode := by
  simp [hfMemTermAt, hfMemAt, betaTermAtConstIdx, betaTermAt,
    remTermAt, ltTermAt, betaAtConstIdx, betaAt, remAt, ltAt, leAt,
    betaDiv2StepsThroughAt, betaDiv2StepWitnessAt, betaDiv2BitAt,
    betaAtSuccIdx, div2StepAt, boolAt, zeroAt, oneAt, eqConstAt,
    betaModTerm, subst, instTerm, Term.subst, Term.upSubst, Term.rename,
    Term.rename_comp]

theorem subst_up_zero_hfMemAt_zero_set :
    subst (Term.upSubst (instTerm Term.zero)) (hfMemAt 0 1) =
      hfMemZeroSetAt 0 := by
  simp [hfMemZeroSetAt, hfMemAt, betaTermAtConstIdx, betaTermAt,
    remTermAt, ltTermAt, betaAtConstIdx, betaAt, remAt, ltAt,
    leAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt, betaDiv2BitAt,
    betaAtSuccIdx, div2StepAt, boolAt, zeroAt, oneAt, eqConstAt,
    betaModTerm, subst, instTerm, Term.subst, Term.upSubst,
    Term.rename]

/-- Instantiating the set slot in the one-variable context
`hfMemAt (elem+1) 0` by an existing PA variable recovers ordinary
Ackermann-membership at that set slot. -/
theorem subst_instTerm_var_hfMemAt_succ_zero (elem set : Nat) :
    subst (instTerm (Term.var set)) (hfMemAt (elem+1) 0) =
      hfMemAt elem set := by
  simp [hfMemAt, betaDiv2BitAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaAtSuccIdx, betaAtConstIdx, betaAt,
    remAt, ltAt, leAt, div2StepAt, boolAt, zeroAt, oneAt, eqConstAt,
    betaModTerm, subst, instTerm, Term.subst, Term.upSubst, Term.rename,
    Term.numeral]

/-- Instantiating the set slot in `hfMemAt (elem+1) 0` by the closed PA
numeral `0` yields the closed-zero-set membership formula. -/
theorem subst_instTerm_zero_hfMemAt_succ_zero (elem : Nat) :
    subst (instTerm Term.zero) (hfMemAt (elem+1) 0) =
      hfMemZeroSetAt elem := by
  simp [hfMemZeroSetAt, hfMemAt, betaTermAtConstIdx, betaTermAt,
    remTermAt, ltTermAt, betaDiv2BitAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaAtSuccIdx, betaAtConstIdx, betaAt,
    remAt, ltAt, leAt, div2StepAt, boolAt, zeroAt, oneAt, eqConstAt,
    betaModTerm, subst, instTerm, Term.subst, Term.upSubst, Term.rename,
    Term.numeral]

/-- Transport ordinary Ackermann membership in a set slot across a PA equality
to an arbitrary set-code term.  This is the proof-level bridge from the slot
macro to `hfMemTermAt`; the formula definitions themselves remain pure
abbreviations. -/
theorem BProv_hfMemTermAt_of_hfMemAt_eq_term
    {B : Formula → Prop} {G : List Formula} {elem set : Nat}
    {setCode : Term}
    (hmem : BProv B G (hfMemAt elem set))
    (hset : BProv B G (eq (Term.var set) setCode)) :
    BProv B G (hfMemTermAt elem setCode) := by
  have hmemSubst : BProv B G
      (subst (instTerm (Term.var set)) (hfMemAt (elem+1) 0)) := by
    simpa [subst_instTerm_var_hfMemAt_succ_zero] using hmem
  have htermSubst : BProv B G
      (subst (instTerm setCode) (hfMemAt (elem+1) 0)) :=
    BProv_eqElim (B := B) (G := G)
      (s := Term.var set) (t := setCode)
      (a := hfMemAt (elem+1) 0) hset hmemSubst
  simpa [subst_instTerm_hfMemAt_succ_zero] using htermSubst

/-- Transport term-parametric Ackermann membership across a PA equality between
set-code terms.  This is the term-code analogue of
`BProv_hfMemTermAt_of_hfMemAt_eq_term`; it keeps equality transport as a proof
operation rather than baking it into the membership macro. -/
theorem BProv_hfMemTermAt_of_hfMemTermAt_eq_term
    {B : Formula → Prop} {G : List Formula} {elem : Nat}
    {oldCode newCode : Term}
    (hmem : BProv B G (hfMemTermAt elem oldCode))
    (hset : BProv B G (eq oldCode newCode)) :
    BProv B G (hfMemTermAt elem newCode) := by
  have hmemSubst : BProv B G
      (subst (instTerm oldCode) (hfMemAt (elem+1) 0)) := by
    simpa [subst_instTerm_hfMemAt_succ_zero] using hmem
  have htermSubst : BProv B G
      (subst (instTerm newCode) (hfMemAt (elem+1) 0)) :=
    BProv_eqElim (B := B) (G := G)
      (s := oldCode) (t := newCode)
      (a := hfMemAt (elem+1) 0) hset hmemSubst
  simpa [subst_instTerm_hfMemAt_succ_zero] using htermSubst

theorem rename_hfMemAt (r : Nat → Nat) (elem set : Nat) :
    rename r (hfMemAt elem set) = hfMemAt (r elem) (r set) := by
  simp [hfMemAt, betaDiv2BitAt, betaDiv2StepsThroughAt,
    betaDiv2StepWitnessAt, betaAtSuccIdx, betaAtConstIdx, betaAt,
    remAt, ltAt, leAt, div2StepAt, boolAt, zeroAt, oneAt,
    eqConstAt, betaModTerm, rename, Term.rename, SetTheory.up]

theorem leAt_nat (e : Nat → Nat) (a b : Nat) :
    Sat natModel e (leAt a b) ↔ e a ≤ e b := by
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    simp only [Sat, Term.eval, natModel, scons] at hd
    change e a + d = e b at hd
    omega
  · intro h
    refine ⟨e b - e a, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    change e a + (e b - e a) = e b
    omega

theorem leConstAt_nat (e : Nat → Nat) (a n : Nat) :
    Sat natModel e (leConstAt a n) ↔ e a ≤ n := by
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    simp only [Sat] at hd
    rw [Term.eval_numeral_natModel] at hd
    simp only [Term.eval, natModel, scons] at hd
    change e a + d = n at hd
    omega
  · intro h
    refine ⟨n - e a, ?_⟩
    simp only [Sat]
    rw [Term.eval_numeral_natModel]
    simp only [Term.eval, natModel, scons]
    change e a + (n - e a) = n
    omega

theorem ltAt_nat (e : Nat → Nat) (a b : Nat) :
    Sat natModel e (ltAt a b) ↔ e a < e b := by
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    simp only [Sat, Term.eval, natModel, scons] at hd
    change e a + (d + 1) = e b at hd
    omega
  · intro h
    refine ⟨e b - e a - 1, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    change e a + ((e b - e a - 1) + 1) = e b
    omega

theorem leTermAt_nat (e : Nat → Nat) (a b : Term) :
    Sat natModel e (leTermAt a b) ↔
      Term.eval natModel e a ≤ Term.eval natModel e b := by
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    simp only [Sat, Term.eval, natModel, Term.eval_rename, scons] at hd
    change Term.eval natModel e a + d = Term.eval natModel e b at hd
    omega
  · intro h
    refine ⟨Term.eval natModel e b - Term.eval natModel e a, ?_⟩
    simp only [Sat, Term.eval, natModel, Term.eval_rename, scons]
    change Term.eval natModel e a +
        (Term.eval natModel e b - Term.eval natModel e a) =
      Term.eval natModel e b
    omega

theorem ltTermAt_nat (e : Nat → Nat) (a b : Term) :
    Sat natModel e (ltTermAt a b) ↔
      Term.eval natModel e a < Term.eval natModel e b := by
  constructor
  · intro h
    rcases h with ⟨d, hd⟩
    simp only [Sat, Term.eval, natModel, Term.eval_rename, scons] at hd
    change Term.eval natModel e a + (d + 1) =
      Term.eval natModel e b at hd
    omega
  · intro h
    refine ⟨Term.eval natModel e b - Term.eval natModel e a - 1, ?_⟩
    simp only [Sat, Term.eval, natModel, Term.eval_rename, scons]
    change Term.eval natModel e a +
        ((Term.eval natModel e b - Term.eval natModel e a - 1) + 1) =
      Term.eval natModel e b
    omega

theorem dvdAt_nat (e : Nat → Nat) (a b : Nat) :
    Sat natModel e (dvdAt a b) ↔ e a ∣ e b := by
  constructor
  · intro h
    rcases h with ⟨q, hq⟩
    simp only [Sat, Term.eval, natModel, scons] at hq
    change e a * q = e b at hq
    exact ⟨q, hq.symm⟩
  · intro h
    rcases h with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    change e a * q = e b
    exact hq.symm

theorem dvdTermTermAt_nat (e : Nat → Nat) (divisor value : Term) :
    Sat natModel e (dvdTermTermAt divisor value) ↔
      Term.eval natModel e divisor ∣ Term.eval natModel e value := by
  constructor
  · intro h
    rcases h with ⟨q, hq⟩
    simp only [Sat, Term.eval, natModel, Term.eval_rename, scons] at hq
    exact ⟨q, hq.symm⟩
  · intro h
    rcases h with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    simp only [Sat, Term.eval, natModel, Term.eval_rename, scons]
    exact hq.symm

theorem commonMultipleThroughTermAt_nat
    (e : Nat → Nat) (bound multiple : Term) :
    Sat natModel e (commonMultipleThroughTermAt bound multiple) ↔
      ∀ q, q < Term.eval natModel e bound →
        q + 1 ∣ Term.eval natModel e multiple := by
  constructor
  · intro h q hq
    have hqSat : Sat natModel (scons q e)
        (ltTermAt (Term.var 0) (Term.rename Nat.succ bound)) := by
      exact (ltTermAt_nat (scons q e)
        (Term.var 0) (Term.rename Nat.succ bound)).mpr (by
          simpa [Term.eval_rename, Term.eval, scons] using hq)
    have hdvd := (dvdTermTermAt_nat (scons q e)
      (Term.succ (Term.var 0))
      (Term.rename Nat.succ multiple)).mp (h q hqSat)
    simpa [Term.eval_rename, Term.eval, natModel,
      Nat.succ_eq_add_one, scons] using hdvd
  · intro h q hqSat
    have hq : q < Term.eval natModel e bound := by
      have hlt := (ltTermAt_nat (scons q e)
        (Term.var 0) (Term.rename Nat.succ bound)).mp hqSat
      simpa [Term.eval_rename, Term.eval, scons] using hlt
    apply (dvdTermTermAt_nat (scons q e)
      (Term.succ (Term.var 0))
      (Term.rename Nat.succ multiple)).mpr
    simpa [Term.eval_rename, Term.eval, natModel,
      Nat.succ_eq_add_one, scons] using h q hq

theorem commonMultipleExistsTermAt_nat
    (e : Nat → Nat) (bound : Term) :
    Sat natModel e (commonMultipleExistsTermAt bound) ↔
      ∃ multiple, ∀ q, q < Term.eval natModel e bound →
        q + 1 ∣ multiple := by
  constructor
  · intro h
    rcases h with ⟨multiple, hmultiple⟩
    refine ⟨multiple, ?_⟩
    have hspec := (commonMultipleThroughTermAt_nat
      (scons multiple e) (Term.rename Nat.succ bound)
      (Term.var 0)).mp hmultiple
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨multiple, hmultiple⟩
    refine ⟨multiple, ?_⟩
    apply (commonMultipleThroughTermAt_nat
      (scons multiple e) (Term.rename Nat.succ bound)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hmultiple

theorem positiveCommonMultipleThroughTermAt_nat
    (e : Nat → Nat) (bound multiple : Term) :
    Sat natModel e
      (positiveCommonMultipleThroughTermAt bound multiple) ↔
      0 < Term.eval natModel e multiple ∧
        ∀ q, q < Term.eval natModel e bound →
          q + 1 ∣ Term.eval natModel e multiple := by
  constructor
  · intro h
    exact ⟨(ltTermAt_nat e Term.zero multiple).mp h.1,
      (commonMultipleThroughTermAt_nat e bound multiple).mp h.2⟩
  · intro h
    exact ⟨(ltTermAt_nat e Term.zero multiple).mpr h.1,
      (commonMultipleThroughTermAt_nat e bound multiple).mpr h.2⟩

theorem positiveCommonMultipleExistsTermAt_nat
    (e : Nat → Nat) (bound : Term) :
    Sat natModel e (positiveCommonMultipleExistsTermAt bound) ↔
      ∃ multiple, 0 < multiple ∧
        ∀ q, q < Term.eval natModel e bound → q + 1 ∣ multiple := by
  constructor
  · intro h
    rcases h with ⟨multiple, hmultiple⟩
    refine ⟨multiple, ?_⟩
    have hspec := (positiveCommonMultipleThroughTermAt_nat
      (scons multiple e) (Term.rename Nat.succ bound)
      (Term.var 0)).mp hmultiple
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨multiple, hmultiple⟩
    refine ⟨multiple, ?_⟩
    apply (positiveCommonMultipleThroughTermAt_nat
      (scons multiple e) (Term.rename Nat.succ bound)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hmultiple

theorem betaCodingStepTermAt_nat
    (e : Nat → Nat) (bound sourceCode step : Term) :
    Sat natModel e (betaCodingStepTermAt bound sourceCode step) ↔
      (∀ q, q < Term.eval natModel e bound →
        q + 1 ∣ Term.eval natModel e step) ∧
      Term.eval natModel e sourceCode + 1 ≤
        Term.eval natModel e step := by
  constructor
  · intro h
    exact ⟨(commonMultipleThroughTermAt_nat e bound step).mp h.1,
      (leTermAt_nat e (Term.succ sourceCode) step).mp h.2⟩
  · intro h
    exact ⟨(commonMultipleThroughTermAt_nat e bound step).mpr h.1,
      (leTermAt_nat e (Term.succ sourceCode) step).mpr h.2⟩

theorem betaCodingStepExistsTermAt_nat
    (e : Nat → Nat) (bound sourceCode : Term) :
    Sat natModel e (betaCodingStepExistsTermAt bound sourceCode) ↔
      ∃ step,
        (∀ q, q < Term.eval natModel e bound → q + 1 ∣ step) ∧
        Term.eval natModel e sourceCode + 1 ≤ step := by
  constructor
  · intro h
    rcases h with ⟨step, hstep⟩
    refine ⟨step, ?_⟩
    have hspec := (betaCodingStepTermAt_nat
      (scons step e) (Term.rename Nat.succ bound)
      (Term.rename Nat.succ sourceCode) (Term.var 0)).mp hstep
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨step, hstep⟩
    refine ⟨step, ?_⟩
    apply (betaCodingStepTermAt_nat
      (scons step e) (Term.rename Nat.succ bound)
      (Term.rename Nat.succ sourceCode) (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hstep

theorem betaPrependCodingStepTermAt_nat
    (e : Nat → Nat) (bound sourceCode head step : Term) :
    Sat natModel e
      (betaPrependCodingStepTermAt bound sourceCode head step) ↔
      (∀ q, q < Term.eval natModel e bound →
        q + 1 ∣ Term.eval natModel e step) ∧
      Term.eval natModel e sourceCode + 1 ≤
        Term.eval natModel e step ∧
      Term.eval natModel e head + 1 ≤
        Term.eval natModel e step := by
  constructor
  · intro h
    exact ⟨(commonMultipleThroughTermAt_nat e bound step).mp h.1,
      (leTermAt_nat e (Term.succ sourceCode) step).mp h.2.1,
      (leTermAt_nat e (Term.succ head) step).mp h.2.2⟩
  · intro h
    exact ⟨(commonMultipleThroughTermAt_nat e bound step).mpr h.1,
      (leTermAt_nat e (Term.succ sourceCode) step).mpr h.2.1,
      (leTermAt_nat e (Term.succ head) step).mpr h.2.2⟩

theorem betaPrependCodingStepExistsTermAt_nat
    (e : Nat → Nat) (bound sourceCode head : Term) :
    Sat natModel e
      (betaPrependCodingStepExistsTermAt bound sourceCode head) ↔
      ∃ step,
        (∀ q, q < Term.eval natModel e bound → q + 1 ∣ step) ∧
        Term.eval natModel e sourceCode + 1 ≤ step ∧
        Term.eval natModel e head + 1 ≤ step := by
  constructor
  · intro h
    rcases h with ⟨step, hstep⟩
    refine ⟨step, ?_⟩
    have hspec := (betaPrependCodingStepTermAt_nat
      (scons step e)
      (Term.rename Nat.succ bound)
      (Term.rename Nat.succ sourceCode)
      (Term.rename Nat.succ head)
      (Term.var 0)).mp hstep
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨step, hstep⟩
    refine ⟨step, ?_⟩
    apply (betaPrependCodingStepTermAt_nat
      (scons step e)
      (Term.rename Nat.succ bound)
      (Term.rename Nat.succ sourceCode)
      (Term.rename Nat.succ head)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hstep

theorem crtInverseTermAt_nat
    (e : Nat → Nat) (product modulus inverse quotient : Term) :
    Sat natModel e
      (crtInverseTermAt product modulus inverse quotient) ↔
      Term.eval natModel e product * Term.eval natModel e inverse =
        Nat.succ
          (Term.eval natModel e modulus *
            Term.eval natModel e quotient) := by
  simp [crtInverseTermAt, Sat, Term.eval, natModel]

theorem crtInverseExistsTermAt_nat
    (e : Nat → Nat) (product modulus : Term) :
    Sat natModel e (crtInverseExistsTermAt product modulus) ↔
      ∃ inverse quotient,
        Term.eval natModel e product * inverse =
          Nat.succ (Term.eval natModel e modulus * quotient) := by
  constructor
  · intro h
    rcases h with ⟨inverse, quotient, hcert⟩
    refine ⟨inverse, quotient, ?_⟩
    have hspec := (crtInverseTermAt_nat
      (scons quotient (scons inverse e))
      (Term.rename (fun n => n + 2) product)
      (Term.rename (fun n => n + 2) modulus)
      (Term.var 1) (Term.var 0)).mp hcert
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨inverse, quotient, hcert⟩
    refine ⟨inverse, quotient, ?_⟩
    apply (crtInverseTermAt_nat
      (scons quotient (scons inverse e))
      (Term.rename (fun n => n + 2) product)
      (Term.rename (fun n => n + 2) modulus)
      (Term.var 1) (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hcert

theorem crtCorrectionTermAt_nat
    (e : Nat → Nat) (oldRem modulus newRem delta : Term) :
    Sat natModel e
      (crtCorrectionTermAt oldRem modulus newRem delta) ↔
      Term.eval natModel e oldRem + Term.eval natModel e delta =
        Term.eval natModel e modulus + Term.eval natModel e newRem := by
  simp [crtCorrectionTermAt, Sat, Term.eval, natModel]

theorem crtCorrectionExistsTermAt_nat
    (e : Nat → Nat) (oldRem modulus newRem : Term) :
    Sat natModel e
      (crtCorrectionExistsTermAt oldRem modulus newRem) ↔
      ∃ delta,
        Term.eval natModel e oldRem + delta =
          Term.eval natModel e modulus + Term.eval natModel e newRem := by
  constructor
  · intro h
    rcases h with ⟨delta, hdelta⟩
    refine ⟨delta, ?_⟩
    have hspec := (crtCorrectionTermAt_nat
      (scons delta e)
      (Term.rename Nat.succ oldRem)
      (Term.rename Nat.succ modulus)
      (Term.rename Nat.succ newRem)
      (Term.var 0)).mp hdelta
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨delta, hdelta⟩
    refine ⟨delta, ?_⟩
    apply (crtCorrectionTermAt_nat
      (scons delta e)
      (Term.rename Nat.succ oldRem)
      (Term.rename Nat.succ modulus)
      (Term.rename Nat.succ newRem)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hdelta

theorem crtSuccessorCorrectionTerm_nat
    (e : Nat → Nat) (oldCode modulusPred newRem : Term) :
    Term.eval natModel e
        (crtSuccessorCorrectionTerm oldCode modulusPred newRem) =
      Term.eval natModel e modulusPred * Term.eval natModel e oldCode +
        Term.eval natModel e newRem := by
  simp [crtSuccessorCorrectionTerm, Term.eval, natModel]

theorem eqConstAt_nat (e : Nat → Nat) (a n : Nat) :
    Sat natModel e (eqConstAt a n) ↔ e a = n := by
  simp only [eqConstAt, Sat, Term.eval, Term.eval_numeral_natModel]

theorem zeroAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (zeroAt a) ↔ e a = 0 :=
  eqConstAt_nat e a 0

theorem oneAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (oneAt a) ↔ e a = 1 :=
  eqConstAt_nat e a 1

theorem twoAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (twoAt a) ↔ e a = 2 :=
  eqConstAt_nat e a 2

theorem nonzeroAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (nonzeroAt a) ↔ e a ≠ 0 := by
  constructor
  · intro h hzero
    rcases h with ⟨d, hd⟩
    simp only [Sat, Term.eval, natModel, scons] at hd
    omega
  · intro h
    refine ⟨e a - 1, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    omega

theorem succPredAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (succPredAt a) ↔ ∃ p, e a = p + 1 := by
  constructor
  · intro h
    rcases h with ⟨p, hp⟩
    simp only [Sat, Term.eval, natModel, scons] at hp
    exact ⟨p, by omega⟩
  · intro h
    rcases h with ⟨p, hp⟩
    refine ⟨p, ?_⟩
    simp only [Sat, Term.eval, natModel, scons]
    omega

theorem zeroOrSuccPredAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (zeroOrSuccPredAt a) ↔
      e a = 0 ∨ ∃ p, e a = p + 1 := by
  simp only [zeroOrSuccPredAt, Sat]
  exact or_congr (zeroAt_nat e a) (succPredAt_nat e a)

theorem boolAt_nat (e : Nat → Nat) (a : Nat) :
    Sat natModel e (boolAt a) ↔ e a = 0 ∨ e a = 1 := by
  simp only [boolAt, Sat]
  exact or_congr (zeroAt_nat e a) (oneAt_nat e a)

theorem boolTermAt_nat (e : Nat → Nat) (a : Term) :
    Sat natModel e (boolTermAt a) ↔
      Term.eval natModel e a = 0 ∨ Term.eval natModel e a = 1 := by
  simp only [boolTermAt, Sat]
  constructor
  · intro h
    rcases h with h | h
    · left
      simpa [Term.eval, natModel] using h
    · right
      simpa [Term.numeral, Term.eval, natModel] using h
  · intro h
    rcases h with h | h
    · left
      simpa [Term.eval, natModel] using h
    · right
      simpa [Term.numeral, Term.eval, natModel] using h

theorem doubleEqAt_nat (e : Nat → Nat) (value half : Nat) :
    Sat natModel e (doubleEqAt value half) ↔ e value = e half + e half := by
  simp only [doubleEqAt, Sat, Term.eval, natModel]
  rfl

theorem oddDoubleEqAt_nat (e : Nat → Nat) (value half : Nat) :
    Sat natModel e (oddDoubleEqAt value half) ↔ e value = e half + e half + 1 := by
  simp only [oddDoubleEqAt, Sat, Term.eval, natModel]
  change e value = Nat.succ (e half + e half) ↔ e value = e half + e half + 1
  omega

theorem div2StepAt_nat (e : Nat → Nat) (value half bit : Nat) :
    Sat natModel e (div2StepAt value half bit) ↔
      (e bit = 0 ∨ e bit = 1) ∧ e value = e half + e half + e bit := by
  simp only [div2StepAt, Sat]
  constructor
  · intro h
    have hval : e value = e half + e half + e bit := by
      have hraw := h.2
      simp only [Term.eval, natModel] at hraw
      change e value = e half + e half + e bit at hraw
      exact hraw
    exact ⟨(boolAt_nat e bit).mp h.1, hval⟩
  · intro h
    exact ⟨(boolAt_nat e bit).mpr h.1, by
      simp only [Term.eval, natModel]
      change e value = e half + e half + e bit
      omega⟩

theorem div2StepTermAt_nat (e : Nat → Nat) (value half bit : Term) :
    Sat natModel e (div2StepTermAt value half bit) ↔
      (Term.eval natModel e bit = 0 ∨ Term.eval natModel e bit = 1) ∧
        Term.eval natModel e value =
          Term.eval natModel e half + Term.eval natModel e half +
            Term.eval natModel e bit := by
  simp only [div2StepTermAt, Sat]
  constructor
  · intro h
    have hval :
        Term.eval natModel e value =
          Term.eval natModel e half + Term.eval natModel e half +
            Term.eval natModel e bit := by
      have hraw := h.2
      simp only [Term.eval, natModel] at hraw
      exact hraw
    exact ⟨(boolTermAt_nat e bit).mp h.1, hval⟩
  · intro h
    exact ⟨(boolTermAt_nat e bit).mpr h.1, by
      simpa [Term.eval, natModel, Nat.add_assoc] using h.2⟩

theorem betaModTerm_nat (e : Nat → Nat) (step idx : Nat) :
    Term.eval natModel e (betaModTerm step idx) = 1 + (e idx + 1) * e step := by
  simp only [betaModTerm, Term.eval, natModel]
  change Nat.succ ((e idx + 1) * e step) = 1 + (e idx + 1) * e step
  omega

theorem betaModTermTerm_nat (e : Nat → Nat) (step idx : Term) :
    Term.eval natModel e (betaModTermTerm step idx) =
      1 + (Term.eval natModel e idx + 1) * Term.eval natModel e step := by
  simp only [betaModTermTerm, Term.eval, natModel]
  change Nat.succ
      ((Term.eval natModel e idx + 1) * Term.eval natModel e step) =
    1 + (Term.eval natModel e idx + 1) * Term.eval natModel e step
  omega

theorem betaPrefixDividesTermAt_nat
    (e : Nat → Nat) (step bound product : Term) :
    Sat natModel e (betaPrefixDividesTermAt step bound product) ↔
      ∀ i, i < Term.eval natModel e bound →
        BetaModulus (Term.eval natModel e step) i ∣
          Term.eval natModel e product := by
  constructor
  · intro h i hi
    have hiSat : Sat natModel (scons i e)
        (ltTermAt (Term.var 0) (Term.rename Nat.succ bound)) := by
      exact (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mpr (by
          simpa [Term.eval_rename, Term.eval, scons] using hi)
    have hdvd := (dvdTermTermAt_nat (scons i e)
      (betaModTermTerm (Term.rename Nat.succ step) (Term.var 0))
      (Term.rename Nat.succ product)).mp (h i hiSat)
    simpa [BetaModulus, betaModTermTerm_nat,
      Term.eval_rename, Term.eval, scons, Nat.add_comm] using hdvd
  · intro h i hiSat
    have hi : i < Term.eval natModel e bound := by
      have hlt := (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mp hiSat
      simpa [Term.eval_rename, Term.eval, scons] using hlt
    apply (dvdTermTermAt_nat (scons i e)
      (betaModTermTerm (Term.rename Nat.succ step) (Term.var 0))
      (Term.rename Nat.succ product)).mpr
    simpa [BetaModulus, betaModTermTerm_nat,
      Term.eval_rename, Term.eval, scons, Nat.add_comm] using h i hi

theorem betaPrefixCRTAccumulatorTermAt_nat
    (e : Nat → Nat) (step target bound product : Term) :
    Sat natModel e
      (betaPrefixCRTAccumulatorTermAt step target bound product) ↔
      (∀ i, i < Term.eval natModel e bound →
        BetaModulus (Term.eval natModel e step) i ∣
          Term.eval natModel e product) ∧
      ∃ inverse quotient,
        Term.eval natModel e product * inverse =
          Nat.succ
            (BetaModulus (Term.eval natModel e step)
              (Term.eval natModel e target) * quotient) := by
  constructor
  · intro h
    refine ⟨(betaPrefixDividesTermAt_nat
      e step bound product).mp h.1, ?_⟩
    have hinv := (crtInverseExistsTermAt_nat e product
      (betaModTermTerm step target)).mp h.2
    simpa [BetaModulus, betaModTermTerm_nat, Nat.add_comm] using hinv
  · intro h
    refine ⟨(betaPrefixDividesTermAt_nat
      e step bound product).mpr h.1, ?_⟩
    apply (crtInverseExistsTermAt_nat e product
      (betaModTermTerm step target)).mpr
    simpa [BetaModulus, betaModTermTerm_nat, Nat.add_comm] using h.2

theorem betaPrefixCRTAccumulatorExistsTermAt_nat
    (e : Nat → Nat) (step target bound : Term) :
    Sat natModel e
      (betaPrefixCRTAccumulatorExistsTermAt step target bound) ↔
      ∃ product,
        (∀ i, i < Term.eval natModel e bound →
          BetaModulus (Term.eval natModel e step) i ∣ product) ∧
        ∃ inverse quotient,
          product * inverse =
            Nat.succ
              (BetaModulus (Term.eval natModel e step)
                (Term.eval natModel e target) * quotient) := by
  constructor
  · intro h
    rcases h with ⟨product, hproduct⟩
    refine ⟨product, ?_⟩
    have hspec := (betaPrefixCRTAccumulatorTermAt_nat
      (scons product e)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ target)
      (Term.rename Nat.succ bound)
      (Term.var 0)).mp hproduct
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨product, hproduct⟩
    refine ⟨product, ?_⟩
    apply (betaPrefixCRTAccumulatorTermAt_nat
      (scons product e)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ target)
      (Term.rename Nat.succ bound)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hproduct

theorem remAt_nat (e : Nat → Nat) (rem value modulus : Nat) :
    Sat natModel e (remAt rem value modulus) ↔
      ∃ q, e value = q * e modulus + e rem ∧ e rem < e modulus := by
  constructor
  · intro h
    rcases h with ⟨q, hlt, hval⟩
    refine ⟨q, ?_, ?_⟩
    · simp only [Sat, Term.eval, natModel, scons] at hval
      change e value = q * e modulus + e rem at hval
      exact hval
    · exact (ltAt_nat (scons q e) (rem+1) (modulus+1)).mp hlt
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    refine ⟨q, ?_, ?_⟩
    · exact (ltAt_nat (scons q e) (rem+1) (modulus+1)).mpr hlt
    · simp only [Sat, Term.eval, natModel, scons]
      change e value = q * e modulus + e rem
      exact hval

theorem remTermTermAt_nat
    (e : Nat → Nat) (rem value modulus : Term) :
    Sat natModel e (remTermTermAt rem value modulus) ↔
      ∃ q,
        Term.eval natModel e value =
          q * Term.eval natModel e modulus + Term.eval natModel e rem ∧
        Term.eval natModel e rem < Term.eval natModel e modulus := by
  constructor
  · intro h
    rcases h with ⟨q, hlt, hval⟩
    refine ⟨q, ?_, ?_⟩
    · simp only [Sat, Term.eval, natModel, Term.eval_rename, scons] at hval
      change Term.eval natModel e value =
        q * Term.eval natModel e modulus + Term.eval natModel e rem at hval
      exact hval
    · have hlt' := (ltTermAt_nat (scons q e)
          (Term.rename Nat.succ rem)
          (Term.rename Nat.succ modulus)).mp hlt
      simpa [Term.eval_rename, scons] using hlt'
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    refine ⟨q, ?_, ?_⟩
    · exact (ltTermAt_nat (scons q e)
        (Term.rename Nat.succ rem)
        (Term.rename Nat.succ modulus)).mpr (by
          simpa [Term.eval_rename, scons] using hlt)
    · simp only [Sat, Term.eval, natModel, Term.eval_rename, scons]
      change Term.eval natModel e value =
        q * Term.eval natModel e modulus + Term.eval natModel e rem
      exact hval

theorem betaAt_nat (e : Nat → Nat) (out code step idx : Nat) :
    Sat natModel e (betaAt out code step idx) ↔
      ∃ q,
        e code = q * (1 + (e idx + 1) * e step) + e out ∧
          e out < 1 + (e idx + 1) * e step := by
  constructor
  · intro h
    rcases h with ⟨m, hmod, hrem⟩
    have hm : m = 1 + (e idx + 1) * e step := by
      simp only [Sat, Term.eval_rename, betaModTerm_nat, scons] at hmod
      exact hmod
    rcases (remAt_nat (scons m e) (out+1) (code+1) 0).mp hrem with
      ⟨q, hval, hlt⟩
    refine ⟨q, ?_, ?_⟩
    · simpa [scons, hm] using hval
    · simpa [scons, hm] using hlt
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    let m := 1 + (e idx + 1) * e step
    refine ⟨m, ?_, ?_⟩
    · simp only [Sat, Term.eval_rename, betaModTerm_nat, scons]
      rfl
    · apply (remAt_nat (scons m e) (out+1) (code+1) 0).mpr
      refine ⟨q, ?_, ?_⟩
      · simpa [scons, m] using hval
      · simpa [scons, m] using hlt

theorem betaAtConstIdx_nat (e : Nat → Nat) (out code step idxValue : Nat) :
    Sat natModel e (betaAtConstIdx out code step idxValue) ↔
      ∃ q,
        e code = q * (1 + (idxValue + 1) * e step) + e out ∧
          e out < 1 + (idxValue + 1) * e step := by
  constructor
  · intro h
    rcases h with ⟨i, hi, hbeta⟩
    have hi' : i = idxValue := (eqConstAt_nat (scons i e) 0 idxValue).mp hi
    rcases (betaAt_nat (scons i e) (out+1) (code+1) (step+1) 0).mp hbeta with
      ⟨q, hval, hlt⟩
    subst hi'
    exact ⟨q, by simpa [scons] using hval, by simpa [scons] using hlt⟩
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    refine ⟨idxValue, ?_, ?_⟩
    · exact (eqConstAt_nat (scons idxValue e) 0 idxValue).mpr rfl
    · apply (betaAt_nat (scons idxValue e) (out+1) (code+1) (step+1) 0).mpr
      exact ⟨q, by simpa [scons] using hval, by simpa [scons] using hlt⟩

theorem betaAtSuccIdx_nat (e : Nat → Nat) (out code step idx : Nat) :
    Sat natModel e (betaAtSuccIdx out code step idx) ↔
      ∃ q,
        e code = q * (1 + (e idx + 1 + 1) * e step) + e out ∧
          e out < 1 + (e idx + 1 + 1) * e step := by
  constructor
  · intro h
    rcases h with ⟨i, hi, hbeta⟩
    have hi' : i = e idx + 1 := by
      simp only [Sat, Term.eval, natModel, scons] at hi
      exact hi
    rcases (betaAt_nat (scons i e) (out+1) (code+1) (step+1) 0).mp hbeta with
      ⟨q, hval, hlt⟩
    subst hi'
    exact ⟨q, by simpa [scons] using hval, by simpa [scons] using hlt⟩
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    refine ⟨e idx + 1, ?_, ?_⟩
    · simp only [Sat, Term.eval, natModel, scons]
    · apply (betaAt_nat (scons (e idx + 1) e) (out+1) (code+1) (step+1) 0).mpr
      exact ⟨q, by simpa [scons] using hval, by simpa [scons] using hlt⟩

theorem betaAt_nat_entry (e : Nat → Nat) (out code step idx : Nat) :
    Sat natModel e (betaAt out code step idx) ↔
      BetaEntry (e code) (e step) (e idx) (e out) := by
  exact betaAt_nat e out code step idx

theorem betaAtConstIdx_nat_entry
    (e : Nat → Nat) (out code step idxValue : Nat) :
    Sat natModel e (betaAtConstIdx out code step idxValue) ↔
      BetaEntry (e code) (e step) idxValue (e out) := by
  exact betaAtConstIdx_nat e out code step idxValue

theorem betaAtSuccIdx_nat_entry
    (e : Nat → Nat) (out code step idx : Nat) :
    Sat natModel e (betaAtSuccIdx out code step idx) ↔
      BetaEntry (e code) (e step) (e idx + 1) (e out) := by
  exact betaAtSuccIdx_nat e out code step idx

theorem betaTermTermAt_nat_entry
    (e : Nat → Nat) (out code step idx : Term) :
    Sat natModel e (betaTermTermAt out code step idx) ↔
      BetaEntry
        (Term.eval natModel e code)
        (Term.eval natModel e step)
        (Term.eval natModel e idx)
        (Term.eval natModel e out) := by
  constructor
  · intro h
    rcases h with ⟨m, hmod, hrem⟩
    have hm :
        m =
          1 + (Term.eval natModel e idx + 1) *
            Term.eval natModel e step := by
      simp only [Sat, Term.eval_rename, betaModTermTerm_nat, scons] at hmod
      exact hmod
    rcases (remTermTermAt_nat (scons m e)
        (Term.rename Nat.succ out)
        (Term.rename Nat.succ code) (Term.var 0)).mp hrem with
      ⟨q, hval, hlt⟩
    refine ⟨q, ?_, ?_⟩
    · calc
        Term.eval natModel e code =
            Term.eval natModel (scons m e) (Term.rename Nat.succ code) := by
              simp [Term.eval_rename, scons]
        _ = q * Term.eval natModel (scons m e) (Term.var 0) +
              Term.eval natModel (scons m e) (Term.rename Nat.succ out) :=
              hval
        _ = q * BetaModulus (Term.eval natModel e step)
              (Term.eval natModel e idx) + Term.eval natModel e out := by
              simp [BetaModulus, Term.eval_rename, Term.eval, scons, hm]
    · calc
        Term.eval natModel e out =
            Term.eval natModel (scons m e) (Term.rename Nat.succ out) := by
              simp [Term.eval_rename, scons]
        _ < Term.eval natModel (scons m e) (Term.var 0) := hlt
        _ = BetaModulus (Term.eval natModel e step)
              (Term.eval natModel e idx) := by
              simp [BetaModulus, Term.eval, scons, hm]
  · intro h
    rcases h with ⟨q, hval, hlt⟩
    let m :=
      BetaModulus (Term.eval natModel e step) (Term.eval natModel e idx)
    refine ⟨m, ?_, ?_⟩
    · simp only [Sat, Term.eval_rename, betaModTermTerm_nat, scons]
      change m =
        1 + (Term.eval natModel e idx + 1) * Term.eval natModel e step
      simp [m, BetaModulus]
    · apply (remTermTermAt_nat (scons m e)
        (Term.rename Nat.succ out)
        (Term.rename Nat.succ code) (Term.var 0)).mpr
      refine ⟨q, ?_, ?_⟩
      · calc
          Term.eval natModel (scons m e) (Term.rename Nat.succ code) =
              Term.eval natModel e code := by
                simp [Term.eval_rename, scons]
          _ = q * m + Term.eval natModel e out := by
                simpa [m, BetaModulus] using hval
          _ = q * Term.eval natModel (scons m e) (Term.var 0) +
                Term.eval natModel (scons m e)
                  (Term.rename Nat.succ out) := by
                simp [Term.eval_rename, Term.eval, scons]
      · have hltM : Term.eval natModel e out < m := by
          simpa [m, BetaModulus] using hlt
        simpa [Term.eval_rename, Term.eval, scons] using hltM

theorem betaEntryExistsTermAt_nat
    (e : Nat → Nat) (code step idx : Term) :
    Sat natModel e (betaEntryExistsTermAt code step idx) ↔
      ∃ out,
        BetaEntry (Term.eval natModel e code)
          (Term.eval natModel e step)
          (Term.eval natModel e idx) out := by
  constructor
  · intro h
    rcases h with ⟨out, hentry⟩
    refine ⟨out, ?_⟩
    have hspec := (betaTermTermAt_nat_entry (scons out e)
      (Term.var 0) (Term.rename Nat.succ code)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ idx)).mp hentry
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨out, hentry⟩
    refine ⟨out, ?_⟩
    apply (betaTermTermAt_nat_entry (scons out e)
      (Term.var 0) (Term.rename Nat.succ code)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ idx)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hentry

theorem betaPrefixAgreementTermAt_nat
    (e : Nat → Nat) (oldCode newCode step bound : Term) :
    Sat natModel e
      (betaPrefixAgreementTermAt oldCode newCode step bound) ↔
      ∀ i, i < Term.eval natModel e bound → ∀ out,
        BetaEntry (Term.eval natModel e oldCode)
            (Term.eval natModel e step) i out →
          BetaEntry (Term.eval natModel e newCode)
            (Term.eval natModel e step) i out := by
  constructor
  · intro h i hi out hold
    have hltSat : Sat natModel (scons i e)
        (ltTermAt (Term.var 0) (Term.rename Nat.succ bound)) :=
      (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mpr (by
          simpa [Term.eval_rename, Term.eval, scons] using hi)
    have houtImp := h i hltSat
    have holdSat : Sat natModel (scons out (scons i e))
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n => n + 2) oldCode)
          (Term.rename (fun n => n + 2) step)
          (Term.var 1)) :=
      (betaTermTermAt_nat_entry (scons out (scons i e))
        (Term.var 0)
        (Term.rename (fun n => n + 2) oldCode)
        (Term.rename (fun n => n + 2) step)
        (Term.var 1)).mpr (by
          simpa [Term.eval_rename, Term.eval, scons] using hold)
    have hnewSat := houtImp out holdSat
    have hnew := (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) newCode)
      (Term.rename (fun n => n + 2) step)
      (Term.var 1)).mp hnewSat
    simpa [Term.eval_rename, Term.eval, scons] using hnew
  · intro h i hltSat out holdSat
    have hi : i < Term.eval natModel e bound := by
      have hlt := (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mp hltSat
      simpa [Term.eval_rename, Term.eval, scons] using hlt
    have hold := (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) oldCode)
      (Term.rename (fun n => n + 2) step)
      (Term.var 1)).mp holdSat
    apply (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) newCode)
      (Term.rename (fun n => n + 2) step)
      (Term.var 1)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using
      h i hi out (by
        simpa [Term.eval_rename, Term.eval, scons] using hold)

theorem betaCodeExtensionTermAt_nat
    (e : Nat → Nat) (oldCode step target newOut newCode : Term) :
    Sat natModel e
      (betaCodeExtensionTermAt oldCode step target newOut newCode) ↔
      (∀ i, i < Term.eval natModel e target → ∀ out,
        BetaEntry (Term.eval natModel e oldCode)
            (Term.eval natModel e step) i out →
          BetaEntry (Term.eval natModel e newCode)
            (Term.eval natModel e step) i out) ∧
      BetaEntry (Term.eval natModel e newCode)
        (Term.eval natModel e step)
        (Term.eval natModel e target)
        (Term.eval natModel e newOut) := by
  simp only [betaCodeExtensionTermAt, Sat]
  exact and_congr
    (betaPrefixAgreementTermAt_nat e oldCode newCode step target)
    (betaTermTermAt_nat_entry e newOut newCode step target)

theorem betaCodeExtensionExistsTermAt_nat
    (e : Nat → Nat) (oldCode step target newOut : Term) :
    Sat natModel e
      (betaCodeExtensionExistsTermAt oldCode step target newOut) ↔
      ∃ newCode,
        (∀ i, i < Term.eval natModel e target → ∀ out,
          BetaEntry (Term.eval natModel e oldCode)
              (Term.eval natModel e step) i out →
            BetaEntry newCode (Term.eval natModel e step) i out) ∧
        BetaEntry newCode (Term.eval natModel e step)
          (Term.eval natModel e target)
          (Term.eval natModel e newOut) := by
  constructor
  · intro h
    rcases h with ⟨newCode, hext⟩
    refine ⟨newCode, ?_⟩
    have hspec := (betaCodeExtensionTermAt_nat
      (scons newCode e)
      (Term.rename Nat.succ oldCode)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ target)
      (Term.rename Nat.succ newOut)
      (Term.var 0)).mp hext
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨newCode, hext⟩
    refine ⟨newCode, ?_⟩
    apply (betaCodeExtensionTermAt_nat
      (scons newCode e)
      (Term.rename Nat.succ oldCode)
      (Term.rename Nat.succ step)
      (Term.rename Nat.succ target)
      (Term.rename Nat.succ newOut)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hext

theorem betaDiv2StepWitnessAt_nat (e : Nat → Nat) (code step idx : Nat) :
    Sat natModel e (betaDiv2StepWitnessAt code step idx) ↔
      ∃ cur next bit,
        BetaEntry (e code) (e step) (e idx) cur ∧
        BetaEntry (e code) (e step) (e idx + 1) next ∧
        (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
  constructor
  · intro h
    rcases h with ⟨cur, next, bit, hcur, hnext, hstep⟩
    let E := scons bit (scons next (scons cur e))
    have hcur' :
        BetaEntry (e code) (e step) (e idx) cur := by
      have hc := (betaAt_nat_entry E 2 (code+3) (step+3) (idx+3)).mp hcur
      simpa [E, scons] using hc
    have hnext' :
        BetaEntry (e code) (e step) (e idx + 1) next := by
      have hn := (betaAtSuccIdx_nat_entry E 1 (code+3) (step+3) (idx+3)).mp hnext
      simpa [E, scons, Nat.add_assoc] using hn
    have hstep' :
        (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
      have hs := (div2StepAt_nat E 2 1 0).mp hstep
      simpa [E, scons] using hs
    exact ⟨cur, next, bit, hcur', hnext', hstep'⟩
  · intro h
    rcases h with ⟨cur, next, bit, hcur, hnext, hstep⟩
    refine ⟨cur, next, bit, ?_, ?_, ?_⟩
    · let E := scons bit (scons next (scons cur e))
      apply (betaAt_nat_entry E 2 (code+3) (step+3) (idx+3)).mpr
      simpa [E, scons] using hcur
    · let E := scons bit (scons next (scons cur e))
      apply (betaAtSuccIdx_nat_entry E 1 (code+3) (step+3) (idx+3)).mpr
      simpa [E, scons, Nat.add_assoc] using hnext
    · let E := scons bit (scons next (scons cur e))
      apply (div2StepAt_nat E 2 1 0).mpr
      simpa [E, scons] using hstep

theorem betaDiv2StepWitnessTermAt_nat
    (e : Nat → Nat) (code step idx : Term) :
    Sat natModel e (betaDiv2StepWitnessTermAt code step idx) ↔
      ∃ cur next bit,
        BetaDiv2Step
          (Term.eval natModel e code)
          (Term.eval natModel e step)
          (Term.eval natModel e idx) cur next bit := by
  constructor
  · intro h
    rcases h with ⟨cur, next, bit, hcur, hnext, hstep⟩
    let E := scons bit (scons next (scons cur e))
    have hcur' :
        BetaEntry (Term.eval natModel e code)
          (Term.eval natModel e step) (Term.eval natModel e idx) cur := by
      have hc := (betaTermTermAt_nat_entry E (Term.var 2)
        (Term.rename (fun n => n+3) code)
        (Term.rename (fun n => n+3) step)
        (Term.rename (fun n => n+3) idx)).mp hcur
      simpa [E, Term.eval_rename, Term.eval, scons, Nat.add_assoc] using hc
    have hnext' :
        BetaEntry (Term.eval natModel e code)
          (Term.eval natModel e step) (Term.eval natModel e idx + 1)
          next := by
      have hn := (betaTermTermAt_nat_entry E (Term.var 1)
        (Term.rename (fun n => n+3) code)
        (Term.rename (fun n => n+3) step)
        (Term.succ (Term.rename (fun n => n+3) idx))).mp hnext
      simpa [E, Term.eval_rename, Term.eval, natModel, scons,
        Nat.add_assoc] using hn
    have hstep' :
        (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
      have hs := (div2StepTermAt_nat E
        (Term.var 2) (Term.var 1) (Term.var 0)).mp hstep
      simpa [E, Term.eval, scons] using hs
    exact ⟨cur, next, bit, hcur', hnext', hstep'.1, hstep'.2⟩
  · intro h
    rcases h with ⟨cur, next, bit, hcur, hnext, hbit, hvalue⟩
    refine ⟨cur, next, bit, ?_, ?_, ?_⟩
    · let E := scons bit (scons next (scons cur e))
      apply (betaTermTermAt_nat_entry E (Term.var 2)
        (Term.rename (fun n => n+3) code)
        (Term.rename (fun n => n+3) step)
        (Term.rename (fun n => n+3) idx)).mpr
      simpa [E, Term.eval_rename, Term.eval, scons, Nat.add_assoc] using hcur
    · let E := scons bit (scons next (scons cur e))
      apply (betaTermTermAt_nat_entry E (Term.var 1)
        (Term.rename (fun n => n+3) code)
        (Term.rename (fun n => n+3) step)
        (Term.succ (Term.rename (fun n => n+3) idx))).mpr
      simpa [E, Term.eval_rename, Term.eval, natModel, scons,
        Nat.add_assoc] using hnext
    · let E := scons bit (scons next (scons cur e))
      apply (div2StepTermAt_nat E
        (Term.var 2) (Term.var 1) (Term.var 0)).mpr
      simpa [E, Term.eval, scons] using And.intro hbit hvalue

theorem betaDiv2StepAt_nat (e : Nat → Nat) (code step limit : Nat) :
    Sat natModel e (betaDiv2StepAt code step limit) ↔
      ∀ k, k < e limit →
        ∃ cur next bit,
          BetaEntry (e code) (e step) k cur ∧
          BetaEntry (e code) (e step) (k+1) next ∧
          (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
  constructor
  · intro h k hk
    have hkSat :
        Sat natModel (scons k e) (ltAt 0 (limit+1)) := by
      exact (ltAt_nat (scons k e) 0 (limit+1)).mpr (by
        simpa [scons] using hk)
    have hw := (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mp
      (h k hkSat)
    simpa [scons] using hw
  · intro h k hkSat
    have hk : k < e limit := by
      have hlt := (ltAt_nat (scons k e) 0 (limit+1)).mp hkSat
      simpa [scons] using hlt
    apply (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mpr
    simpa [scons] using h k hk

theorem betaDiv2StepsThroughAt_nat (e : Nat → Nat) (code step last : Nat) :
    Sat natModel e (betaDiv2StepsThroughAt code step last) ↔
      ∀ k, k ≤ e last →
        ∃ cur next bit,
          BetaEntry (e code) (e step) k cur ∧
          BetaEntry (e code) (e step) (k+1) next ∧
          (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
  constructor
  · intro h k hk
    have hkSat :
        Sat natModel (scons k e) (leAt 0 (last+1)) := by
      exact (leAt_nat (scons k e) 0 (last+1)).mpr (by
        simpa [scons] using hk)
    have hw := (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mp
      (h k hkSat)
    simpa [scons] using hw
  · intro h k hkSat
    have hk : k ≤ e last := by
      have hle := (leAt_nat (scons k e) 0 (last+1)).mp hkSat
      simpa [scons] using hle
    apply (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mpr
    simpa [scons] using h k hk

theorem betaDiv2StepsThroughTermAt_nat
    (e : Nat → Nat) (code step : Nat) (last : Term) :
    Sat natModel e (betaDiv2StepsThroughTermAt code step last) ↔
      BetaDiv2StepsThrough (e code) (e step) (Term.eval natModel e last) := by
  constructor
  · intro h k hk
    have hkSat :
        Sat natModel (scons k e)
          (leTermAt (Term.var 0) (Term.rename Nat.succ last)) := by
      exact (leTermAt_nat (scons k e)
          (Term.var 0) (Term.rename Nat.succ last)).mpr (by
        calc
          Term.eval natModel (scons k e) (Term.var 0) = k := by
            simp [Term.eval, scons]
          _ ≤ Term.eval natModel e last := hk
          _ = Term.eval natModel (scons k e)
                (Term.rename Nat.succ last) := by
            simp [Term.eval_rename, scons])
    have hw := (betaDiv2StepWitnessAt_nat (scons k e)
      (code+1) (step+1) 0).mp (h k hkSat)
    rcases hw with ⟨cur, next, bit, hcur, hnext, hbit, hvalue⟩
    exact ⟨cur, next, bit, by
      simpa [BetaDiv2Step, scons] using
        And.intro hcur (And.intro hnext (And.intro hbit hvalue))⟩
  · intro h k hkSat
    have hk : k ≤ Term.eval natModel e last := by
      have hle := (leTermAt_nat (scons k e)
          (Term.var 0) (Term.rename Nat.succ last)).mp hkSat
      calc
        k = Term.eval natModel (scons k e) (Term.var 0) := by
          simp [Term.eval, scons]
        _ ≤ Term.eval natModel (scons k e)
            (Term.rename Nat.succ last) := hle
        _ = Term.eval natModel e last := by
          simp [Term.eval_rename, scons]
    rcases h k hk with ⟨cur, next, bit, hdiv⟩
    rcases hdiv with ⟨hcur, hnext, hbit, hvalue⟩
    apply (betaDiv2StepWitnessAt_nat (scons k e)
      (code+1) (step+1) 0).mpr
    exact ⟨cur, next, bit, by simpa [scons] using hcur,
      by simpa [scons] using hnext, by
        simpa using And.intro hbit hvalue⟩

theorem betaShiftPrefixTermAt_nat
    (e : Nat → Nat) (oldCode oldStep newCode newStep bound : Term) :
    Sat natModel e
      (betaShiftPrefixTermAt
        oldCode oldStep newCode newStep bound) ↔
      ∀ i, i < Term.eval natModel e bound → ∀ out,
        BetaEntry (Term.eval natModel e oldCode)
            (Term.eval natModel e oldStep) (i + 1) out →
          BetaEntry (Term.eval natModel e newCode)
            (Term.eval natModel e newStep) i out := by
  constructor
  · intro h i hi out hold
    have hltSat : Sat natModel (scons i e)
        (ltTermAt (Term.var 0) (Term.rename Nat.succ bound)) :=
      (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mpr (by
          simpa [Term.eval_rename, Term.eval, scons] using hi)
    have houtImp := h i hltSat
    have holdSat : Sat natModel (scons out (scons i e))
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n => n + 2) oldCode)
          (Term.rename (fun n => n + 2) oldStep)
          (Term.succ (Term.var 1))) :=
      (betaTermTermAt_nat_entry (scons out (scons i e))
        (Term.var 0)
        (Term.rename (fun n => n + 2) oldCode)
        (Term.rename (fun n => n + 2) oldStep)
        (Term.succ (Term.var 1))).mpr (by
          simpa [Term.eval_rename, Term.eval, natModel, scons,
            Nat.succ_eq_add_one] using hold)
    have hnewSat := houtImp out holdSat
    have hnew := (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) newCode)
      (Term.rename (fun n => n + 2) newStep)
      (Term.var 1)).mp hnewSat
    simpa [Term.eval_rename, Term.eval, scons] using hnew
  · intro h i hltSat out holdSat
    have hi : i < Term.eval natModel e bound := by
      have hlt := (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mp hltSat
      simpa [Term.eval_rename, Term.eval, scons] using hlt
    have hold := (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) oldCode)
      (Term.rename (fun n => n + 2) oldStep)
      (Term.succ (Term.var 1))).mp holdSat
    apply (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) newCode)
      (Term.rename (fun n => n + 2) newStep)
      (Term.var 1)).mpr
    simpa [Term.eval_rename, Term.eval, natModel, scons,
      Nat.succ_eq_add_one] using
      h i hi out (by
        simpa [Term.eval_rename, Term.eval, natModel, scons,
          Nat.succ_eq_add_one] using hold)

theorem betaShiftPrefixCodeExistsTermAt_nat
    (e : Nat → Nat) (oldCode oldStep newStep bound : Term) :
    Sat natModel e
      (betaShiftPrefixCodeExistsTermAt
        oldCode oldStep newStep bound) ↔
      ∃ newCode, ∀ i, i < Term.eval natModel e bound → ∀ out,
        BetaEntry (Term.eval natModel e oldCode)
            (Term.eval natModel e oldStep) (i + 1) out →
          BetaEntry newCode (Term.eval natModel e newStep) i out := by
  constructor
  · intro h
    rcases h with ⟨newCode, hprefix⟩
    refine ⟨newCode, ?_⟩
    have hspec := (betaShiftPrefixTermAt_nat
      (scons newCode e)
      (Term.rename Nat.succ oldCode)
      (Term.rename Nat.succ oldStep)
      (Term.var 0)
      (Term.rename Nat.succ newStep)
      (Term.rename Nat.succ bound)).mp hprefix
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨newCode, hprefix⟩
    refine ⟨newCode, ?_⟩
    apply (betaShiftPrefixTermAt_nat
      (scons newCode e)
      (Term.rename Nat.succ oldCode)
      (Term.rename Nat.succ oldStep)
      (Term.var 0)
      (Term.rename Nat.succ newStep)
      (Term.rename Nat.succ bound)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hprefix

theorem betaUnshiftPrefixTermAt_nat
    (e : Nat → Nat)
    (sourceCode sourceStep targetCode targetStep bound : Term) :
    Sat natModel e
      (betaUnshiftPrefixTermAt
        sourceCode sourceStep targetCode targetStep bound) ↔
      ∀ i, i < Term.eval natModel e bound → ∀ out,
        BetaEntry (Term.eval natModel e sourceCode)
            (Term.eval natModel e sourceStep) i out →
          BetaEntry (Term.eval natModel e targetCode)
            (Term.eval natModel e targetStep) (i + 1) out := by
  constructor
  · intro h i hi out hsource
    have hltSat : Sat natModel (scons i e)
        (ltTermAt (Term.var 0) (Term.rename Nat.succ bound)) :=
      (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mpr (by
          simpa [Term.eval_rename, Term.eval, scons] using hi)
    have houtImp := h i hltSat
    have hsourceSat : Sat natModel (scons out (scons i e))
        (betaTermTermAt (Term.var 0)
          (Term.rename (fun n => n + 2) sourceCode)
          (Term.rename (fun n => n + 2) sourceStep)
          (Term.var 1)) :=
      (betaTermTermAt_nat_entry (scons out (scons i e))
        (Term.var 0)
        (Term.rename (fun n => n + 2) sourceCode)
        (Term.rename (fun n => n + 2) sourceStep)
        (Term.var 1)).mpr (by
          simpa [Term.eval_rename, Term.eval, scons] using hsource)
    have htargetSat := houtImp out hsourceSat
    have htarget := (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) targetCode)
      (Term.rename (fun n => n + 2) targetStep)
      (Term.succ (Term.var 1))).mp htargetSat
    simpa [Term.eval_rename, Term.eval, natModel, scons,
      Nat.succ_eq_add_one] using htarget
  · intro h i hltSat out hsourceSat
    have hi : i < Term.eval natModel e bound := by
      have hlt := (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mp hltSat
      simpa [Term.eval_rename, Term.eval, scons] using hlt
    have hsource := (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) sourceCode)
      (Term.rename (fun n => n + 2) sourceStep)
      (Term.var 1)).mp hsourceSat
    apply (betaTermTermAt_nat_entry
      (scons out (scons i e))
      (Term.var 0)
      (Term.rename (fun n => n + 2) targetCode)
      (Term.rename (fun n => n + 2) targetStep)
      (Term.succ (Term.var 1))).mpr
    simpa [Term.eval_rename, Term.eval, natModel, scons,
      Nat.succ_eq_add_one] using h i hi out (by
        simpa [Term.eval_rename, Term.eval, scons] using hsource)

theorem betaUnshiftPrefixCodeExistsTermAt_nat
    (e : Nat → Nat) (sourceCode sourceStep targetStep bound : Term) :
    Sat natModel e
      (betaUnshiftPrefixCodeExistsTermAt
        sourceCode sourceStep targetStep bound) ↔
      ∃ targetCode, ∀ i, i < Term.eval natModel e bound → ∀ out,
        BetaEntry (Term.eval natModel e sourceCode)
            (Term.eval natModel e sourceStep) i out →
          BetaEntry targetCode (Term.eval natModel e targetStep)
            (i + 1) out := by
  constructor
  · intro h
    rcases h with ⟨targetCode, hprefix⟩
    refine ⟨targetCode, ?_⟩
    have hspec := (betaUnshiftPrefixTermAt_nat
      (scons targetCode e)
      (Term.rename Nat.succ sourceCode)
      (Term.rename Nat.succ sourceStep)
      (Term.var 0)
      (Term.rename Nat.succ targetStep)
      (Term.rename Nat.succ bound)).mp hprefix
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨targetCode, hprefix⟩
    refine ⟨targetCode, ?_⟩
    apply (betaUnshiftPrefixTermAt_nat
      (scons targetCode e)
      (Term.rename Nat.succ sourceCode)
      (Term.rename Nat.succ sourceStep)
      (Term.var 0)
      (Term.rename Nat.succ targetStep)
      (Term.rename Nat.succ bound)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hprefix

theorem betaPrependPrefixTermAt_nat
    (e : Nat → Nat)
    (sourceCode sourceStep head targetCode targetStep bound : Term) :
    Sat natModel e
      (betaPrependPrefixTermAt
        sourceCode sourceStep head targetCode targetStep bound) ↔
      BetaEntry (Term.eval natModel e targetCode)
          (Term.eval natModel e targetStep) 0
          (Term.eval natModel e head) ∧
        ∀ i, i < Term.eval natModel e bound → ∀ out,
          BetaEntry (Term.eval natModel e sourceCode)
              (Term.eval natModel e sourceStep) i out →
            BetaEntry (Term.eval natModel e targetCode)
              (Term.eval natModel e targetStep) (i + 1) out := by
  constructor
  · intro h
    exact ⟨(betaTermTermAt_nat_entry e head targetCode targetStep
        Term.zero).mp h.1,
      (betaUnshiftPrefixTermAt_nat e sourceCode sourceStep
        targetCode targetStep bound).mp h.2⟩
  · intro h
    exact ⟨(betaTermTermAt_nat_entry e head targetCode targetStep
        Term.zero).mpr h.1,
      (betaUnshiftPrefixTermAt_nat e sourceCode sourceStep
        targetCode targetStep bound).mpr h.2⟩

theorem betaPrependPrefixCodeExistsTermAt_nat
    (e : Nat → Nat)
    (sourceCode sourceStep head targetStep bound : Term) :
    Sat natModel e
      (betaPrependPrefixCodeExistsTermAt
        sourceCode sourceStep head targetStep bound) ↔
      ∃ targetCode,
        BetaEntry targetCode (Term.eval natModel e targetStep) 0
            (Term.eval natModel e head) ∧
          ∀ i, i < Term.eval natModel e bound → ∀ out,
            BetaEntry (Term.eval natModel e sourceCode)
                (Term.eval natModel e sourceStep) i out →
              BetaEntry targetCode (Term.eval natModel e targetStep)
                (i + 1) out := by
  constructor
  · intro h
    rcases h with ⟨targetCode, hprefix⟩
    refine ⟨targetCode, ?_⟩
    have hspec := (betaPrependPrefixTermAt_nat
      (scons targetCode e)
      (Term.rename Nat.succ sourceCode)
      (Term.rename Nat.succ sourceStep)
      (Term.rename Nat.succ head)
      (Term.var 0)
      (Term.rename Nat.succ targetStep)
      (Term.rename Nat.succ bound)).mp hprefix
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨targetCode, hprefix⟩
    refine ⟨targetCode, ?_⟩
    apply (betaPrependPrefixTermAt_nat
      (scons targetCode e)
      (Term.rename Nat.succ sourceCode)
      (Term.rename Nat.succ sourceStep)
      (Term.rename Nat.succ head)
      (Term.var 0)
      (Term.rename Nat.succ targetStep)
      (Term.rename Nat.succ bound)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using hprefix

theorem betaPrependExistsTermAt_nat
    (e : Nat → Nat) (sourceCode sourceStep head bound : Term) :
    Sat natModel e
      (betaPrependExistsTermAt sourceCode sourceStep head bound) ↔
      ∃ targetStep targetCode,
        BetaEntry targetCode targetStep 0
            (Term.eval natModel e head) ∧
          ∀ i, i < Term.eval natModel e bound → ∀ out,
            BetaEntry (Term.eval natModel e sourceCode)
                (Term.eval natModel e sourceStep) i out →
              BetaEntry targetCode targetStep (i + 1) out := by
  constructor
  · intro h
    rcases h with ⟨targetStep, hcode⟩
    have hspec := (betaPrependPrefixCodeExistsTermAt_nat
      (scons targetStep e)
      (Term.rename Nat.succ sourceCode)
      (Term.rename Nat.succ sourceStep)
      (Term.rename Nat.succ head)
      (Term.var 0)
      (Term.rename Nat.succ bound)).mp hcode
    refine ⟨targetStep, ?_⟩
    simpa [Term.eval_rename, Term.eval, scons] using hspec
  · intro h
    rcases h with ⟨targetStep, targetCode, hprefix⟩
    refine ⟨targetStep, ?_⟩
    apply (betaPrependPrefixCodeExistsTermAt_nat
      (scons targetStep e)
      (Term.rename Nat.succ sourceCode)
      (Term.rename Nat.succ sourceStep)
      (Term.rename Nat.succ head)
      (Term.var 0)
      (Term.rename Nat.succ bound)).mpr
    refine ⟨targetCode, ?_⟩
    simpa [Term.eval_rename, Term.eval, scons] using hprefix

theorem betaEntryExistsPrefixTermAt_nat
    (e : Nat → Nat) (code step bound : Term) :
    Sat natModel e (betaEntryExistsPrefixTermAt code step bound) ↔
      ∀ i, i < Term.eval natModel e bound →
        ∃ out, BetaEntry (Term.eval natModel e code)
          (Term.eval natModel e step) i out := by
  constructor
  · intro h i hi
    have hltSat : Sat natModel (scons i e)
        (ltTermAt (Term.var 0) (Term.rename Nat.succ bound)) :=
      (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mpr (by
          simpa [Term.eval_rename, Term.eval, scons] using hi)
    have hex := h i hltSat
    have hout := (betaEntryExistsTermAt_nat
      (scons i e)
      (Term.rename Nat.succ code)
      (Term.rename Nat.succ step)
      (Term.var 0)).mp (by simpa [betaEntryExistsPrefixTermAt] using hex)
    simpa [Term.eval_rename, Term.eval, scons] using hout
  · intro h i hltSat
    have hi : i < Term.eval natModel e bound := by
      have hlt := (ltTermAt_nat (scons i e)
        (Term.var 0) (Term.rename Nat.succ bound)).mp hltSat
      simpa [Term.eval_rename, Term.eval, scons] using hlt
    apply (betaEntryExistsTermAt_nat
      (scons i e)
      (Term.rename Nat.succ code)
      (Term.rename Nat.succ step)
      (Term.var 0)).mpr
    simpa [Term.eval_rename, Term.eval, scons] using h i hi

theorem betaShiftTailThroughTermAt_nat
    (e : Nat → Nat) (oldCode oldStep : Nat)
    (newCode newStep last : Term) :
    Sat natModel e
      (betaShiftTailThroughTermAt oldCode oldStep newCode newStep last) ↔
      BetaShiftTailThrough
        (e oldCode) (e oldStep)
        (Term.eval natModel e newCode)
        (Term.eval natModel e newStep)
        (Term.eval natModel e last) := by
  constructor
  · intro h k hk value hold
    have hkSat :
        Sat natModel (scons k e)
          (leTermAt (Term.var 0) (Term.rename Nat.succ last)) := by
      exact (leTermAt_nat (scons k e)
          (Term.var 0) (Term.rename Nat.succ last)).mpr (by
        calc
          Term.eval natModel (scons k e) (Term.var 0) = k := by
            simp [Term.eval, scons]
          _ ≤ Term.eval natModel e last := hk
          _ = Term.eval natModel (scons k e)
                (Term.rename Nat.succ last) := by
            simp [Term.eval_rename, scons])
    have holdSat :
        Sat natModel (scons value (scons k e))
          (betaTermTermAt (Term.var 0)
            (Term.var (oldCode+2)) (Term.var (oldStep+2))
            (Term.succ (Term.var 1))) := by
      apply (betaTermTermAt_nat_entry (scons value (scons k e))
        (Term.var 0) (Term.var (oldCode+2)) (Term.var (oldStep+2))
        (Term.succ (Term.var 1))).mpr
      simpa [Term.eval, natModel, scons, Nat.add_assoc] using hold
    have hnewSat := h k hkSat value holdSat
    have hnew := (betaTermTermAt_nat_entry (scons value (scons k e))
        (Term.var 0)
        (Term.rename (fun n => n+2) newCode)
        (Term.rename (fun n => n+2) newStep)
        (Term.var 1)).mp hnewSat
    simpa [Term.eval_rename, Term.eval, scons, Nat.add_assoc] using hnew
  · intro h k hkSat value holdSat
    have hk : k ≤ Term.eval natModel e last := by
      have hle := (leTermAt_nat (scons k e)
          (Term.var 0) (Term.rename Nat.succ last)).mp hkSat
      calc
        k = Term.eval natModel (scons k e) (Term.var 0) := by
          simp [Term.eval, scons]
        _ ≤ Term.eval natModel (scons k e)
            (Term.rename Nat.succ last) := hle
        _ = Term.eval natModel e last := by
          simp [Term.eval_rename, scons]
    have hold :
        BetaEntry (e oldCode) (e oldStep) (k + 1) value := by
      have hb := (betaTermTermAt_nat_entry (scons value (scons k e))
          (Term.var 0) (Term.var (oldCode+2)) (Term.var (oldStep+2))
          (Term.succ (Term.var 1))).mp holdSat
      simpa [Term.eval, natModel, scons, Nat.add_assoc] using hb
    apply (betaTermTermAt_nat_entry (scons value (scons k e))
      (Term.var 0)
      (Term.rename (fun n => n+2) newCode)
      (Term.rename (fun n => n+2) newStep)
      (Term.var 1)).mpr
    simpa [Term.eval_rename, Term.eval, scons, Nat.add_assoc] using
      h k hk value hold

/-- Standard-model meaning of the existential shifted-tail formula. -/
theorem betaShiftTailExistsTermAt_nat
    (e : Nat → Nat) (oldCode oldStep : Nat) (last : Term) :
    Sat natModel e (betaShiftTailExistsTermAt oldCode oldStep last) ↔
      ∃ newCode newStep,
        BetaShiftTailThrough
          (e oldCode) (e oldStep) newCode newStep
          (Term.eval natModel e last) := by
  constructor
  · intro h
    rcases h with ⟨newCode, newStep, htailSat⟩
    have htail :=
      (betaShiftTailThroughTermAt_nat
        (scons newStep (scons newCode e))
        (oldCode+2) (oldStep+2)
        (Term.var 1) (Term.var 0)
        (Term.rename (fun n => n+2) last)).mp htailSat
    refine ⟨newCode, newStep, ?_⟩
    simpa [Term.eval_rename, Term.eval, scons, Nat.add_assoc] using htail
  · intro h
    rcases h with ⟨newCode, newStep, htail⟩
    refine ⟨newCode, newStep, ?_⟩
    apply (betaShiftTailThroughTermAt_nat
      (scons newStep (scons newCode e))
      (oldCode+2) (oldStep+2)
      (Term.var 1) (Term.var 0)
      (Term.rename (fun n => n+2) last)).mpr
    simpa [Term.eval_rename, Term.eval, scons, Nat.add_assoc] using htail

theorem betaShiftTailThroughConstAt_nat
    (e : Nat → Nat) (oldCode oldStep newCode newStep last : Nat) :
    Sat natModel e
      (betaShiftTailThroughConstAt oldCode oldStep newCode newStep last) ↔
      BetaShiftTailThrough
        (e oldCode) (e oldStep) (e newCode) (e newStep) last := by
  constructor
  · intro h k hk value hold
    have hkSat :
        Sat natModel (scons k e) (leConstAt 0 last) := by
      exact (leConstAt_nat (scons k e) 0 last).mpr (by
        simpa [scons] using hk)
    have holdSat :
        Sat natModel (scons value (scons k e))
          (betaTermTermAt (Term.var 0)
            (Term.var (oldCode+2)) (Term.var (oldStep+2))
            (Term.succ (Term.var 1))) := by
      apply (betaTermTermAt_nat_entry (scons value (scons k e))
        (Term.var 0) (Term.var (oldCode+2)) (Term.var (oldStep+2))
        (Term.succ (Term.var 1))).mpr
      simpa [Term.eval, natModel, scons, Nat.add_assoc] using hold
    have hnewSat := h k hkSat value holdSat
    have hnew := (betaTermTermAt_nat_entry (scons value (scons k e))
        (Term.var 0) (Term.var (newCode+2)) (Term.var (newStep+2))
        (Term.var 1)).mp hnewSat
    simpa [Term.eval, scons, Nat.add_assoc] using hnew
  · intro h k hkSat value holdSat
    have hk : k ≤ last := by
      have hle := (leConstAt_nat (scons k e) 0 last).mp hkSat
      simpa [scons] using hle
    have hold :
        BetaEntry (e oldCode) (e oldStep) (k + 1) value := by
      have hb := (betaTermTermAt_nat_entry (scons value (scons k e))
          (Term.var 0) (Term.var (oldCode+2)) (Term.var (oldStep+2))
          (Term.succ (Term.var 1))).mp holdSat
      simpa [Term.eval, natModel, scons, Nat.add_assoc] using hb
    apply (betaTermTermAt_nat_entry (scons value (scons k e))
      (Term.var 0) (Term.var (newCode+2)) (Term.var (newStep+2))
      (Term.var 1)).mpr
    simpa [Term.eval, scons, Nat.add_assoc] using h k hk value hold

theorem betaDiv2StepsThroughTermTermAt_nat
    (e : Nat → Nat) (code step last : Term) :
    Sat natModel e (betaDiv2StepsThroughTermTermAt code step last) ↔
      BetaDiv2StepsThrough
        (Term.eval natModel e code)
        (Term.eval natModel e step)
        (Term.eval natModel e last) := by
  constructor
  · intro h k hk
    have hkSat :
        Sat natModel (scons k e)
          (leTermAt (Term.var 0) (Term.rename Nat.succ last)) := by
      exact (leTermAt_nat (scons k e)
          (Term.var 0) (Term.rename Nat.succ last)).mpr (by
        calc
          Term.eval natModel (scons k e) (Term.var 0) = k := by
            simp [Term.eval, scons]
          _ ≤ Term.eval natModel e last := hk
          _ = Term.eval natModel (scons k e)
                (Term.rename Nat.succ last) := by
            simp [Term.eval_rename, scons])
    have hw := (betaDiv2StepWitnessTermAt_nat (scons k e)
      (Term.rename Nat.succ code)
      (Term.rename Nat.succ step) (Term.var 0)).mp (h k hkSat)
    rcases hw with ⟨cur, next, bit, hdiv⟩
    refine ⟨cur, next, bit, ?_⟩
    simpa [BetaDiv2Step, Term.eval_rename, Term.eval, scons] using hdiv
  · intro h k hkSat
    have hk : k ≤ Term.eval natModel e last := by
      have hle := (leTermAt_nat (scons k e)
          (Term.var 0) (Term.rename Nat.succ last)).mp hkSat
      calc
        k = Term.eval natModel (scons k e) (Term.var 0) := by
          simp [Term.eval, scons]
        _ ≤ Term.eval natModel (scons k e)
            (Term.rename Nat.succ last) := hle
        _ = Term.eval natModel e last := by
          simp [Term.eval_rename, scons]
    rcases h k hk with ⟨cur, next, bit, hdiv⟩
    apply (betaDiv2StepWitnessTermAt_nat (scons k e)
      (Term.rename Nat.succ code)
      (Term.rename Nat.succ step) (Term.var 0)).mpr
    refine ⟨cur, next, bit, ?_⟩
    simpa [BetaDiv2Step, Term.eval_rename, Term.eval, scons] using hdiv

theorem betaDiv2StepsThroughConstAt_nat
    (e : Nat → Nat) (code step last : Nat) :
    Sat natModel e (betaDiv2StepsThroughConstAt code step last) ↔
      BetaDiv2StepsThrough (e code) (e step) last := by
  constructor
  · intro h k hk
    have hkSat :
        Sat natModel (scons k e) (leConstAt 0 last) := by
      exact (leConstAt_nat (scons k e) 0 last).mpr (by
        simpa [scons] using hk)
    have hw := (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mp
      (h k hkSat)
    rcases hw with ⟨cur, next, bit, hcur, hnext, hbit, hvalue⟩
    exact ⟨cur, next, bit, by
      simpa [BetaDiv2Step, scons] using
        And.intro hcur (And.intro hnext (And.intro hbit hvalue))⟩
  · intro h k hkSat
    have hk : k ≤ last := by
      have hle := (leConstAt_nat (scons k e) 0 last).mp hkSat
      simpa [scons] using hle
    rcases h k hk with ⟨cur, next, bit, hdiv⟩
    rcases hdiv with ⟨hcur, hnext, hbit, hvalue⟩
    apply (betaDiv2StepWitnessAt_nat (scons k e) (code+1) (step+1) 0).mpr
    exact ⟨cur, next, bit, by simpa [scons] using hcur,
      by simpa [scons] using hnext, by
        simpa using And.intro hbit hvalue⟩

theorem betaDiv2BitAt_nat (e : Nat → Nat) (bit code step idx : Nat) :
    Sat natModel e (betaDiv2BitAt bit code step idx) ↔
      BetaDiv2Bit (e code) (e step) (e idx) (e bit) := by
  constructor
  · intro h
    rcases h with ⟨cur, next, hcur, hnext, hstep⟩
    let E := scons next (scons cur e)
    have hcur' :
        BetaEntry (e code) (e step) (e idx) cur := by
      have hc := (betaAt_nat_entry E 1 (code+2) (step+2) (idx+2)).mp hcur
      simpa [E, scons] using hc
    have hnext' :
        BetaEntry (e code) (e step) (e idx + 1) next := by
      have hn := (betaAtSuccIdx_nat_entry E 0 (code+2) (step+2) (idx+2)).mp hnext
      simpa [E, scons, Nat.add_assoc] using hn
    have hstep' :
        (e bit = 0 ∨ e bit = 1) ∧ cur = next + next + e bit := by
      have hs := (div2StepAt_nat E 1 0 (bit+2)).mp hstep
      simpa [E, scons] using hs
    exact ⟨cur, next, hcur', hnext', hstep'⟩
  · intro h
    rcases h with ⟨cur, next, hcur, hnext, hstep⟩
    refine ⟨cur, next, ?_, ?_, ?_⟩
    · let E := scons next (scons cur e)
      apply (betaAt_nat_entry E 1 (code+2) (step+2) (idx+2)).mpr
      simpa [E, scons] using hcur
    · let E := scons next (scons cur e)
      apply (betaAtSuccIdx_nat_entry E 0 (code+2) (step+2) (idx+2)).mpr
      simpa [E, scons, Nat.add_assoc] using hnext
    · let E := scons next (scons cur e)
      apply (div2StepAt_nat E 1 0 (bit+2)).mpr
      simpa [E, scons] using hstep

theorem betaDiv2BitTermAt_nat
    (e : Nat → Nat) (bit code step idx : Term) :
    Sat natModel e (betaDiv2BitTermAt bit code step idx) ↔
      BetaDiv2Bit
        (Term.eval natModel e code)
        (Term.eval natModel e step)
        (Term.eval natModel e idx)
        (Term.eval natModel e bit) := by
  constructor
  · intro h
    rcases h with ⟨cur, next, hcur, hnext, hstep⟩
    let E := scons next (scons cur e)
    have hcur' :
        BetaEntry (Term.eval natModel e code)
          (Term.eval natModel e step) (Term.eval natModel e idx) cur := by
      have hc := (betaTermTermAt_nat_entry E (Term.var 1)
        (Term.rename (fun n => n+2) code)
        (Term.rename (fun n => n+2) step)
        (Term.rename (fun n => n+2) idx)).mp hcur
      simpa [E, Term.eval_rename, Term.eval, scons, Nat.add_assoc] using hc
    have hnext' :
        BetaEntry (Term.eval natModel e code)
          (Term.eval natModel e step) (Term.eval natModel e idx + 1)
          next := by
      have hn := (betaTermTermAt_nat_entry E (Term.var 0)
        (Term.rename (fun n => n+2) code)
        (Term.rename (fun n => n+2) step)
        (Term.succ (Term.rename (fun n => n+2) idx))).mp hnext
      simpa [E, Term.eval_rename, Term.eval, natModel, scons,
        Nat.add_assoc] using hn
    have hstep' :
        (Term.eval natModel e bit = 0 ∨ Term.eval natModel e bit = 1) ∧
          cur = next + next + Term.eval natModel e bit := by
      have hs := (div2StepTermAt_nat E
        (Term.var 1) (Term.var 0)
        (Term.rename (fun n => n+2) bit)).mp hstep
      simpa [E, Term.eval_rename, Term.eval, scons, Nat.add_assoc] using hs
    exact ⟨cur, next, hcur', hnext', hstep'.1, hstep'.2⟩
  · intro h
    rcases h with ⟨cur, next, hcur, hnext, hbit, hvalue⟩
    refine ⟨cur, next, ?_, ?_, ?_⟩
    · let E := scons next (scons cur e)
      apply (betaTermTermAt_nat_entry E (Term.var 1)
        (Term.rename (fun n => n+2) code)
        (Term.rename (fun n => n+2) step)
        (Term.rename (fun n => n+2) idx)).mpr
      simpa [E, Term.eval_rename, Term.eval, scons, Nat.add_assoc] using hcur
    · let E := scons next (scons cur e)
      apply (betaTermTermAt_nat_entry E (Term.var 0)
        (Term.rename (fun n => n+2) code)
        (Term.rename (fun n => n+2) step)
        (Term.succ (Term.rename (fun n => n+2) idx))).mpr
      simpa [E, Term.eval_rename, Term.eval, natModel, scons,
        Nat.add_assoc] using hnext
    · let E := scons next (scons cur e)
      apply (div2StepTermAt_nat E
        (Term.var 1) (Term.var 0)
        (Term.rename (fun n => n+2) bit)).mpr
      simpa [E, Term.eval_rename, Term.eval, scons, Nat.add_assoc] using
        And.intro hbit hvalue

theorem betaDiv2BitOneTermExAt_nat
    (e : Nat → Nat) (code step idx : Term) :
    Sat natModel e (betaDiv2BitOneTermExAt code step idx) ↔
      BetaDiv2Bit
        (Term.eval natModel e code)
        (Term.eval natModel e step)
        (Term.eval natModel e idx) 1 := by
  constructor
  · intro h
    rcases h with ⟨bit, hone, hbit⟩
    have hbitOne : bit = 1 := (oneAt_nat (scons bit e) 0).mp hone
    have hb := (betaDiv2BitTermAt_nat (scons bit e)
      (Term.var 0) (Term.rename Nat.succ code)
      (Term.rename Nat.succ step) (Term.rename Nat.succ idx)).mp hbit
    subst hbitOne
    simpa [Term.eval_rename, Term.eval, scons] using hb
  · intro h
    refine ⟨1, ?_, ?_⟩
    · exact (oneAt_nat (scons 1 e) 0).mpr rfl
    · apply (betaDiv2BitTermAt_nat (scons 1 e)
        (Term.var 0) (Term.rename Nat.succ code)
        (Term.rename Nat.succ step) (Term.rename Nat.succ idx)).mpr
      simpa [Term.eval_rename, Term.eval, scons] using h

theorem hfMemAt_nat_trace (e : Nat → Nat) (elem set : Nat) :
    Sat natModel e (hfMemAt elem set) ↔
      ∃ code step, HFMemTrace (e elem) (e set) code step := by
  constructor
  · intro h
    rcases h with ⟨code, step, hstart, hsteps, hbitOne⟩
    let E := scons step (scons code e)
    have hstart' :
        BetaEntry code step 0 (e set) := by
      have hs := (betaAtConstIdx_nat_entry E (set+2) 1 0 0).mp hstart
      simpa [E, scons] using hs
    have hsteps' :
        BetaDiv2StepsThrough code step (e elem) := by
      have hs := (betaDiv2StepsThroughAt_nat E 1 0 (elem+2)).mp hsteps
      intro k hk
      have hkE : k ≤ E (elem+2) := by
        simpa [E, scons] using hk
      have hraw := hs k hkE
      simpa [BetaDiv2Step, E, scons] using hraw
    have hbit' :
        BetaDiv2Bit code step (e elem) 1 := by
      rcases hbitOne with ⟨bit, hone, hbit⟩
      have hone' : bit = 1 := (oneAt_nat (scons bit E) 0).mp hone
      have hb := (betaDiv2BitAt_nat (scons bit E) 0 2 1 (elem+3)).mp hbit
      subst bit
      simpa [E, scons] using hb
    exact ⟨code, step, hstart', hsteps', hbit'⟩
  · intro h
    rcases h with ⟨code, step, hstart, hsteps, hbit⟩
    let E := scons step (scons code e)
    refine ⟨code, step, ?_, ?_, ?_⟩
    · apply (betaAtConstIdx_nat_entry E (set+2) 1 0 0).mpr
      simpa [E, scons] using hstart
    · apply (betaDiv2StepsThroughAt_nat E 1 0 (elem+2)).mpr
      intro k hk
      have hk' : k ≤ e elem := by
        simpa [E, scons] using hk
      have hraw := hsteps k hk'
      simpa [BetaDiv2Step, E, scons] using hraw
    · refine ⟨1, ?_, ?_⟩
      · exact (oneAt_nat (scons 1 E) 0).mpr rfl
      · apply (betaDiv2BitAt_nat (scons 1 E) 0 2 1 (elem+3)).mpr
        simpa [E, scons] using hbit

theorem betaFact_pos : ∀ n, 0 < betaFact n
  | 0 => by simp [betaFact]
  | n+1 => by
      simp [betaFact, betaFact_pos n]

theorem dvd_betaFact_of_pos_le {k n : Nat} (hk : 0 < k) (hkn : k ≤ n) :
    k ∣ betaFact n := by
  induction n with
  | zero =>
      have hk0 : k = 0 := by omega
      omega
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le hkn with hlt | heq
      · have hle : k ≤ n := Nat.lt_succ_iff.mp hlt
        exact Nat.dvd_trans (ih hle) (by
          change betaFact n ∣ (n+1) * betaFact n
          exact Nat.dvd_mul_left (betaFact n) (n+1))
      · subst k
        change n+1 ∣ (n+1) * betaFact n
        exact Nat.dvd_mul_right (n+1) (betaFact n)

theorem BetaModulus_pos (step idx : Nat) : 0 < BetaModulus step idx := by
  simp [BetaModulus]
  omega

theorem BetaModuliProduct_pos (step : Nat) :
    ∀ n, 0 < BetaModuliProduct step n
  | 0 => by simp [BetaModuliProduct]
  | n+1 => by
      have hp := BetaModuliProduct_pos step n
      have hm := BetaModulus_pos step n
      simp [BetaModuliProduct]
      exact Nat.mul_pos hp hm

theorem BetaModulus_coprime_step (step idx : Nat) :
    (BetaModulus step idx).Coprime step := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  let d := Nat.gcd (BetaModulus step idx) step
  have hdm : d ∣ BetaModulus step idx := Nat.gcd_dvd_left _ _
  have hdstep : d ∣ step := Nat.gcd_dvd_right _ _
  have hdprod : d ∣ (idx + 1) * step :=
    Nat.dvd_trans hdstep (Nat.dvd_mul_left step (idx+1))
  have hdone : d ∣ 1 := by
    have hsub := Nat.dvd_sub hdm hdprod
    have hdiff : BetaModulus step idx - (idx + 1) * step = 1 := by
      simp [BetaModulus]
    rw [hdiff] at hsub
    exact hsub
  exact Nat.dvd_one.mp hdone

theorem BetaModulus_sub {step i j : Nat} (hij : i ≤ j) :
    BetaModulus step j - BetaModulus step i = (j - i) * step := by
  have hj : j + 1 = (j - i) + (i + 1) := by omega
  simp [BetaModulus, hj, Nat.add_mul]
  omega

theorem BetaModulus_pair_coprime_of_dvd_step {step i j : Nat}
    (hij : i < j) (hdiff : j - i ∣ step) :
    (BetaModulus step i).Coprime (BetaModulus step j) := by
  apply (Nat.coprime_iff_gcd_eq_one).mpr
  let d := Nat.gcd (BetaModulus step i) (BetaModulus step j)
  have hdi : d ∣ BetaModulus step i := Nat.gcd_dvd_left _ _
  have hdj : d ∣ BetaModulus step j := Nat.gcd_dvd_right _ _
  have hcopStep : d.Coprime step :=
    Nat.Coprime.coprime_dvd_left hdi (BetaModulus_coprime_step step i)
  have hddiffstep : d ∣ (j - i) * step := by
    have hsub := Nat.dvd_sub hdj hdi
    simpa [d, BetaModulus_sub (Nat.le_of_lt hij)] using hsub
  have hddiff : d ∣ j - i := by
    apply hcopStep.dvd_of_dvd_mul_left
    simpa [Nat.mul_comm] using hddiffstep
  have hdstep' : d ∣ step := Nat.dvd_trans hddiff hdiff
  exact hcopStep.eq_one_of_dvd hdstep'

theorem BetaModulus_pair_coprime_of_lt_le {i j N : Nat}
    (hij : i < j) (hj : j ≤ N) :
    (BetaModulus (betaFact N) i).Coprime (BetaModulus (betaFact N) j) := by
  apply BetaModulus_pair_coprime_of_dvd_step hij
  apply dvd_betaFact_of_pos_le
  · omega
  · omega

theorem BetaModuliProduct_coprime_modulus_of_le {n j N : Nat}
    (hnj : n ≤ j) (hjN : j ≤ N) :
    (BetaModuliProduct (betaFact N) n).Coprime
      (BetaModulus (betaFact N) j) := by
  induction n with
  | zero =>
      simp [BetaModuliProduct]
  | succ n ih =>
      simp [BetaModuliProduct]
      apply Nat.Coprime.mul_left
      · exact ih (by omega)
      · exact BetaModulus_pair_coprime_of_lt_le (by omega) hjN

theorem BetaModuliProduct_coprime_next_of_le {n N : Nat} (hn : n ≤ N) :
    (BetaModuliProduct (betaFact N) n).Coprime
      (BetaModulus (betaFact N) n) :=
  BetaModuliProduct_coprime_modulus_of_le (Nat.le_refl n) hn

theorem int_bezout_gcd (m n : Nat) :
    ∃ s t : Int, s * (m : Int) + t * (n : Int) = (Nat.gcd m n : Int) := by
  induction m, n using Nat.gcd.induction with
  | H0 n =>
      refine ⟨0, 1, ?_⟩
      simp
  | H1 m n hm ih =>
      rcases ih with ⟨s, t, hst⟩
      refine ⟨t - s * ((n / m : Nat) : Int), s, ?_⟩
      rw [Nat.gcd_rec]
      rw [← hst]
      let M : Int := (m : Int)
      let q : Int := ((n / m : Nat) : Int)
      let r : Int := ((n % m : Nat) : Int)
      have hdiv : M * q + r = (n : Int) := by
        have h : ((m * (n / m) + n % m : Nat) : Int) = (n : Int) := by
          have h0 := Nat.div_add_mod n m
          rw [h0]
        simpa [M, q, r, Int.natCast_add, Int.natCast_mul] using h
      change (t - s * q) * M + s * (n : Int) = s * r + t * M
      rw [← hdiv]
      simp [Int.mul_add, Int.mul_sub, Int.mul_comm, Int.mul_left_comm, Int.add_comm]
      omega

theorem coprime_int_bezout {m n : Nat} (h : m.Coprime n) :
    ∃ s t : Int, s * (m : Int) + t * (n : Int) = 1 := by
  rcases int_bezout_gcd m n with ⟨s, t, hst⟩
  refine ⟨s, t, ?_⟩
  have hg : Nat.gcd m n = 1 := h.gcd_eq_one
  simpa [hg] using hst

theorem int_nonneg_shift (z : Int) {M : Nat} (hM : 0 < M) :
    0 ≤ z + ((M : Nat) : Int) * (((z.natAbs + 1 : Nat) : Int)) := by
  have hzlow : -((z.natAbs : Nat) : Int) ≤ z := by
    rcases Int.natAbs_eq z with hz | hz <;> omega
  have hprodNat : z.natAbs ≤ M * (z.natAbs + 1) := by
    have h1 : z.natAbs ≤ z.natAbs + 1 := by omega
    have h2 : z.natAbs + 1 ≤ M * (z.natAbs + 1) := by
      have hm1 : 1 ≤ M := by omega
      have hm := Nat.mul_le_mul_right (z.natAbs + 1) hm1
      simpa [Nat.one_mul] using hm
    exact Nat.le_trans h1 h2
  have hprod :
      ((z.natAbs : Nat) : Int) ≤
        (M : Int) * (((z.natAbs + 1 : Nat) : Int)) := by
    exact Int.ofNat_le.mpr hprodNat
  omega

theorem int_crt_shape_left {s t m n a b : Int}
    (hbez : s * m + t * n = 1) :
    a * (t * n) + b * (s * m) = a + m * (b * s - a * s) := by
  have htn : t * n = 1 - s * m := by omega
  rw [htn]
  simp [Int.mul_sub, Int.mul_comm, Int.mul_left_comm]
  omega

theorem int_crt_shape_right {s t m n a b : Int}
    (hbez : s * m + t * n = 1) :
    a * (t * n) + b * (s * m) = b + n * (a * t - b * t) := by
  have hsm : s * m = 1 - t * n := by omega
  rw [hsm]
  simp [Int.mul_sub, Int.mul_comm, Int.mul_left_comm]
  omega

theorem crt_two_mod {m n a b : Nat} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (ha : a < m) (hb : b < n) :
    ∃ c, c % m = a ∧ c % n = b := by
  rcases coprime_int_bezout hcop with ⟨s, t, hbez⟩
  let z : Int := (a : Int) * (t * (n : Int)) + (b : Int) * (s * (m : Int))
  let K : Int := (((z.natAbs + 1 : Nat) : Int))
  let big : Nat := m * n
  let cInt : Int := z + (big : Int) * K
  let c : Nat := cInt.toNat
  have hbig : 0 < big := Nat.mul_pos hm hn
  have hcNonneg : 0 ≤ cInt := by
    simpa [cInt, K, big] using int_nonneg_shift z hbig
  have hcCast : (c : Int) = cInt := by
    exact Int.toNat_of_nonneg hcNonneg
  refine ⟨c, ?_, ?_⟩
  · have hzmod : z % (m : Int) = (a : Int) := by
      have hshape :
          z = (a : Int) + (m : Int) * ((b : Int) * s - (a : Int) * s) := by
        exact int_crt_shape_left hbez
      rw [hshape]
      rw [Int.add_mul_emod_self_left]
      apply Int.emod_eq_of_lt <;> omega
    have hcmodInt : (c : Int) % (m : Int) = (a : Int) := by
      rw [hcCast]
      have hbigshape : (big : Int) * K = (m : Int) * ((n : Int) * K) := by
        simp [big, Int.natCast_mul, Int.mul_assoc]
      simp only [cInt]
      rw [hbigshape]
      rw [Int.add_mul_emod_self_left]
      exact hzmod
    have hcastmod : ((c % m : Nat) : Int) = (a : Int) := by
      rw [Int.natCast_emod]
      exact hcmodInt
    omega
  · have hzmod : z % (n : Int) = (b : Int) := by
      have hshape :
          z = (b : Int) + (n : Int) * ((a : Int) * t - (b : Int) * t) := by
        exact int_crt_shape_right hbez
      rw [hshape]
      rw [Int.add_mul_emod_self_left]
      apply Int.emod_eq_of_lt <;> omega
    have hcmodInt : (c : Int) % (n : Int) = (b : Int) := by
      rw [hcCast]
      have hbigshape : (big : Int) * K = (n : Int) * ((m : Int) * K) := by
        simp [big, Int.natCast_mul, Int.mul_assoc, Int.mul_left_comm]
      simp only [cInt]
      rw [hbigshape]
      rw [Int.add_mul_emod_self_left]
      exact hzmod
    have hcastmod : ((c % n : Nat) : Int) = (b : Int) := by
      rw [Int.natCast_emod]
      exact hcmodInt
    omega

theorem BetaEntry_value_lt {code step idx value : Nat}
    (h : BetaEntry code step idx value) :
    value < BetaModulus step idx := by
  rcases h with ⟨_, _, hlt⟩
  exact hlt

theorem BetaEntry_mod_eq {code step idx value : Nat}
    (h : BetaEntry code step idx value) :
    code % BetaModulus step idx = value := by
  rcases h with ⟨q, hcode, hlt⟩
  rw [hcode]
  rw [Nat.mul_comm q (BetaModulus step idx)]
  rw [Nat.mul_add_mod_self_left]
  exact Nat.mod_eq_of_lt hlt

theorem BetaEntry_of_mod_eq {code step idx value : Nat}
    (hlt : value < BetaModulus step idx)
    (hmod : code % BetaModulus step idx = value) :
    BetaEntry code step idx value := by
  refine ⟨code / BetaModulus step idx, ?_, hlt⟩
  have hdiv : code = (code / BetaModulus step idx) * BetaModulus step idx +
      code % BetaModulus step idx := by
    simpa [Nat.mul_comm] using (Nat.div_add_mod code (BetaModulus step idx)).symm
  simpa [hmod] using hdiv

theorem BetaModuliProduct_dvd_of_lt {step i n : Nat} (hi : i < n) :
    BetaModulus step i ∣ BetaModuliProduct step n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
      · have hd : BetaModulus step i ∣ BetaModuliProduct step n := ih hlt
        rcases hd with ⟨q, hq⟩
        refine ⟨q * BetaModulus step n, ?_⟩
        simp [BetaModuliProduct, hq, Nat.mul_assoc]
      · subst i
        change BetaModulus step n ∣ BetaModuliProduct step n * BetaModulus step n
        exact Nat.dvd_mul_left (BetaModulus step n) (BetaModuliProduct step n)

theorem mod_eq_of_mod_BetaModuliProduct_eq {code old step idx n : Nat}
    (hi : idx < n)
    (hmod : code % BetaModuliProduct step n = old % BetaModuliProduct step n) :
    code % BetaModulus step idx = old % BetaModulus step idx := by
  have hd : BetaModulus step idx ∣ BetaModuliProduct step n :=
    BetaModuliProduct_dvd_of_lt hi
  calc
    code % BetaModulus step idx = code % BetaModuliProduct step n % BetaModulus step idx := by
      exact (Nat.mod_mod_of_dvd code hd).symm
    _ = old % BetaModuliProduct step n % BetaModulus step idx := by rw [hmod]
    _ = old % BetaModulus step idx := Nat.mod_mod_of_dvd old hd

theorem BetaEntry_of_mod_BetaModuliProduct_eq {code old step idx n value : Nat}
    (hi : idx < n)
    (hmod : code % BetaModuliProduct step n = old % BetaModuliProduct step n)
    (hold : BetaEntry old step idx value) :
    BetaEntry code step idx value := by
  apply BetaEntry_of_mod_eq (BetaEntry_value_lt hold)
  calc
    code % BetaModulus step idx = old % BetaModulus step idx :=
      mod_eq_of_mod_BetaModuliProduct_eq hi hmod
    _ = value := BetaEntry_mod_eq hold

theorem BetaModulus_pair_coprime_of_lt_le_mul_betaFact {i j N scale : Nat}
    (hij : i < j) (hj : j ≤ N) :
    (BetaModulus (betaFact N * scale) i).Coprime
      (BetaModulus (betaFact N * scale) j) := by
  apply BetaModulus_pair_coprime_of_dvd_step hij
  have hd : j - i ∣ betaFact N := by
    apply dvd_betaFact_of_pos_le
    · omega
    · omega
  exact Nat.dvd_trans hd (Nat.dvd_mul_right (betaFact N) scale)

theorem BetaModuliProduct_coprime_modulus_of_le_mul_betaFact {n j N scale : Nat}
    (hnj : n ≤ j) (hjN : j ≤ N) :
    (BetaModuliProduct (betaFact N * scale) n).Coprime
      (BetaModulus (betaFact N * scale) j) := by
  induction n with
  | zero =>
      simp [BetaModuliProduct]
  | succ n ih =>
      simp [BetaModuliProduct]
      apply Nat.Coprime.mul_left
      · exact ih (by omega)
      · exact BetaModulus_pair_coprime_of_lt_le_mul_betaFact (by omega) hjN

theorem BetaModuliProduct_coprime_next_of_le_mul_betaFact {n N scale : Nat}
    (hn : n ≤ N) :
    (BetaModuliProduct (betaFact N * scale) n).Coprime
      (BetaModulus (betaFact N * scale) n) :=
  BetaModuliProduct_coprime_modulus_of_le_mul_betaFact (Nat.le_refl n) hn

theorem beta_entries_exist_lt_mul_betaFact {N n scale : Nat} (hn : n ≤ N + 1)
    (value : Nat → Nat)
    (hsmall : ∀ i, i < n → value i < BetaModulus (betaFact N * scale) i) :
    ∃ code, ∀ i, i < n → BetaEntry code (betaFact N * scale) i (value i) := by
  induction n with
  | zero =>
      refine ⟨0, ?_⟩
      intro i hi
      omega
  | succ n ih =>
      have hnOld : n ≤ N + 1 := by omega
      rcases ih hnOld (by
        intro i hi
        exact hsmall i (by omega)) with ⟨old, hold⟩
      let step := betaFact N * scale
      let prod := BetaModuliProduct step n
      let modn := BetaModulus step n
      have hprodPos : 0 < prod := by
        simpa [prod, step] using BetaModuliProduct_pos step n
      have hmodnPos : 0 < modn := by
        simpa [modn, step] using BetaModulus_pos step n
      have hnN : n ≤ N := by omega
      have hcop : prod.Coprime modn := by
        simpa [prod, modn, step] using
          BetaModuliProduct_coprime_next_of_le_mul_betaFact
            (n := n) (N := N) (scale := scale) hnN
      have ha : old % prod < prod := Nat.mod_lt old hprodPos
      have hb : value n < modn := by
        simpa [modn, step] using hsmall n (Nat.lt_succ_self n)
      rcases crt_two_mod hprodPos hmodnPos hcop ha hb with ⟨code, hprod, hnew⟩
      refine ⟨code, ?_⟩
      intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
      · apply BetaEntry_of_mod_BetaModuliProduct_eq hlt
        · simpa [prod, step] using hprod
        · exact hold i hlt
      · subst i
        apply BetaEntry_of_mod_eq
        · exact hsmall n (Nat.lt_succ_self n)
        · simpa [modn, step] using hnew

theorem beta_entries_exist_through_mul_betaFact {N scale : Nat} (value : Nat → Nat)
    (hsmall : ∀ i, i ≤ N → value i < BetaModulus (betaFact N * scale) i) :
    ∃ code, ∀ i, i ≤ N → BetaEntry code (betaFact N * scale) i (value i) := by
  rcases beta_entries_exist_lt_mul_betaFact (N := N) (n := N + 1) (scale := scale)
      (Nat.le_refl (N + 1)) value (by
    intro i hi
    exact hsmall i (by omega)) with ⟨code, hcode⟩
  refine ⟨code, ?_⟩
  intro i hi
  exact hcode i (by omega)

/-- A finite shifted beta tail exists semantically.

The fresh step is chosen large enough to dominate every old successor-index
value through `last`; the existing finite CRT construction then packs those
values into one beta code. -/
theorem BetaShiftTailThrough_exists_with_betaFact_step
    (oldCode oldStep last : Nat) :
    ∃ newCode,
      BetaShiftTailThrough oldCode oldStep newCode
        (betaFact last * BetaModulus oldStep (last + 1)) last := by
  let scale : Nat := BetaModulus oldStep (last + 1)
  let newStep : Nat := betaFact last * scale
  let value : Nat → Nat :=
    fun k => oldCode % BetaModulus oldStep (k + 1)
  have hsmall : ∀ k, k ≤ last → value k < BetaModulus newStep k := by
    intro k hk
    have holdModPos : 0 < BetaModulus oldStep (k + 1) :=
      BetaModulus_pos oldStep (k + 1)
    have hvalueOld : value k < BetaModulus oldStep (k + 1) :=
      Nat.mod_lt oldCode holdModPos
    have hmul :
        (k + 2) * oldStep ≤ (last + 2) * oldStep :=
      Nat.mul_le_mul_right oldStep (by omega)
    have holdMod_le_scale : BetaModulus oldStep (k + 1) ≤ scale := by
      simpa [scale, BetaModulus, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using Nat.succ_le_succ hmul
    have hvalue_lt_scale : value k < scale :=
      Nat.lt_of_lt_of_le hvalueOld holdMod_le_scale
    have hbetaFact_ge_one : 1 ≤ betaFact last :=
      betaFact_pos last
    have hscale_le_newStep : scale ≤ newStep := by
      calc
        scale = 1 * scale := by simp
        _ ≤ betaFact last * scale :=
          Nat.mul_le_mul_right scale hbetaFact_ge_one
    have hvalue_lt_newStep : value k < newStep :=
      Nat.lt_of_lt_of_le hvalue_lt_scale hscale_le_newStep
    have hnewStep_le_mod : newStep ≤ BetaModulus newStep k := by
      have hone_le : 1 ≤ k + 1 := by omega
      have hmulStep : 1 * newStep ≤ (k + 1) * newStep :=
        Nat.mul_le_mul_right newStep hone_le
      have hle : newStep ≤ (k + 1) * newStep + 1 := by
        exact Nat.le_trans (by simpa using hmulStep) (Nat.le_succ _)
      simpa [BetaModulus, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hle
    exact Nat.lt_of_lt_of_le hvalue_lt_newStep hnewStep_le_mod
  rcases beta_entries_exist_through_mul_betaFact
      (N := last) (scale := scale) value (by
        simpa [newStep] using hsmall) with ⟨newCode, hnewCode⟩
  refine ⟨newCode, ?_⟩
  intro k hk out hold
  have hvalue : value k = out := by
    simpa [value] using BetaEntry_mod_eq hold
  have hnew : BetaEntry newCode newStep k (value k) :=
    hnewCode k hk
  simpa [BetaShiftTailThrough, newStep, scale, hvalue] using hnew

/-- Existential form of semantic finite shifted-tail construction. -/
theorem BetaShiftTailThrough_exists (oldCode oldStep last : Nat) :
    ∃ newCode newStep,
      BetaShiftTailThrough oldCode oldStep newCode newStep last := by
  rcases BetaShiftTailThrough_exists_with_betaFact_step
      oldCode oldStep last with ⟨newCode, htail⟩
  exact ⟨newCode, betaFact last * BetaModulus oldStep (last + 1), htail⟩

/-- Iterated closed binary halving, used for meta-level trace propagation
statements. -/
def div2Iter (value : Nat) : Nat → Nat
  | 0 => value
  | n + 1 => div2Iter value n / 2

/-- Iterated integer division by two is binary right shift. -/
theorem div2Iter_eq_shiftRight (value k : Nat) :
    div2Iter value k = value >>> k := by
  induction k with
  | zero =>
      simp [div2Iter, Nat.shiftRight_zero]
  | succ k ih =>
      simp [div2Iter, ih]
      exact (Nat.shiftRight_succ value k).symm

/-- If `elem` is not present in the Ackermann bitset `set`, then the
`elem`-th iterated halving current is even. -/
theorem div2Iter_mod_two_eq_zero_of_not_mem {elem set : Nat}
    (hnot : ¬ AckermannHF.Mem elem set) :
    div2Iter set elem % 2 = 0 := by
  have hshiftFalse : (set >>> elem).testBit 0 = false := by
    have hshift := Nat.testBit_shiftRight (i := elem) (j := 0) set
    have hbit := AckermannHF.testBit_false_of_not_mem hnot
    simp [hbit] at hshift ⊢
  have hmod : (set >>> elem) % 2 = 0 := by
    rw [Nat.testBit_zero] at hshiftFalse
    rcases Nat.mod_two_eq_zero_or_one (set >>> elem) with hzero | hone
    · exact hzero
    · have hodd : decide ((set >>> elem) % 2 = 1) = true := by
        simp [hone]
      simp [hodd] at hshiftFalse
  simpa [div2Iter_eq_shiftRight] using hmod

theorem shiftRight_lt_trace_modulus (elem set i : Nat) :
    set >>> i < BetaModulus (betaFact (elem + 1) * (set + 1)) i := by
  let step := betaFact (elem + 1) * (set + 1)
  have hshift : set >>> i ≤ set := Nat.shiftRight_le set i
  have hbf1 : 1 ≤ betaFact (elem + 1) := Nat.succ_le_of_lt (betaFact_pos (elem + 1))
  have hstep_ge : set + 1 ≤ step := by
    have hm := Nat.mul_le_mul_right (set + 1) hbf1
    simpa [step, Nat.mul_comm, Nat.mul_assoc] using hm
  have hset_lt_step : set < step := by omega
  have hstep_le_mul : step ≤ (i + 1) * step := by
    have hi1 : 1 ≤ i + 1 := by omega
    have hm := Nat.mul_le_mul_right step hi1
    simpa [Nat.one_mul, Nat.mul_comm] using hm
  change set >>> i < 1 + (i + 1) * step
  omega

theorem div2_step_shiftRight (set k : Nat) :
    let cur := set >>> k
    let next := set >>> (k + 1)
    let bit := cur % 2
    (bit = 0 ∨ bit = 1) ∧ cur = next + next + bit := by
  intro cur next bit
  have hbit : bit = 0 ∨ bit = 1 := by
    simpa [bit] using Nat.mod_two_eq_zero_or_one cur
  have hnext : next = cur / 2 := by
    simpa [cur, next] using Nat.shiftRight_succ set k
  have hdiv := Nat.div_add_mod cur 2
  constructor
  · exact hbit
  · omega

theorem div2_step_shiftRight_one {set elem : Nat}
    (hmem : AckermannHF.Mem elem set) :
    let cur := set >>> elem
    let next := set >>> (elem + 1)
    cur = next + next + 1 := by
  intro cur next
  have hbitTrue : cur.testBit 0 = true := by
    have hshift := Nat.testBit_shiftRight (i := elem) (j := 0) set
    simpa [AckermannHF.Mem, cur, Nat.add_comm] using hmem.symm.trans hshift.symm
  have hmod : cur % 2 = 1 := by
    rw [Nat.testBit_zero] at hbitTrue
    exact of_decide_eq_true hbitTrue
  have hnext : next = cur / 2 := by
    simpa [cur, next] using Nat.shiftRight_succ set elem
  have hdiv := Nat.div_add_mod cur 2
  omega

theorem HFMemTrace_exists_of_mem {elem set : Nat}
    (hmem : AckermannHF.Mem elem set) :
    ∃ code step, HFMemTrace elem set code step := by
  let N := elem + 1
  let scale := set + 1
  let step := betaFact N * scale
  let value : Nat → Nat := fun k => set >>> k
  have hsmall : ∀ i, i ≤ N → value i < BetaModulus step i := by
    intro i _hi
    simpa [value, step, N, scale] using shiftRight_lt_trace_modulus elem set i
  rcases beta_entries_exist_through_mul_betaFact (N := N) (scale := scale) value hsmall with
    ⟨code, hcode⟩
  refine ⟨code, step, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · have h0 := hcode 0 (by omega)
    simpa [value, step, Nat.shiftRight_zero] using h0
  · intro k hk
    let cur := set >>> k
    let next := set >>> (k + 1)
    let bit := cur % 2
    have hcur : BetaEntry code step k cur := by
      have h := hcode k (by omega)
      simpa [value, cur] using h
    have hnext : BetaEntry code step (k + 1) next := by
      have h := hcode (k + 1) (by omega)
      simpa [value, next] using h
    have hstep := div2_step_shiftRight set k
    refine ⟨cur, next, bit, ?_, ?_, ?_, ?_⟩
    · exact hcur
    · exact hnext
    · simpa [cur, bit] using hstep.1
    · simpa [cur, next, bit] using hstep.2
  · let cur := set >>> elem
    let next := set >>> (elem + 1)
    have hcur : BetaEntry code step elem cur := by
      have h := hcode elem (by omega)
      simpa [value, cur] using h
    have hnext : BetaEntry code step (elem + 1) next := by
      have h := hcode (elem + 1) (by omega)
      simpa [value, next] using h
    have hcurEq : cur = next + next + 1 := by
      simpa [cur, next] using div2_step_shiftRight_one hmem
    refine ⟨cur, next, ?_, ?_, ?_, ?_⟩
    · exact hcur
    · exact hnext
    · exact Or.inr rfl
    · exact hcurEq

theorem BetaEntry_functional {code step idx a b : Nat}
    (ha : BetaEntry code step idx a) (hb : BetaEntry code step idx b) : a = b := by
  rcases ha with ⟨qa, hca, hla⟩
  rcases hb with ⟨qb, hcb, hlb⟩
  let m := BetaModulus step idx
  have hmoda : code % m = a := by
    rw [hca]
    have htmp : (qa * m + a) % m = a := by
      rw [Nat.mul_comm qa m]
      rw [Nat.mul_add_mod_self_left]
      exact Nat.mod_eq_of_lt (by simpa [m] using hla)
    simpa [m] using htmp
  have hmodb : code % m = b := by
    rw [hcb]
    have htmp : (qb * m + b) % m = b := by
      rw [Nat.mul_comm qb m]
      rw [Nat.mul_add_mod_self_left]
      exact Nat.mod_eq_of_lt (by simpa [m] using hlb)
    simpa [m] using htmp
  exact hmoda.symm.trans hmodb

theorem BetaDiv2Step_div_two {code step idx cur next bit : Nat}
    (h : BetaDiv2Step code step idx cur next bit) : cur / 2 = next := by
  rcases h with ⟨_, _, hbit, hcur⟩
  rcases hbit with rfl | rfl
  · rw [hcur, ← Nat.two_mul next]
    rw [Nat.mul_add_div]
    · simp
    · decide
  · rw [hcur, ← Nat.two_mul next]
    rw [Nat.mul_add_div]
    · simp
    · decide

theorem BetaDiv2Step_bit_one_testBit_zero {code step idx cur next : Nat}
    (h : BetaDiv2Step code step idx cur next 1) : cur.testBit 0 = true := by
  rcases h with ⟨_, _, _, hcur⟩
  rw [hcur, Nat.testBit_zero]
  have hshape : next + next + 1 = 1 + 2 * next := by omega
  rw [hshape]
  rw [Nat.add_mul_mod_self_left]
  simp

/-- A beta-coded halving trace whose zeroth entry is `set` computes the
successive binary right shifts of `set`.  This is the semantic invariant that
the PA-side nonmembership proof has to mirror syntactically. -/
theorem BetaDiv2StepsThrough_entry_shiftRight {elem set code step : Nat}
    (hentry : BetaEntry code step 0 set)
    (hsteps : BetaDiv2StepsThrough code step elem) :
    ∀ k value, k ≤ elem + 1 →
      BetaEntry code step k value → value = set >>> k := by
  intro k
  induction k with
  | zero =>
      intro value _ hvalue
      have hv : value = set := BetaEntry_functional hvalue hentry
      simpa [Nat.shiftRight_zero] using hv
  | succ k ih =>
      intro value hle hvalue
      have hk : k ≤ elem := by omega
      rcases hsteps k hk with ⟨cur, next, bit, hstep⟩
      have hcur : cur = set >>> k := ih cur (by omega) hstep.1
      have hvalue_next : value = next :=
        BetaEntry_functional hvalue hstep.2.1
      have hnext : next = cur / 2 :=
        (BetaDiv2Step_div_two hstep).symm
      calc
        value = next := hvalue_next
        _ = cur / 2 := hnext
        _ = (set >>> k) / 2 := by rw [hcur]
        _ = set >>> (k+1) := (Nat.shiftRight_succ set k).symm

/-- `HFMemTrace`-packaged form of
`BetaDiv2StepsThrough_entry_shiftRight`. -/
theorem HFMemTrace_entry_shiftRight {elem set code step : Nat}
    (h : HFMemTrace elem set code step) :
    ∀ k value, k ≤ elem + 1 →
      BetaEntry code step k value → value = set >>> k :=
  BetaDiv2StepsThrough_entry_shiftRight h.1 h.2.1

/-- In any semantic halving trace starting from `set`, if `elem` is absent
from `set`, then the halving step at `elem` has output bit `0`. -/
theorem BetaDiv2Step_bit_zero_of_not_mem
    {elem set code step cur next bit : Nat}
    (hentry : BetaEntry code step 0 set)
    (hsteps : BetaDiv2StepsThrough code step elem)
    (hstep : BetaDiv2Step code step elem cur next bit)
    (hnot : ¬ AckermannHF.Mem elem set) :
    bit = 0 := by
  have hcur : cur = set >>> elem :=
    BetaDiv2StepsThrough_entry_shiftRight hentry hsteps elem cur
      (by omega) hstep.1
  have hshiftFalse : (set >>> elem).testBit 0 = false := by
    have hshift := Nat.testBit_shiftRight (i := elem) (j := 0) set
    have hbit := AckermannHF.testBit_false_of_not_mem hnot
    simp [hbit] at hshift ⊢
  rcases hstep.2.2.1 with hbitZero | hbitOne
  · exact hbitZero
  · subst bit
    have hone : cur.testBit 0 = true :=
      BetaDiv2Step_bit_one_testBit_zero hstep
    have hcurFalse : cur.testBit 0 = false := by
      simpa [hcur] using hshiftFalse
    exact False.elim (by simp [hcurFalse] at hone)

/-- In the same situation, the semantic current value is exactly twice the
next value. -/
theorem BetaDiv2Step_current_double_of_not_mem
    {elem set code step cur next bit : Nat}
    (hentry : BetaEntry code step 0 set)
    (hsteps : BetaDiv2StepsThrough code step elem)
    (hstep : BetaDiv2Step code step elem cur next bit)
    (hnot : ¬ AckermannHF.Mem elem set) :
    cur = next + next := by
  have hbit : bit = 0 :=
    BetaDiv2Step_bit_zero_of_not_mem hentry hsteps hstep hnot
  rcases hstep with ⟨_, _, _, hcur⟩
  omega

theorem HFMemTrace_mem {elem set code step : Nat}
    (h : HFMemTrace elem set code step) : AckermannHF.Mem elem set := by
  rcases h.2.2 with ⟨cur, next, hstep⟩
  have hcur : cur = set >>> elem :=
    HFMemTrace_entry_shiftRight h elem cur (by omega) hstep.1
  have hlow : (set >>> elem).testBit 0 = true := by
    have hbit := BetaDiv2Step_bit_one_testBit_zero hstep
    simpa [hcur] using hbit
  have hshift := Nat.testBit_shiftRight (i := elem) (j := 0) set
  rw [hshift] at hlow
  simpa [AckermannHF.Mem] using hlow

/-- Semantic trace existence for the carry fact used by the high-even
successor branch: a positive-bit membership trace in an even code can be
replaced by a membership trace for the incremented code. -/
theorem HFMemTrace_succ_of_double_mem_succ
    {x set half code step : Nat}
    (hset : set = half + half)
    (htrace : HFMemTrace (x+1) set code step) :
    ∃ code' step', HFMemTrace (x+1) (set+1) code' step' := by
  exact HFMemTrace_exists_of_mem
    (AckermannHF.mem_succ_of_double_mem_succ hset
      (HFMemTrace_mem htrace))

/-- Semantic trace transport for the inverse even-code membership step:
if `S x` is witnessed as a member of an explicitly even code `2*half`, then
`x` has a membership trace in `half`.

The object-language proof cannot simply invoke this semantic lemma, but this
records the exact trace invariant that the later PA beta-tail construction
must realize. -/
theorem HFMemTrace_pred_of_succ_double
    {x set half code step : Nat}
    (hset : set = half + half)
    (htrace : HFMemTrace (x+1) set code step) :
    ∃ code' step', HFMemTrace x half code' step' := by
  have hmemSet : AckermannHF.Mem (x+1) set :=
    HFMemTrace_mem htrace
  have hmemDouble : AckermannHF.Mem (x+1) (half + half) := by
    simpa [hset] using hmemSet
  exact HFMemTrace_exists_of_mem
    ((AckermannHF.mem_succ_double_iff x half).mp hmemDouble)

/-- Semantic trace transport for the inverse odd-code membership step:
if `S x` is witnessed as a member of `2*half+1`, then `x` has a membership
trace in `half`. -/
theorem HFMemTrace_pred_of_succ_odd_double
    {x set half code step : Nat}
    (hset : set = half + half + 1)
    (htrace : HFMemTrace (x+1) set code step) :
    ∃ code' step', HFMemTrace x half code' step' := by
  have hmemSet : AckermannHF.Mem (x+1) set :=
    HFMemTrace_mem htrace
  have hmemOdd : AckermannHF.Mem (x+1) (half + half + 1) := by
    simpa [hset] using hmemSet
  exact HFMemTrace_exists_of_mem
    ((AckermannHF.mem_succ_odd_double_iff x half).mp hmemOdd)

/-- Unified semantic trace transport for the inverse halving step.

If `set` is `2 * half + bit` with `bit` boolean, then a trace witnessing
`S x ∈ set` yields some trace witnessing `x ∈ half`.  The object-language PA
proof still has to construct the new beta witnesses syntactically; this theorem
is the reusable semantic specification for that beta-tail construction. -/
theorem HFMemTrace_pred_of_succ_div2Step
    {x set half bit code step : Nat}
    (hbit : bit = 0 ∨ bit = 1)
    (hset : set = half + half + bit)
    (htrace : HFMemTrace (x+1) set code step) :
    ∃ code' step', HFMemTrace x half code' step' := by
  rcases hbit with rfl | rfl
  · exact HFMemTrace_pred_of_succ_double
      (x := x) (set := set) (half := half) (code := code) (step := step)
      (by omega) htrace
  · exact HFMemTrace_pred_of_succ_odd_double
      (x := x) (set := set) (half := half) (code := code) (step := step)
      (by omega) htrace

/-- Transport one semantic binary-halving step through a shifted beta tail.

The old step at index `k+1` uses old entries `k+1` and `k+2`; a tail through
`last` with `k+1 <= last` copies those entries to new indices `k` and `k+1`,
leaving the binary-halving equation unchanged. -/
theorem BetaShiftTailThrough_step
    {oldCode oldStep newCode newStep last k cur next bit : Nat}
    (htail : BetaShiftTailThrough oldCode oldStep newCode newStep last)
    (hkNext : k + 1 ≤ last)
    (hstep : BetaDiv2Step oldCode oldStep (k + 1) cur next bit) :
    BetaDiv2Step newCode newStep k cur next bit := by
  rcases hstep with ⟨hcur, hnext, hbit, hvalue⟩
  refine ⟨?_, ?_, hbit, hvalue⟩
  · exact htail k (by omega) cur hcur
  · simpa [Nat.add_assoc] using
      htail (k+1) hkNext next hnext

/-- Transport a semantic bounded halving trace through a shifted beta tail. -/
theorem BetaShiftTailThrough_stepsThrough
    {oldCode oldStep newCode newStep last : Nat}
    (htail : BetaShiftTailThrough oldCode oldStep newCode newStep (last+1))
    (hsteps : BetaDiv2StepsThrough oldCode oldStep (last+1)) :
    BetaDiv2StepsThrough newCode newStep last := by
  intro k hk
  rcases hsteps (k+1) (by omega) with ⟨cur, next, bit, hstep⟩
  exact ⟨cur, next, bit,
    BetaShiftTailThrough_step
      (oldCode := oldCode) (oldStep := oldStep)
      (newCode := newCode) (newStep := newStep)
      (last := last+1) (k := k) (cur := cur) (next := next)
      (bit := bit) htail (by omega) hstep⟩

/-- Transport a semantic final-bit witness through a shifted beta tail. -/
theorem BetaShiftTailThrough_bit
    {oldCode oldStep newCode newStep idx bit : Nat}
    (htail : BetaShiftTailThrough oldCode oldStep newCode newStep (idx+1))
    (hbit : BetaDiv2Bit oldCode oldStep (idx+1) bit) :
    BetaDiv2Bit newCode newStep idx bit := by
  rcases hbit with ⟨cur, next, hstep⟩
  exact ⟨cur, next,
    BetaShiftTailThrough_step
      (oldCode := oldCode) (oldStep := oldStep)
      (newCode := newCode) (newStep := newStep)
      (last := idx+1) (k := idx) (cur := cur) (next := next)
      (bit := bit) htail (by omega) hstep⟩

/-- A shifted beta tail turns an `S x` membership trace into an `x` trace for
the first halving successor.

This is the semantic invariant behind the object-language shifted-tail
construction: the old step at index `0` supplies the new entry value `half`,
the shifted tail transports all later halving steps, and the old final `1` bit
at index `S x` becomes the new final `1` bit at index `x`. -/
theorem HFMemTrace_pred_of_shift_tail
    {x set half bit oldCode oldStep newCode newStep : Nat}
    (htrace : HFMemTrace (x+1) set oldCode oldStep)
    (hstep0 : BetaDiv2Step oldCode oldStep 0 set half bit)
    (htail : BetaShiftTailThrough oldCode oldStep newCode newStep (x+1)) :
    HFMemTrace x half newCode newStep := by
  rcases htrace with ⟨_hentry, hsteps, hbitOne⟩
  refine ⟨?_, ?_, ?_⟩
  · exact htail 0 (by omega) half hstep0.2.1
  · exact BetaShiftTailThrough_stepsThrough htail hsteps
  · exact BetaShiftTailThrough_bit htail hbitOne

/-- Existential semantic predecessor trace obtained by choosing the fresh
shifted beta tail with the CRT construction. -/
theorem HFMemTrace_pred_of_shift_tail_exists
    {x set half bit oldCode oldStep : Nat}
    (htrace : HFMemTrace (x+1) set oldCode oldStep)
    (hstep0 : BetaDiv2Step oldCode oldStep 0 set half bit) :
    ∃ newCode newStep, HFMemTrace x half newCode newStep := by
  rcases BetaShiftTailThrough_exists oldCode oldStep (x+1) with
    ⟨newCode, newStep, htail⟩
  exact ⟨newCode, newStep,
    HFMemTrace_pred_of_shift_tail htrace hstep0 htail⟩

theorem hfMemAt_sound (e : Nat → Nat) (elem set : Nat) :
    Sat natModel e (hfMemAt elem set) → AckermannHF.Mem (e elem) (e set) := by
  intro h
  rcases (hfMemAt_nat_trace e elem set).mp h with ⟨code, step, htrace⟩
  exact HFMemTrace_mem htrace

theorem hfMemAt_complete (e : Nat → Nat) (elem set : Nat) :
    AckermannHF.Mem (e elem) (e set) → Sat natModel e (hfMemAt elem set) := by
  intro hmem
  rcases HFMemTrace_exists_of_mem hmem with ⟨code, step, htrace⟩
  exact (hfMemAt_nat_trace e elem set).mpr ⟨code, step, htrace⟩

theorem hfMemAt_exact (e : Nat → Nat) (elem set : Nat) :
    Sat natModel e (hfMemAt elem set) ↔ AckermannHF.Mem (e elem) (e set) := by
  constructor
  · exact hfMemAt_sound e elem set
  · exact hfMemAt_complete e elem set

theorem hfMemAt_free {i elem set : Nat} (h : Free i (hfMemAt elem set)) :
    i = elem ∨ i = set := by
  simp [hfMemAt, betaDiv2BitAt, betaDiv2StepsThroughAt, betaDiv2StepWitnessAt,
    betaAtConstIdx, betaAtSuccIdx, betaAt, remAt, ltAt, leAt, div2StepAt,
    boolAt, zeroAt, oneAt, eqConstAt, betaModTerm, Free, Term.Free,
    Term.rename, Term.numeral] at h
  omega

/-- Slot-map extension across a translated HF quantifier.  The newly bound HF
variable is represented by the newly bound PA variable `0`; older HF variables
are shifted past it. -/
def hfUpVarMap (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n+1 => ρ n + 1

@[simp] theorem hfUpVarMap_id :
    hfUpVarMap (fun n : Nat => n) = (fun n : Nat => n) := by
  funext n
  cases n <;> rfl

/-- Translate set-theory formulas to PA formulas using Ackermann membership.
The HF domain is all natural numbers, so quantifiers are not relativized. -/
def hfFormulaAt (ρ : Nat → Nat) : Form → Formula
  | Form.fMem i j => hfMemAt (ρ i) (ρ j)
  | Form.fEq i j => eq (Term.var (ρ i)) (Term.var (ρ j))
  | Form.fBot => bot
  | Form.fImp a b => imp (hfFormulaAt ρ a) (hfFormulaAt ρ b)
  | Form.fAnd a b => and (hfFormulaAt ρ a) (hfFormulaAt ρ b)
  | Form.fOr a b => or (hfFormulaAt ρ a) (hfFormulaAt ρ b)
  | Form.fAll a => all (hfFormulaAt (hfUpVarMap ρ) a)
  | Form.fEx a => ex (hfFormulaAt (hfUpVarMap ρ) a)

theorem hfFormulaAt_free (phi : Form) :
    ∀ {ρ : Nat → Nat} {i : Nat}, Free i (hfFormulaAt ρ phi) →
      ∃ n, SetTheory.Free n phi ∧ i = ρ n := by
  induction phi with
  | fMem a b =>
      intro ρ i h
      rcases hfMemAt_free h with hi | hi
      · exact ⟨a, Or.inl rfl, hi⟩
      · exact ⟨b, Or.inr rfl, hi⟩
  | fEq a b =>
      intro ρ i h
      simp only [hfFormulaAt, Free, Term.Free] at h
      rcases h with hi | hi
      · exact ⟨a, Or.inl rfl, hi⟩
      · exact ⟨b, Or.inr rfl, hi⟩
  | fBot =>
      intro ρ i h
      cases h
  | fImp a b iha ihb =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | fAnd a b iha ihb =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | fOr a b iha ihb =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases h with h | h
      · rcases iha h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inl hn, hi⟩
      · rcases ihb h with ⟨n, hn, hi⟩
        exact ⟨n, Or.inr hn, hi⟩
  | fAll a ih =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases ih h with ⟨n, hn, hi⟩
      cases n with
      | zero =>
          simp [hfUpVarMap] at hi
      | succ n =>
          exists n
          constructor
          · exact hn
          · simp [hfUpVarMap] at hi
            omega
  | fEx a ih =>
      intro ρ i h
      simp only [hfFormulaAt, Free] at h
      rcases ih h with ⟨n, hn, hi⟩
      cases n with
      | zero =>
          simp [hfUpVarMap] at hi
      | succ n =>
          exists n
          constructor
          · exact hn
          · simp [hfUpVarMap] at hi
            omega

/-- The default HF-in-PA translation reads HF variable `n` from PA slot `n`. -/
def translateHFFormula (phi : Form) : Formula :=
  hfFormulaAt (fun n : Nat => n) phi

/-- Context-level counterpart of `hfFormulaAt`. -/
def hfContextAt (ρ : Nat → Nat) (G : List Form) : List Formula :=
  G.map (hfFormulaAt ρ)

/-- Default context translation for the HF-in-PA interpretation. -/
def translateHFContext (G : List Form) : List Formula :=
  G.map translateHFFormula

theorem translateHFContext_eq_hfContextAt_id (G : List Form) :
    translateHFContext G = hfContextAt (fun n : Nat => n) G := by
  simp [translateHFContext, hfContextAt, translateHFFormula]

theorem hfFormulaAt_ext (phi : Form) :
    ∀ {ρ σ : Nat → Nat},
      (∀ n, ρ n = σ n) → hfFormulaAt ρ phi = hfFormulaAt σ phi := by
  induction phi with
  | fMem i j =>
      intro ρ σ h
      simp [hfFormulaAt, h]
  | fEq i j =>
      intro ρ σ h
      simp [hfFormulaAt, h]
  | fBot =>
      intro ρ σ h
      rfl
  | fImp a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha h, ihb h]
  | fAnd a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha h, ihb h]
  | fOr a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha h, ihb h]
  | fAll a ih =>
      intro ρ σ h
      simp only [hfFormulaAt]
      apply congrArg all
      exact ih (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [hfUpVarMap, h n])
  | fEx a ih =>
      intro ρ σ h
      simp only [hfFormulaAt]
      apply congrArg ex
      exact ih (fun n => by
        cases n with
        | zero => rfl
        | succ n => simp [hfUpVarMap, h n])

/-- HF-in-PA translation only depends on the slot map at variables free in the
source HF formula. -/
theorem hfFormulaAt_ext_free (phi : Form) :
    ∀ {ρ σ : Nat → Nat},
      (∀ n, SetTheory.Free n phi → ρ n = σ n) →
        hfFormulaAt ρ phi = hfFormulaAt σ phi := by
  induction phi with
  | fMem i j =>
      intro ρ σ h
      simp [hfFormulaAt, h i (Or.inl rfl), h j (Or.inr rfl)]
  | fEq i j =>
      intro ρ σ h
      simp [hfFormulaAt, h i (Or.inl rfl), h j (Or.inr rfl)]
  | fBot =>
      intro ρ σ h
      rfl
  | fImp a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha (fun n hn => h n (Or.inl hn)),
        ihb (fun n hn => h n (Or.inr hn))]
  | fAnd a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha (fun n hn => h n (Or.inl hn)),
        ihb (fun n hn => h n (Or.inr hn))]
  | fOr a b iha ihb =>
      intro ρ σ h
      simp [hfFormulaAt, iha (fun n hn => h n (Or.inl hn)),
        ihb (fun n hn => h n (Or.inr hn))]
  | fAll a ih =>
      intro ρ σ h
      simp only [hfFormulaAt]
      apply congrArg all
      exact ih (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [hfUpVarMap, h n hn])
  | fEx a ih =>
      intro ρ σ h
      simp only [hfFormulaAt]
      apply congrArg ex
      exact ih (fun n hn => by
        cases n with
        | zero => rfl
        | succ n => simp [hfUpVarMap, h n hn])

theorem hfFormulaAt_source_rename (phi : Form) (ρ r : Nat → Nat) :
    hfFormulaAt ρ (SetTheory.rename r phi) =
      hfFormulaAt (fun n => ρ (r n)) phi := by
  induction phi generalizing ρ r with
  | fMem i j =>
      rfl
  | fEq i j =>
      rfl
  | fBot =>
      rfl
  | fImp a b iha ihb =>
      simp [SetTheory.rename, hfFormulaAt, iha, ihb]
  | fAnd a b iha ihb =>
      simp [SetTheory.rename, hfFormulaAt, iha, ihb]
  | fOr a b iha ihb =>
      simp [SetTheory.rename, hfFormulaAt, iha, ihb]
  | fAll a ih =>
      simp only [SetTheory.rename, hfFormulaAt]
      apply congrArg all
      calc
        hfFormulaAt (hfUpVarMap ρ) (SetTheory.rename (SetTheory.up r) a)
            = hfFormulaAt (fun n => hfUpVarMap ρ (SetTheory.up r n)) a := by
                exact ih (hfUpVarMap ρ) (SetTheory.up r)
        _ = hfFormulaAt (hfUpVarMap (fun n => ρ (r n))) a := by
                exact hfFormulaAt_ext a (fun n => by
                  cases n with
                  | zero => rfl
                  | succ n => rfl)
  | fEx a ih =>
      simp only [SetTheory.rename, hfFormulaAt]
      apply congrArg ex
      calc
        hfFormulaAt (hfUpVarMap ρ) (SetTheory.rename (SetTheory.up r) a)
            = hfFormulaAt (fun n => hfUpVarMap ρ (SetTheory.up r n)) a := by
                exact ih (hfUpVarMap ρ) (SetTheory.up r)
        _ = hfFormulaAt (hfUpVarMap (fun n => ρ (r n))) a := by
                exact hfFormulaAt_ext a (fun n => by
                  cases n with
                  | zero => rfl
                  | succ n => rfl)

theorem rename_hfFormulaAt (phi : Form) (ρ r : Nat → Nat) :
    rename r (hfFormulaAt ρ phi) =
      hfFormulaAt (fun n => r (ρ n)) phi := by
  induction phi generalizing ρ r with
  | fMem i j =>
      simp [hfFormulaAt, rename_hfMemAt]
  | fEq i j =>
      rfl
  | fBot =>
      rfl
  | fImp a b iha ihb =>
      simp [hfFormulaAt, rename, iha, ihb]
  | fAnd a b iha ihb =>
      simp [hfFormulaAt, rename, iha, ihb]
  | fOr a b iha ihb =>
      simp [hfFormulaAt, rename, iha, ihb]
  | fAll a ih =>
      simp only [hfFormulaAt, rename]
      apply congrArg all
      calc
        rename (SetTheory.up r) (hfFormulaAt (hfUpVarMap ρ) a)
            = hfFormulaAt (fun n => SetTheory.up r (hfUpVarMap ρ n)) a := by
                exact ih (hfUpVarMap ρ) (SetTheory.up r)
        _ = hfFormulaAt (hfUpVarMap (fun n => r (ρ n))) a := by
                exact hfFormulaAt_ext a (fun n => by
                  cases n with
                  | zero => rfl
                  | succ n => rfl)
  | fEx a ih =>
      simp only [hfFormulaAt, rename]
      apply congrArg ex
      calc
        rename (SetTheory.up r) (hfFormulaAt (hfUpVarMap ρ) a)
            = hfFormulaAt (fun n => SetTheory.up r (hfUpVarMap ρ n)) a := by
                exact ih (hfUpVarMap ρ) (SetTheory.up r)
        _ = hfFormulaAt (hfUpVarMap (fun n => r (ρ n))) a := by
                exact hfFormulaAt_ext a (fun n => by
                  cases n with
                  | zero => rfl
                  | succ n => rfl)

/-- HF-to-PA translation is natural in source and target variable maps: a
commuting square of maps induces a commuting square of formula renamings. -/
theorem hfFormulaAt_rename_natural (phi : Form)
    (ρ σ r s : Nat → Nat)
    (h : ∀ n, ρ (r n) = s (σ n)) :
    hfFormulaAt ρ (SetTheory.rename r phi) =
      rename s (hfFormulaAt σ phi) := by
  calc
    hfFormulaAt ρ (SetTheory.rename r phi) =
        hfFormulaAt (fun n => ρ (r n)) phi :=
      hfFormulaAt_source_rename phi ρ r
    _ = hfFormulaAt (fun n => s (σ n)) phi :=
      hfFormulaAt_ext phi h
    _ = rename s (hfFormulaAt σ phi) :=
      (rename_hfFormulaAt phi σ s).symm

theorem hfFormulaAt_id_rename (phi : Form) (r : Nat → Nat) :
    hfFormulaAt (fun n : Nat => n) (SetTheory.rename r phi) =
      rename r (hfFormulaAt (fun n => n) phi) := by
  exact hfFormulaAt_rename_natural phi
    (fun n => n) (fun n => n) r r (fun _ => rfl)

theorem hfFormulaAt_rename_succ (phi : Form) (ρ : Nat → Nat) :
    hfFormulaAt (hfUpVarMap ρ) (SetTheory.rename Nat.succ phi) =
      rename Nat.succ (hfFormulaAt ρ phi) := by
  exact hfFormulaAt_rename_natural phi
    (hfUpVarMap ρ) ρ Nat.succ Nat.succ (fun _ => rfl)

theorem hfContextAt_rename_succ (ρ : Nat → Nat) (G : List Form) :
    hfContextAt (hfUpVarMap ρ) (G.map (SetTheory.rename Nat.succ)) =
      (hfContextAt ρ G).map (rename Nat.succ) := by
  simp only [hfContextAt, List.map_map]
  apply List.map_congr_left
  intro phi _hphi
  exact hfFormulaAt_rename_succ phi ρ

theorem hfContextAt_cons_rename_succ (ρ : Nat → Nat) (a : Form)
    (G : List Form) :
    hfContextAt (hfUpVarMap ρ)
        (a :: G.map (SetTheory.rename Nat.succ)) =
      hfFormulaAt (hfUpVarMap ρ) a ::
        (hfContextAt ρ G).map (rename Nat.succ) := by
  simp only [hfContextAt, List.map_cons]
  exact congrArg (fun tail => hfFormulaAt (hfUpVarMap ρ) a :: tail)
    (hfContextAt_rename_succ ρ G)

theorem subst_instTerm_var_hfFormulaAt (phi : Form) (ρ : Nat → Nat)
    (k : Nat) :
    subst (instTerm (Term.var (ρ k))) (hfFormulaAt (hfUpVarMap ρ) phi) =
      hfFormulaAt ρ (SetTheory.rename (SetTheory.inst k) phi) := by
  rw [subst_instTerm_var]
  exact (hfFormulaAt_rename_natural phi
    ρ (hfUpVarMap ρ)
    (SetTheory.inst k) (SetTheory.inst (ρ k))
    (fun n => by cases n <;> rfl)).symm

theorem hfFormulaAt_eq_translateHFFormula_of_HF_sentence (phi : Form)
    (ρ : Nat → Nat) (hphi : SetTheory.Sentence phi) :
    hfFormulaAt ρ phi = translateHFFormula phi := by
  unfold translateHFFormula
  exact hfFormulaAt_ext_free phi
    (fun n hn => False.elim (hphi n hn))

theorem hfFormulaAt_exact (phi : Form) :
    ∀ (ρ : Nat → Nat) (v e : Nat → Nat),
      (∀ n, e (ρ n) = v n) →
        (Sat natModel e (hfFormulaAt ρ phi) ↔ SetTheory.Sat AckermannHF.Mem v phi) := by
  induction phi with
  | fMem i j =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat]
      rw [hfMemAt_exact]
      rw [hρ i, hρ j]
  | fEq i j =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat, Term.eval]
      constructor
      · intro h
        rw [← hρ i, ← hρ j]
        exact h
      · intro h
        rw [hρ i, hρ j]
        exact h
  | fBot =>
      intro ρ v e _hρ
      simp [hfFormulaAt, SetTheory.Sat, Sat]
  | fImp a b iha ihb =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      rw [iha ρ v e hρ, ihb ρ v e hρ]
  | fAnd a b iha ihb =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      rw [iha ρ v e hρ, ihb ρ v e hρ]
  | fOr a b iha ihb =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      rw [iha ρ v e hρ, ihb ρ v e hρ]
  | fAll a ih =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      constructor
      · intro h d
        have hρ' : ∀ n, (scons d e) (hfUpVarMap ρ n) = (scons d v) n := by
          intro n
          cases n with
          | zero => simp [hfUpVarMap, scons]
          | succ n => simp [hfUpVarMap, scons, hρ n]
        exact (ih (hfUpVarMap ρ) (scons d v) (scons d e) hρ').mp (h d)
      · intro h d
        have hρ' : ∀ n, (scons d e) (hfUpVarMap ρ n) = (scons d v) n := by
          intro n
          cases n with
          | zero => simp [hfUpVarMap, scons]
          | succ n => simp [hfUpVarMap, scons, hρ n]
        exact (ih (hfUpVarMap ρ) (scons d v) (scons d e) hρ').mpr (h d)
  | fEx a ih =>
      intro ρ v e hρ
      simp only [hfFormulaAt, SetTheory.Sat, Sat]
      constructor
      · intro h
        rcases h with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        have hρ' : ∀ n, (scons d e) (hfUpVarMap ρ n) = (scons d v) n := by
          intro n
          cases n with
          | zero => simp [hfUpVarMap, scons]
          | succ n => simp [hfUpVarMap, scons, hρ n]
        exact (ih (hfUpVarMap ρ) (scons d v) (scons d e) hρ').mp hd
      · intro h
        rcases h with ⟨d, hd⟩
        refine ⟨d, ?_⟩
        have hρ' : ∀ n, (scons d e) (hfUpVarMap ρ n) = (scons d v) n := by
          intro n
          cases n with
          | zero => simp [hfUpVarMap, scons]
          | succ n => simp [hfUpVarMap, scons, hρ n]
        exact (ih (hfUpVarMap ρ) (scons d v) (scons d e) hρ').mpr hd

theorem translateHFFormula_exact (phi : Form) (v : Nat → Nat) :
    Sat natModel v (translateHFFormula phi) ↔ SetTheory.Sat AckermannHF.Mem v phi :=
  hfFormulaAt_exact phi (fun n : Nat => n) v v (fun _ => rfl)

theorem translated_HF_axiom_sat_nat (phi : Form)
    (hphi : AckermannHF.HFAx_s phi) (v : Nat → Nat) :
    Sat natModel v (translateHFFormula phi) :=
  (translateHFFormula_exact phi v).mpr (AckermannHF.standard_sat_HF v phi hphi)

theorem translated_HFFin_axiom_sat_nat (phi : Form)
    (hphi : AckermannHF.HFFinAx_s phi) (v : Nat → Nat) :
    Sat natModel v (translateHFFormula phi) :=
  (translateHFFormula_exact phi v).mpr (AckermannHF.standard_sat_HFFin v phi hphi)

theorem hfFormulaAt_sentence_of_HF_sentence (phi : Form) (ρ : Nat → Nat)
    (hphi : SetTheory.Sentence phi) : Sentence (hfFormulaAt ρ phi) := by
  intro i hi
  rcases hfFormulaAt_free phi hi with ⟨n, hn, _⟩
  exact hphi n hn

theorem translateHFFormula_sentence_of_HF_sentence (phi : Form)
    (hphi : SetTheory.Sentence phi) : Sentence (translateHFFormula phi) :=
  hfFormulaAt_sentence_of_HF_sentence phi (fun n : Nat => n) hphi

theorem translated_HF_axiom_sentence (g : Form)
    (hg : AckermannHF.HFAx_s g) : Sentence (translateHFFormula g) :=
  translateHFFormula_sentence_of_HF_sentence g (AckermannHF.Sentences_HF g hg)

theorem translated_HFFin_axiom_sentence (g : Form)
    (hg : AckermannHF.HFFinAx_s g) : Sentence (translateHFFormula g) :=
  translateHFFormula_sentence_of_HF_sentence g (AckermannHF.Sentences_HFFin g hg)

/-- The PA-side theory consisting of syntactic translations of the sealed HF
axiom-scheme instances. -/
def translatedHFAx (phi : Formula) : Prop :=
  ∃ g, AckermannHF.HFAx_s g ∧ phi = translateHFFormula g

/-- The PA-side theory consisting of syntactic translations of the strengthened
hereditary-finite axiom-scheme instances.  This is the PA-side target for the
HF-in-PA half of the PA/HFFin deductive bi-interpretability theorem. -/
def translatedHFFinAx (phi : Formula) : Prop :=
  ∃ g, AckermannHF.HFFinAx_s g ∧ phi = translateHFFormula g

theorem translatedHFAx_intro {g : Form} (hg : AckermannHF.HFAx_s g) :
    translatedHFAx (translateHFFormula g) :=
  ⟨g, hg, rfl⟩

theorem translatedHFFinAx_intro {g : Form} (hg : AckermannHF.HFFinAx_s g) :
    translatedHFFinAx (translateHFFormula g) :=
  ⟨g, hg, rfl⟩

theorem translatedHFFinAx_of_translatedHFAx {phi : Formula}
    (hphi : translatedHFAx phi) : translatedHFFinAx phi := by
  rcases hphi with ⟨g, hg, rfl⟩
  exact translatedHFFinAx_intro (AckermannHF.HFFinAx_s_of_HFAx_s hg)

theorem Sentences_translatedHFAx : ∀ phi, translatedHFAx phi → Sentence phi := by
  intro phi hphi
  rcases hphi with ⟨g, hg, rfl⟩
  exact translated_HF_axiom_sentence g hg

theorem Sentences_translatedHFFinAx :
    ∀ phi, translatedHFFinAx phi → Sentence phi := by
  intro phi hphi
  rcases hphi with ⟨g, hg, rfl⟩
  exact translated_HFFin_axiom_sentence g hg

theorem BProv_translatedHFAx_of_HFAx {g : Form} (hg : AckermannHF.HFAx_s g) :
    BProv translatedHFAx [] (translateHFFormula g) :=
  BProv_ax (translatedHFAx_intro hg)

theorem BProv_translatedHFFinAx_of_HFFinAx {g : Form}
    (hg : AckermannHF.HFFinAx_s g) :
    BProv translatedHFFinAx [] (translateHFFormula g) :=
  BProv_ax (translatedHFFinAx_intro hg)

theorem BProv_lift_translatedHFAx_to_PA
    (hAx : ∀ f, translatedHFAx f → BProv Ax_s [] f)
    {f : Formula} (h : BProv translatedHFAx [] f) : BProv Ax_s [] f :=
  BProv_lift h hAx (fun _ hg => nomatch hg)

theorem BProv_lift_translatedHFFinAx_to_PA
    (hAx : ∀ f, translatedHFFinAx f → BProv Ax_s [] f)
    {f : Formula} (h : BProv translatedHFFinAx [] f) : BProv Ax_s [] f :=
  BProv_lift h hAx (fun _ hg => nomatch hg)

theorem standard_sat_translatedHFAx (e : Nat → Nat) :
    ∀ g, translatedHFAx g → Sat natModel e g := by
  intro g hg
  rcases hg with ⟨phi, hphi, rfl⟩
  exact translated_HF_axiom_sat_nat phi hphi e

theorem standard_sat_translatedHFFinAx (e : Nat → Nat) :
    ∀ g, translatedHFFinAx g → Sat natModel e g := by
  intro g hg
  rcases hg with ⟨phi, hphi, rfl⟩
  exact translated_HFFin_axiom_sat_nat phi hphi e

/-- Pure first-order HF derivations translate structurally to PA derivations
under the Ackermann membership translation.

This theorem is intentionally only a proof-calculus translation: source axioms
are not discharged here.  The bounded axiom list introduced by `BProv` is
handled separately by the `BProv_hfFormulaAt_of_BProv_*` variants. -/
theorem Prov_hfFormulaAt_of_Prov {G : List Form} {phi : Form}
    (h : SetTheory.Prov G phi) :
    ∀ ρ : Nat → Nat, Prov (hfContextAt ρ G) (hfFormulaAt ρ phi) := by
  induction h with
  | P_ass G a hin =>
      intro ρ
      exact Prov.P_ass _ _ (List.mem_map_of_mem (f := hfFormulaAt ρ) hin)
  | P_impI G a b _ ih =>
      intro ρ
      exact Prov.P_impI _ _ _ (ih ρ)
  | P_impE G a b _ _ ihab iha =>
      intro ρ
      exact Prov.P_impE _ (hfFormulaAt ρ a) (hfFormulaAt ρ b)
        (ihab ρ) (iha ρ)
  | P_botE G a _ ih =>
      intro ρ
      exact Prov.P_botE _ (hfFormulaAt ρ a) (ih ρ)
  | P_lem G a =>
      intro ρ
      exact Prov.P_lem _ _
  | P_andI G a b _ _ iha ihb =>
      intro ρ
      exact Prov.P_andI _ _ _ (iha ρ) (ihb ρ)
  | P_andE1 G a b _ ih =>
      intro ρ
      exact Prov.P_andE1 _ (hfFormulaAt ρ a) (hfFormulaAt ρ b) (ih ρ)
  | P_andE2 G a b _ ih =>
      intro ρ
      exact Prov.P_andE2 _ (hfFormulaAt ρ a) (hfFormulaAt ρ b) (ih ρ)
  | P_orI1 G a b _ ih =>
      intro ρ
      exact Prov.P_orI1 _ _ _ (ih ρ)
  | P_orI2 G a b _ ih =>
      intro ρ
      exact Prov.P_orI2 _ _ _ (ih ρ)
  | P_orE G a b c _ _ _ ihor iha ihb =>
      intro ρ
      exact Prov.P_orE _ (hfFormulaAt ρ a) (hfFormulaAt ρ b)
        (hfFormulaAt ρ c) (ihor ρ) (iha ρ) (ihb ρ)
  | P_allI G a _ ih =>
      intro ρ
      apply Prov.P_allI
      have hbody := ih (hfUpVarMap ρ)
      rwa [hfContextAt_rename_succ ρ G] at hbody
  | P_allE G a k _ ih =>
      intro ρ
      have hinst := Prov.P_allE _ (hfFormulaAt (hfUpVarMap ρ) a)
        (Term.var (ρ k)) (ih ρ)
      simpa [hfFormulaAt, subst_instTerm_var_hfFormulaAt] using hinst
  | P_exI G a k _ ih =>
      intro ρ
      apply Prov.P_exI _ (hfFormulaAt (hfUpVarMap ρ) a)
        (Term.var (ρ k))
      simpa [hfFormulaAt, subst_instTerm_var_hfFormulaAt] using ih ρ
  | P_exE G a c _ _ ihex ihbody =>
      intro ρ
      apply Prov.P_exE _ (hfFormulaAt (hfUpVarMap ρ) a) (hfFormulaAt ρ c)
      · exact ihex ρ
      · have hbody := ihbody (hfUpVarMap ρ)
        rw [hfContextAt_cons_rename_succ ρ a G,
          hfFormulaAt_rename_succ c ρ] at hbody
        exact hbody
  | P_eqRefl G k =>
      intro ρ
      exact Prov.P_eqRefl _ (Term.var (ρ k))
  | P_eqElim G i j a _ _ iheq iha =>
      intro ρ
      have hbody :
          Prov (hfContextAt ρ G)
            (subst (instTerm (Term.var (ρ i)))
              (hfFormulaAt (hfUpVarMap ρ) a)) := by
        simpa [subst_instTerm_var_hfFormulaAt] using iha ρ
      have hmain := Prov.P_eqElim _ (Term.var (ρ i)) (Term.var (ρ j))
        (hfFormulaAt (hfUpVarMap ρ) a) (iheq ρ) hbody
      simpa [subst_instTerm_var_hfFormulaAt] using hmain

theorem BProv_hfFormulaAt_of_BProv_HF {G : List Form} {phi : Form}
    (h : SetTheory.BProv AckermannHF.HFAx_s G phi) :
    ∀ ρ : Nat → Nat,
      BProv translatedHFAx (hfContextAt ρ G) (hfFormulaAt ρ phi) := by
  rcases h with ⟨L, hL, hprov⟩
  intro ρ
  refine ⟨hfContextAt ρ L, ?_, ?_⟩
  · intro f hf
    simp only [hfContextAt, List.mem_map] at hf
    rcases hf with ⟨g, hg, rfl⟩
    have hgAx : AckermannHF.HFAx_s g := hL g hg
    rw [hfFormulaAt_eq_translateHFFormula_of_HF_sentence g ρ
      (AckermannHF.Sentences_HF g hgAx)]
    exact translatedHFAx_intro hgAx
  · have hp := Prov_hfFormulaAt_of_Prov hprov ρ
    simpa [hfContextAt, List.map_append] using hp

theorem BProv_translateHFFormula_of_BProv_HF {phi : Form}
    (h : SetTheory.BProv AckermannHF.HFAx_s [] phi) :
    BProv translatedHFAx [] (translateHFFormula phi) := by
  have htranslated :=
    BProv_hfFormulaAt_of_BProv_HF h (fun n : Nat => n)
  simpa [hfContextAt, translateHFFormula] using htranslated

theorem BProv_hfFormulaAt_of_BProv_HFFin {G : List Form} {phi : Form}
    (h : SetTheory.BProv AckermannHF.HFFinAx_s G phi) :
    ∀ ρ : Nat → Nat,
      BProv translatedHFFinAx (hfContextAt ρ G) (hfFormulaAt ρ phi) := by
  rcases h with ⟨L, hL, hprov⟩
  intro ρ
  refine ⟨hfContextAt ρ L, ?_, ?_⟩
  · intro f hf
    simp only [hfContextAt, List.mem_map] at hf
    rcases hf with ⟨g, hg, rfl⟩
    have hgAx : AckermannHF.HFFinAx_s g := hL g hg
    rw [hfFormulaAt_eq_translateHFFormula_of_HF_sentence g ρ
      (AckermannHF.Sentences_HFFin g hgAx)]
    exact translatedHFFinAx_intro hgAx
  · have hp := Prov_hfFormulaAt_of_Prov hprov ρ
    simpa [hfContextAt, List.map_append] using hp

theorem BProv_translateHFFormula_of_BProv_HFFin {phi : Form}
    (h : SetTheory.BProv AckermannHF.HFFinAx_s [] phi) :
    BProv translatedHFFinAx [] (translateHFFormula phi) := by
  have htranslated :=
    BProv_hfFormulaAt_of_BProv_HFFin h (fun n : Nat => n)
  simpa [hfContextAt, translateHFFormula] using htranslated

end Formula

namespace Formula

def substZero : Nat → Term
  | 0 => Term.zero
  | n+1 => Term.var n

theorem substZero_eq_instTerm :
    substZero = instTerm Term.zero := by
  funext n
  cases n <;> rfl

def substZeroAt (p : Nat) : Nat → Term :=
  fun n => if n < p then Term.var n else if n = p then Term.zero else Term.var (n - 1)

@[simp] theorem substZeroAt_lt {p n : Nat} (h : n < p) :
    substZeroAt p n = Term.var n := by
  simp [substZeroAt, h]

@[simp] theorem substZeroAt_eq {p : Nat} :
    substZeroAt p p = Term.zero := by
  simp [substZeroAt]

theorem substZeroAt_gt {p n : Nat} (h : p < n) :
    substZeroAt p n = Term.var (n - 1) := by
  have hnlt : ¬ n < p := by omega
  have hne : n ≠ p := by omega
  simp [substZeroAt, hnlt, hne]

@[simp] theorem substZeroAt_zero :
    substZeroAt 0 = substZero := by
  funext n
  cases n <;> simp [substZeroAt, substZero]

theorem upSubst_substZeroAt (p : Nat) :
    Term.upSubst (substZeroAt p) = substZeroAt (p+1) := by
  funext n
  cases n with
  | zero =>
      simp [Term.upSubst, substZeroAt]
  | succ n =>
      by_cases hlt : n < p
      · have hslt : n + 1 < p + 1 := by omega
        rw [Term.upSubst, substZeroAt_lt hlt, substZeroAt_lt hslt]
        rfl
      · by_cases heq : n = p
        · subst n
          rw [Term.upSubst, substZeroAt_eq, substZeroAt_eq]
          rfl
        · have hgt : p < n := by omega
          have hsgt : p + 1 < n + 1 := by omega
          rw [Term.upSubst, substZeroAt_gt hgt, substZeroAt_gt hsgt]
          simp [Term.rename]
          omega

/-- Substitute PA variable `p` by the term `t`, shifting the free variables of
`t` through the `p` surrounding binders and closing the de Bruijn gap above
`p`.  The case `p = 0` is ordinary `instTerm t`. -/
def substTermAt (p : Nat) (t : Term) : Nat → Term :=
  fun n =>
    if n < p then Term.var n
    else if n = p then Term.rename (fun m => m + p) t
    else Term.var (n - 1)

@[simp] theorem substTermAt_lt {p n : Nat} {t : Term} (h : n < p) :
    substTermAt p t n = Term.var n := by
  simp [substTermAt, h]

@[simp] theorem substTermAt_eq {p : Nat} {t : Term} :
    substTermAt p t p = Term.rename (fun m => m + p) t := by
  simp [substTermAt]

theorem substTermAt_gt {p n : Nat} {t : Term} (h : p < n) :
    substTermAt p t n = Term.var (n - 1) := by
  have hnlt : ¬ n < p := by omega
  have hne : n ≠ p := by omega
  simp [substTermAt, hnlt, hne]

@[simp] theorem substTermAt_zero (t : Term) :
    substTermAt 0 t = instTerm t := by
  have hrename : Term.rename (fun m => m) t = t := by
    induction t with
    | var n => rfl
    | zero => rfl
    | succ t ih => simp [Term.rename, ih]
    | add a b iha ihb => simp [Term.rename, iha, ihb]
    | mul a b iha ihb => simp [Term.rename, iha, ihb]
  funext n
  cases n with
  | zero =>
      simp [substTermAt, instTerm, hrename]
  | succ n =>
      simp [substTermAt, instTerm]

theorem upSubst_substTermAt (p : Nat) (t : Term) :
    Term.upSubst (substTermAt p t) = substTermAt (p+1) t := by
  funext n
  cases n with
  | zero =>
      simp [Term.upSubst, substTermAt]
  | succ n =>
      by_cases hlt : n < p
      · have hslt : n + 1 < p + 1 := by omega
        rw [Term.upSubst, substTermAt_lt hlt, substTermAt_lt hslt]
        rfl
      · by_cases heq : n = p
        · subst n
          rw [Term.upSubst, substTermAt_eq, substTermAt_eq]
          rw [Term.rename_comp]
          exact Term.rename_ext t _ _ (fun m => by omega)
        · have hgt : p < n := by omega
          have hsgt : p + 1 < n + 1 := by omega
          rw [Term.upSubst, substTermAt_gt hgt, substTermAt_gt hsgt]
          simp [Term.rename]
          omega

def substSuccVar : Nat → Term
  | 0 => Term.succ (Term.var 0)
  | n+1 => Term.var (n+1)

/-- Zero-instantiating the induction variable removes the surrounding shift
from the ambient code and step slots of a shifted-tail existential. -/
theorem substZero_betaShiftTailExistsTermAt_succ
    (oldCode oldStep : Nat) :
    subst substZero
        (betaShiftTailExistsTermAt
          (oldCode+1) (oldStep+1) (Term.var 0)) =
      betaShiftTailExistsTermAt oldCode oldStep Term.zero := by
  simp [betaShiftTailExistsTermAt, betaShiftTailThroughTermAt,
    betaTermTermAt, remTermTermAt, ltTermAt, betaModTermTerm, leTermAt,
    substZero, subst, Term.subst, Term.upSubst, Term.rename, Nat.add_assoc]

/-- Successor-instantiating the induction variable preserves the shifted
ambient slots and replaces the tail bound by its successor. -/
theorem substSuccVar_betaShiftTailExistsTermAt_succ
    (oldCode oldStep : Nat) :
    subst substSuccVar
        (betaShiftTailExistsTermAt
          (oldCode+1) (oldStep+1) (Term.var 0)) =
      betaShiftTailExistsTermAt
        (oldCode+1) (oldStep+1) (Term.succ (Term.var 0)) := by
  simp [betaShiftTailExistsTermAt, betaShiftTailThroughTermAt,
    betaTermTermAt, remTermTermAt, ltTermAt, betaModTermTerm, leTermAt,
    substSuccVar, subst, Term.subst, Term.upSubst, Term.rename, Nat.add_assoc]

def substSuccAt (p : Nat) : Nat → Term :=
  fun n => if n = p then Term.succ (Term.var p) else Term.var n

@[simp] theorem substSuccAt_eq {p : Nat} :
    substSuccAt p p = Term.succ (Term.var p) := by
  simp [substSuccAt]

theorem substSuccAt_ne {p n : Nat} (h : n ≠ p) :
    substSuccAt p n = Term.var n := by
  simp [substSuccAt, h]

@[simp] theorem substSuccAt_zero :
    substSuccAt 0 = substSuccVar := by
  funext n
  cases n <;> simp [substSuccAt, substSuccVar]

theorem upSubst_substSuccAt (p : Nat) :
    Term.upSubst (substSuccAt p) = substSuccAt (p+1) := by
  funext n
  cases n with
  | zero =>
      simp [Term.upSubst, substSuccAt]
  | succ n =>
      by_cases heq : n = p
      · subst n
        rw [Term.upSubst, substSuccAt_eq, substSuccAt_eq]
        rfl
      · have hsne : n + 1 ≠ p + 1 := by omega
        rw [Term.upSubst, substSuccAt_ne heq, substSuccAt_ne hsne]
        rfl

def succInj : Formula :=
  all (all (imp
    (eq (Term.succ (Term.var 1)) (Term.succ (Term.var 0)))
    (eq (Term.var 1) (Term.var 0))))

def zeroNotSucc : Formula :=
  all (imp (eq (Term.succ (Term.var 0)) Term.zero) bot)

def addZero : Formula :=
  all (eq (Term.add (Term.var 0) Term.zero) (Term.var 0))

def addSucc : Formula :=
  all (all (eq
    (Term.add (Term.var 1) (Term.succ (Term.var 0)))
    (Term.succ (Term.add (Term.var 1) (Term.var 0)))))

def mulZero : Formula :=
  all (eq (Term.mul (Term.var 0) Term.zero) Term.zero)

def mulSucc : Formula :=
  all (all (eq
    (Term.mul (Term.var 1) (Term.succ (Term.var 0)))
    (Term.add (Term.mul (Term.var 1) (Term.var 0)) (Term.var 1))))

def inductionForm (phi : Formula) : Formula :=
  imp
    (and (subst substZero phi)
         (all (imp phi (subst substSuccVar phi))))
    (all phi)

/-- Modus ponens form of the PA induction body.

This is not the PA induction axiom itself: callers still have to supply a
proof of `inductionForm phi`, typically by instantiating the sealed PA axiom
schema. -/
theorem BProv_inductionForm_mp {B : Formula → Prop} {G : List Formula}
    {phi : Formula}
    (hind : BProv B G (inductionForm phi))
    (hzero : BProv B G (subst substZero phi))
    (hsucc : BProv B G (all (imp phi (subst substSuccVar phi)))) :
    BProv B G (all phi) := by
  exact BProv_mp B G
    (and (subst substZero phi)
      (all (imp phi (subst substSuccVar phi))))
    (all phi) hind (BProv_andI hzero hsucc)

def Ax (f : Formula) : Prop :=
  f = succInj ∨ f = zeroNotSucc ∨
  f = addZero ∨ f = addSucc ∨
  f = mulZero ∨ f = mulSucc ∨
  ∃ phi, f = inductionForm phi

def Ax_s (f : Formula) : Prop :=
  f = sealPA succInj ∨ f = sealPA zeroNotSucc ∨
  f = sealPA addZero ∨ f = sealPA addSucc ∨
  f = sealPA mulZero ∨ f = sealPA mulSucc ∨
  ∃ phi, f = sealPA (inductionForm phi)

theorem sentence_ax_s {f : Formula} (hf : Ax_s f) : Sentence f := by
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ <;>
    exact sealPA_sentence _

/-- Every sealed PA axiom is a sentence. -/
theorem Ax_s_sentences : Sentences Ax_s := by
  intro f hf
  exact sentence_ax_s hf

/-!
The two structural rules below are used constantly at the PA axiom set, and
both are only available because `Ax_s` consists of sentences.  Naming the
`Ax_s` instances once keeps that side condition from being re-discharged, and
re-read, at several hundred call sites.
-/

/-- Renaming a PA derivation, i.e. `BProv_rename_of_sentences` at `Ax_s`. -/
theorem BProv_Ax_s_rename {G : List Formula} {phi : Formula}
    (h : BProv Ax_s G phi) (r : Nat → Nat) :
    BProv Ax_s (G.map (rename r)) (rename r phi) :=
  BProv_rename_of_sentences (B := Ax_s) Ax_s_sentences h r

/-- Existential elimination for PA, i.e. `BProv_exE_of_sentences` at `Ax_s`. -/
theorem BProv_Ax_s_exE {G : List Formula} {a c : Formula}
    (hex : BProv Ax_s G (ex a))
    (hbody : BProv Ax_s (a :: G.map (rename Nat.succ)) (rename Nat.succ c)) :
    BProv Ax_s G c :=
  BProv_exE_of_sentences (B := Ax_s) Ax_s_sentences hex hbody

/-- Named membership of the sealed successor-injectivity axiom in PA. -/
theorem Ax_s_succInj : Ax_s (sealPA succInj) :=
  Or.inl rfl

/-- Named membership of the sealed zero-is-not-successor axiom in PA. -/
theorem Ax_s_zeroNotSucc : Ax_s (sealPA zeroNotSucc) :=
  Or.inr (Or.inl rfl)

/-- Named membership of the sealed addition-by-zero axiom in PA. -/
theorem Ax_s_addZero : Ax_s (sealPA addZero) :=
  Or.inr (Or.inr (Or.inl rfl))

/-- Named membership of the sealed addition-successor axiom in PA. -/
theorem Ax_s_addSucc : Ax_s (sealPA addSucc) :=
  Or.inr (Or.inr (Or.inr (Or.inl rfl)))

/-- Named membership of the sealed multiplication-by-zero axiom in PA. -/
theorem Ax_s_mulZero : Ax_s (sealPA mulZero) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))

/-- Named membership of the sealed multiplication-successor axiom in PA. -/
theorem Ax_s_mulSucc : Ax_s (sealPA mulSucc) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))

/-- Named membership of a sealed induction instance in PA. -/
theorem Ax_s_induction (phi : Formula) : Ax_s (sealPA (inductionForm phi)) :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨phi, rfl⟩)))))

/-- PA proves every variable-renamed body whose sealed form is one of its
axioms. -/
theorem BProv_Ax_s_of_sealPA_rename {phi : Formula}
    (hphi : Ax_s (sealPA phi)) (r : Nat → Nat) :
    BProv Ax_s [] (rename r phi) :=
  BProv_sealPA_allE_rename phi r (BProv_ax hphi)

/-- PA proves every variable-renamed body of successor injectivity. -/
theorem BProv_Ax_s_succInj_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r succInj) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_succInj r

/-- PA proves successor injectivity. -/
theorem BProv_Ax_s_succInj :
    BProv Ax_s [] succInj := by
  simpa [rename_id] using
    BProv_Ax_s_succInj_rename (fun n : Nat => n)

/-- Arbitrary-term instance of PA successor injectivity. -/
theorem BProv_Ax_s_succInj_terms {G : List Formula} (s t : Term) :
    BProv Ax_s G (imp
      (eq (Term.succ s) (Term.succ t))
      (eq s t)) := by
  apply BProv_weaken_nil
  have h1 := BProv_allE (B := Ax_s) (G := []) (t := s)
    BProv_Ax_s_succInj
  have h2 := BProv_allE (B := Ax_s) (G := []) (t := t) h1
  simpa [succInj, subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using h2

/-- PA proves every variable-renamed body of zero-is-not-successor. -/
theorem BProv_Ax_s_zeroNotSucc_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r zeroNotSucc) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_zeroNotSucc r

/-- PA proves zero-is-not-successor. -/
theorem BProv_Ax_s_zeroNotSucc :
    BProv Ax_s [] zeroNotSucc := by
  simpa [rename_id] using
    BProv_Ax_s_zeroNotSucc_rename (fun n : Nat => n)

/-- Arbitrary-term instance of PA zero-is-not-successor. -/
theorem BProv_Ax_s_zeroNotSucc_term {G : List Formula} (t : Term) :
    BProv Ax_s G (imp (eq (Term.succ t) Term.zero) bot) := by
  apply BProv_weaken_nil
  have h := BProv_allE (B := Ax_s) (G := []) (t := t)
    BProv_Ax_s_zeroNotSucc
  simpa [zeroNotSucc, subst, instTerm, Term.subst] using h

/-- PA proves every variable-renamed body of addition by zero. -/
theorem BProv_Ax_s_addZero_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r addZero) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_addZero r

/-- PA proves addition by zero. -/
theorem BProv_Ax_s_addZero :
    BProv Ax_s [] addZero := by
  simpa [rename_id] using
    BProv_Ax_s_addZero_rename (fun n : Nat => n)

/-- Arbitrary-term instance of PA addition by zero. -/
theorem BProv_Ax_s_addZero_term {G : List Formula} (t : Term) :
    BProv Ax_s G (eq (Term.add t Term.zero) t) := by
  apply BProv_weaken_nil
  have h := BProv_allE (B := Ax_s) (G := []) (t := t)
    BProv_Ax_s_addZero
  simpa [addZero, subst, instTerm, Term.subst] using h

/-- PA proves every variable-renamed body of the addition-successor axiom. -/
theorem BProv_Ax_s_addSucc_rename (r : Nat → Nat) :
    BProv Ax_s [] (rename r addSucc) :=
  BProv_Ax_s_of_sealPA_rename Ax_s_addSucc r

/-- PA proves the addition-successor axiom. -/
theorem BProv_Ax_s_addSucc :
    BProv Ax_s [] addSucc := by
  simpa [rename_id] using
    BProv_Ax_s_addSucc_rename (fun n : Nat => n)

/-- Arbitrary-term instance of the PA addition-successor axiom. -/
theorem BProv_Ax_s_addSucc_terms {G : List Formula} (s t : Term) :
    BProv Ax_s G (eq
      (Term.add s (Term.succ t))
      (Term.succ (Term.add s t))) := by
  apply BProv_weaken_nil
  have h1 := BProv_allE (B := Ax_s) (G := []) (t := s)
    BProv_Ax_s_addSucc
  have h2 := BProv_allE (B := Ax_s) (G := []) (t := t) h1
  simpa [addSucc, subst, instTerm, Term.subst, Term.upSubst,
    term_subst_instTerm_rename_succ] using h2

/-- PA proves the left-zero law for addition. -/
theorem BProv_Ax_s_zero_add_all {G : List Formula} :
    BProv Ax_s G
      (all (eq (Term.add Term.zero (Term.var 0)) (Term.var 0))) := by
  apply BProv_weaken_nil
  let phi : Formula := eq (Term.add Term.zero (Term.var 0)) (Term.var 0)
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, substZero, subst, instTerm, Term.subst, Term.upSubst,
      Term.numeral] using BProv_Ax_s_addZero_term Term.zero
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    have hphi : BProv Ax_s [phi]
        (eq (Term.add Term.zero (Term.var 0)) (Term.var 0)) :=
      BProv_ass (B := Ax_s) (G := [phi]) (by simp [phi])
    have hstep : BProv Ax_s [phi]
        (eq (Term.add Term.zero (Term.succ (Term.var 0)))
          (Term.succ (Term.add Term.zero (Term.var 0)))) :=
      (BProv_Ax_s_addSucc_terms Term.zero (Term.var 0))
    have hsucc : BProv Ax_s [phi]
        (eq (Term.succ (Term.add Term.zero (Term.var 0)))
          (Term.succ (Term.var 0))) :=
      BProv_eq_congr_succ hphi
    have htarget : BProv Ax_s [phi]
        (eq (Term.add Term.zero (Term.succ (Term.var 0)))
          (Term.succ (Term.var 0))) :=
      BProv_eqTrans hstep hsucc
    simpa [phi, substSuccVar, subst, instTerm, Term.subst, Term.upSubst,
      Term.rename] using htarget
  have hsuccImp : BProv Ax_s [] (imp phi (subst substSuccVar phi)) :=
    BProv_impI hsuccBody
  have hsucc : BProv Ax_s []
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences (B := Ax_s)
      Ax_s_sentences hsuccImp
  have hind : BProv Ax_s [] (inductionForm phi) := by
    simpa [rename_id] using
      BProv_Ax_s_of_sealPA_rename (Ax_s_induction phi) (fun n : Nat => n)
  simpa [phi] using BProv_inductionForm_mp hind hzero hsucc

/-- Arbitrary-term instance of the PA left-zero law for addition. -/
theorem BProv_Ax_s_zero_add_term {G : List Formula} (t : Term) :
    BProv Ax_s G (eq (Term.add Term.zero t) t) := by
  have hall : BProv Ax_s G
      (all (eq (Term.add Term.zero (Term.var 0)) (Term.var 0))) :=
    BProv_Ax_s_zero_add_all
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := t) hall
  simpa [subst, instTerm, Term.subst, Term.upSubst] using hinst

/-- PA proves that every number is either zero or the successor of a
predecessor. -/
theorem BProv_Ax_s_zeroOrSuccPredAt_all {G : List Formula} :
    BProv Ax_s G (all (zeroOrSuccPredAt 0)) := by
  apply BProv_weaken_nil
  let phi : Formula := zeroOrSuccPredAt 0
  have hzeroLeft : BProv Ax_s [] (subst substZero (zeroAt 0)) := by
    simpa [zeroAt, eqConstAt, substZero, subst, instTerm, Term.subst,
      Term.upSubst, Term.numeral] using
      (BProv_eqRefl (B := Ax_s) (G := []) Term.zero)
  have hzero : BProv Ax_s [] (subst substZero phi) := by
    simpa [phi, zeroOrSuccPredAt, subst] using
      (BProv_orI1 (B := Ax_s) (G := [])
        (b := subst substZero (succPredAt 0)) hzeroLeft)
  have hsuccBody : BProv Ax_s [phi] (subst substSuccVar phi) := by
    have hrefl : BProv Ax_s [phi]
        (eq (Term.succ (Term.var 0)) (Term.succ (Term.var 0))) :=
      BProv_eqRefl (B := Ax_s) (G := [phi])
        (Term.succ (Term.var 0))
    have hinst : BProv Ax_s [phi]
        (subst (instTerm (Term.var 0))
          (eq (Term.succ (Term.var 1)) (Term.succ (Term.var 0)))) := by
      simpa [subst, instTerm, Term.subst] using hrefl
    have hright : BProv Ax_s [phi] (subst substSuccVar (succPredAt 0)) := by
      simpa [succPredAt, subst, substSuccVar, Term.subst, Term.upSubst,
        Term.rename]
        using
          (BProv_exI (B := Ax_s) (G := [phi])
            (a := eq (Term.succ (Term.var 1)) (Term.succ (Term.var 0)))
            (t := Term.var 0) hinst)
    simpa [phi, zeroOrSuccPredAt, subst] using
      (BProv_orI2 (B := Ax_s) (G := [phi])
        (a := subst substSuccVar (zeroAt 0)) hright)
  have hsuccImp : BProv Ax_s [] (imp phi (subst substSuccVar phi)) :=
    BProv_impI hsuccBody
  have hsucc : BProv Ax_s []
      (all (imp phi (subst substSuccVar phi))) :=
    BProv_allI_of_sentences (B := Ax_s)
      Ax_s_sentences hsuccImp
  have hind : BProv Ax_s [] (inductionForm phi) := by
    simpa [rename_id] using
      BProv_Ax_s_of_sealPA_rename (Ax_s_induction phi) (fun n : Nat => n)
  simpa [phi] using BProv_inductionForm_mp hind hzero hsucc

/-- Arbitrary-term instance of the PA zero-or-successor predecessor split. -/
theorem BProv_Ax_s_zeroOrSuccPred_term {G : List Formula} (t : Term) :
    BProv Ax_s G
      (or (eq t Term.zero)
        (ex (eq (Term.rename Nat.succ t) (Term.succ (Term.var 0))))) := by
  have hall : BProv Ax_s G (all (zeroOrSuccPredAt 0)) :=
    BProv_Ax_s_zeroOrSuccPredAt_all
  have hinst := BProv_allE (B := Ax_s) (G := G) (t := t) hall
  simpa [zeroOrSuccPredAt, zeroAt, succPredAt, eqConstAt, subst,
    instTerm, Term.subst, Term.upSubst, Term.numeral,
    term_subst_instTerm_rename_succ]
    using hinst

/-- Slot-level zero-or-successor predecessor split. -/
theorem BProv_Ax_s_zeroOrSuccPredAt {G : List Formula} (a : Nat) :
    BProv Ax_s G (zeroOrSuccPredAt a) := by
  simpa [zeroOrSuccPredAt, zeroAt, succPredAt, eqConstAt, Term.rename,
    Term.numeral]
    using (BProv_Ax_s_zeroOrSuccPred_term (G := G) (Term.var a))

/-- Eliminate a positive-witness formula by opening its predecessor witness.

The opened body uses the orientation built into `nonzeroAt`:
`S pred = a`.  This keeps later predecessor-sensitive proofs from having to
open the existential by hand. -/
theorem BProv_nonzeroAt_elim
    {B : Formula → Prop} (hB : Sentences B) {G : List Formula}
    {target : Formula} {a : Nat}
    (hnonzero : BProv B G (nonzeroAt a))
    (hbody : BProv B
      (eq (Term.succ (Term.var 0)) (Term.var (a+1)) ::
        G.map (rename Nat.succ))
      (rename Nat.succ target)) :
    BProv B G target := by
  let body : Formula := eq (Term.succ (Term.var 0)) (Term.var (a+1))
  have hex : BProv B G (ex body) := by
    simpa [nonzeroAt, body] using hnonzero
  exact BProv_exE_of_sentences (B := B) hB (a := body)
    (c := target) hex (by simpa [body] using hbody)

/-- A successor-predecessor witness is the same positive-witness fact as
`nonzeroAt`, with the equality reversed.  This lemma keeps the orientation
change as proof plumbing rather than baking it into either macro. -/
theorem BProv_nonzeroAt_of_succPredAt
    {B : Formula → Prop} (hB : Sentences B) {G : List Formula} {a : Nat}
    (hsucc : BProv B G (succPredAt a)) :
    BProv B G (nonzeroAt a) := by
  let succBody : Formula := eq (Term.var (a+1)) (Term.succ (Term.var 0))
  let nzBody : Formula := eq (Term.succ (Term.var 0)) (Term.var (a+2))
  have hbody : BProv B (succBody :: G.map (rename Nat.succ))
      (rename Nat.succ (nonzeroAt a)) := by
    let C : List Formula := succBody :: G.map (rename Nat.succ)
    have hsuccBody : BProv B C succBody :=
      BProv_ass (B := B) (G := C) (by simp [C, succBody])
    have hsym : BProv B C
        (eq (Term.succ (Term.var 0)) (Term.var (a+1))) :=
      BProv_eqSym hsuccBody
    have hinst : BProv B C (subst (instTerm (Term.var 0)) nzBody) := by
      simpa [nzBody, subst, instTerm, Term.subst, Term.upSubst]
        using hsym
    have hnonzero : BProv B C (ex nzBody) :=
      BProv_exI (B := B) (G := C) (a := nzBody)
        (t := Term.var 0) hinst
    simpa [C, nonzeroAt, nzBody, rename, Term.rename, SetTheory.up]
      using hnonzero
  exact BProv_exE_of_sentences (B := B) hB (a := succBody)
    (c := nonzeroAt a)
    (by simpa [succPredAt, succBody] using hsucc)
    (by simpa [succBody] using hbody)

/-- Zero-substitution removes one surrounding binder from a shifted term. -/
theorem term_substZero_rename_succ (t : Term) :
    Term.subst substZero (Term.rename Nat.succ t) = t := by
  rw [substZero_eq_instTerm]
  exact term_subst_instTerm_rename_succ t Term.zero

/-- Successor-substitution leaves a term shifted through the induction binder. -/
theorem term_substSuccVar_rename_succ (t : Term) :
    Term.subst substSuccVar (Term.rename Nat.succ t) =
      Term.rename Nat.succ t := by
  rw [Term.subst_rename]
  simpa [substSuccVar] using term_subst_var_rename t Nat.succ

end Formula

end PA

end SetTheory
