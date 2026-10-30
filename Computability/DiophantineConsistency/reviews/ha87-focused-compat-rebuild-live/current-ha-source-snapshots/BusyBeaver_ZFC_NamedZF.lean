import ZF.Zf

/-!
Named first-order formulas over `Form`, and named Separation and Replacement
in models of the `ZFAxioms` bundle.

Internal set theory in an arbitrary model needs a formula for every set it
carves out by Separation or Replacement. Written directly in De Bruijn form
those formulas are hard to read and to get right. `NForm` uses *named*
variables, evaluated in an environment updated at the bound name, and
`toForm` translates into `Form` (each binder moves its name to slot 0 and
shifts the other names, as in `NamedForm254`); `sat_toForm` is the semantic
correctness of the translation, with no freshness assumption. An `atom`
embeds an arbitrary De Bruijn formula, reading its slot `i` at name `args i`;
it is how a given matrix (for instance a GIC instance) enters a named
formula. `sepN` and
`replN` then state Separation and Replacement for named formulas: the
separated variable is name `0`, and for Replacement the output is name `0`
and the input name `1`; all other names are parameters read from the
environment.
-/

namespace SetTheory.BusyBeaver.ZFC.NamedZF

open Form

/-! ## Named formulas -/

inductive NForm where
  | mem (x y : Nat)
  | eq (x y : Nat)
  | bot
  | imp (a b : NForm)
  | and (a b : NForm)
  | or (a b : NForm)
  | all (x : Nat) (a : NForm)
  | ex (x : Nat) (a : NForm)
  /-- A De Bruijn formula whose slot `i` is read at name `args i`. -/
  | atom (φ : Form) (args : Nat → Nat)

universe u
variable {V : Type u}

/-- Update a named environment. -/
def upd (ρ : Nat → V) (x : Nat) (d : V) : Nat → V := fun i => if i = x then d else ρ i

@[simp] theorem upd_same (ρ : Nat → V) (x : Nat) (d : V) : upd ρ x d x = d := by simp [upd]

theorem upd_other (ρ : Nat → V) {x i : Nat} (d : V) (h : i ≠ x) : upd ρ x d i = ρ i := by
  simp [upd, h]

def NSat (mem : V → V → Prop) : (Nat → V) → NForm → Prop
  | ρ, .mem x y => mem (ρ x) (ρ y)
  | ρ, .eq x y => ρ x = ρ y
  | _, .bot => False
  | ρ, .imp a b => NSat mem ρ a → NSat mem ρ b
  | ρ, .and a b => NSat mem ρ a ∧ NSat mem ρ b
  | ρ, .or a b => NSat mem ρ a ∨ NSat mem ρ b
  | ρ, .all x a => ∀ d, NSat mem (upd ρ x d) a
  | ρ, .ex x a => ∃ d, NSat mem (upd ρ x d) a
  | ρ, .atom φ args => Sat mem (fun i => ρ (args i)) φ

/-! ## Translation into De Bruijn formulas -/

def under (slots : Nat → Nat) (x : Nat) (i : Nat) : Nat := if i = x then 0 else slots i + 1

def toForm (slots : Nat → Nat) : NForm → Form
  | .mem x y => fMem (slots x) (slots y)
  | .eq x y => fEq (slots x) (slots y)
  | .bot => fBot
  | .imp a b => fImp (toForm slots a) (toForm slots b)
  | .and a b => fAnd (toForm slots a) (toForm slots b)
  | .or a b => fOr (toForm slots a) (toForm slots b)
  | .all x a => fAll (toForm (under slots x) a)
  | .ex x a => fEx (toForm (under slots x) a)
  | .atom φ args => rename (fun i => slots (args i)) φ

theorem under_env (slots : Nat → Nat) (x : Nat) (env : Nat → V) (d : V) :
    (fun i => scons d env (under slots x i)) = upd (fun i => env (slots i)) x d := by
  funext i
  by_cases h : i = x <;> simp [under, upd, h, scons]

theorem sat_toForm (mem : V → V → Prop) :
    ∀ (φ : NForm) (slots : Nat → Nat) (env : Nat → V),
      Sat mem env (toForm slots φ) ↔ NSat mem (fun i => env (slots i)) φ
  | .mem _ _, _, _ => Iff.rfl
  | .eq _ _, _, _ => Iff.rfl
  | .bot, _, _ => Iff.rfl
  | .imp a b, slots, env | .and a b, slots, env | .or a b, slots, env => by
      simp only [toForm, Sat, NSat, sat_toForm mem a slots env, sat_toForm mem b slots env]
  | .all x a, slots, env => by
      simp only [toForm, Sat, NSat]
      exact forall_congr' fun d => by rw [sat_toForm mem a, under_env]
  | .ex x a, slots, env => by
      simp only [toForm, Sat, NSat]
      exact exists_congr fun d => by rw [sat_toForm mem a, under_env]
  | .atom φ args, slots, env => by
      simp only [toForm, NSat]
      exact Sat_rename φ _ env

/-! ## Derived connectives -/

def NForm.neg (a : NForm) : NForm := .imp a .bot
def NForm.iff (a b : NForm) : NForm := .and (.imp a b) (.imp b a)

@[simp] theorem nsat_neg (mem : V → V → Prop) (ρ : Nat → V) (a : NForm) :
    NSat mem ρ a.neg ↔ ¬ NSat mem ρ a := Iff.rfl

@[simp] theorem nsat_iff (mem : V → V → Prop) (ρ : Nat → V) (a b : NForm) :
    NSat mem ρ (a.iff b) ↔ (NSat mem ρ a ↔ NSat mem ρ b) :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

/-! ## Named Separation and Replacement -/

section ZF

variable {mem : V → V → Prop}

theorem scons_shift (x : V) (ρ : Nat → V) :
    (fun i => scons x (fun i => ρ (i + 1)) (id i)) = upd ρ 0 x := by
  funext i; cases i <;> simp [scons, upd]

theorem scons_shift2 (y x : V) (ρ : Nat → V) :
    (fun i => scons y (scons x (fun i => ρ (i + 2))) (id i)) = upd (upd ρ 1 x) 0 y := by
  funext i
  rcases i with _ | _ | i <;> simp [scons, upd]

/-- Separation by a named formula: name `0` is the separated variable. -/
theorem sepN (H : ZFAxioms mem) (φ : NForm) (ρ : Nat → V) (a : V) :
    ∃ s, ∀ x, mem x s ↔ mem x a ∧ NSat mem (upd ρ 0 x) φ := by
  obtain ⟨s, hs⟩ := H.sep (toForm id φ) (fun i => ρ (i + 1)) a
  exact ⟨s, fun x => by rw [hs x, sat_toForm, scons_shift]⟩

/-- Separation for any predicate that a named formula defines. -/
theorem sep_of (H : ZFAxioms mem) (P : V → Prop) (φ : NForm) (ρ : Nat → V)
    (hP : ∀ x, NSat mem (upd ρ 0 x) φ ↔ P x) (a : V) :
    ∃ s, ∀ x, mem x s ↔ mem x a ∧ P x := by
  obtain ⟨s, hs⟩ := sepN H φ ρ a
  exact ⟨s, fun x => by rw [hs x, hP x]⟩

/-- Replacement by a named formula: name `0` is the output, name `1` the input. -/
theorem replN (H : ZFAxioms mem) (φ : NForm) (ρ : Nat → V)
    (hF : ∀ x y1 y2, NSat mem (upd (upd ρ 1 x) 0 y1) φ → NSat mem (upd (upd ρ 1 x) 0 y2) φ →
      y1 = y2) (a : V) :
    ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ NSat mem (upd (upd ρ 1 x) 0 y) φ := by
  have hfun : Functional (relOf mem (toForm id φ) (fun i => ρ (i + 2))) := fun x y1 y2 h1 h2 => by
    simp only [relOf, sat_toForm, scons_shift2] at h1 h2
    exact hF x y1 y2 h1 h2
  obtain ⟨r, hr⟩ := H.repl (toForm id φ) (fun i => ρ (i + 2)) hfun a
  exact ⟨r, fun y => by rw [hr y]; simp only [relOf, sat_toForm, scons_shift2]⟩

/-- Replacement for any functional relation that a named formula defines. -/
theorem repl_of (H : ZFAxioms mem) (R : V → V → Prop) (φ : NForm) (ρ : Nat → V)
    (hR : ∀ x y, NSat mem (upd (upd ρ 1 x) 0 y) φ ↔ R x y)
    (hF : ∀ x y1 y2, R x y1 → R x y2 → y1 = y2) (a : V) :
    ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ R x y := by
  obtain ⟨r, hr⟩ := replN H φ ρ (fun x y1 y2 h1 h2 => hF x y1 y2 ((hR x y1).1 h1) ((hR x y2).1 h2)) a
  exact ⟨r, fun y => by rw [hr y]; simp only [hR]⟩

end ZF

end SetTheory.BusyBeaver.ZFC.NamedZF
