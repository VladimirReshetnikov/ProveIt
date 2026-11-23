import Lean

/-!
# Propositional syntax and a natural-deduction reference kernel

Status: compiler-unverified proof candidate. No Lean executable was available
in the production environment. No `sorry`, `axiom`, `admit`, `Classical`, or
noncomputable definition is used below.

The theorems in this module are metatheorems in Lean. They are not, merely by
being Lean theorems, derivations of their natural-number encodings in iPRA.
`ObjectExamples.lean` exhibits the separate object-logic interface, and the
formalization plan lists the remaining arithmetization obligations.
-/

namespace IPRAProp

inductive Formula where
  | bot : Formula
  | var : Nat → Formula
  | and : Formula → Formula → Formula
  | or : Formula → Formula → Formula
  | imp : Formula → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

def neg (a : Formula) : Formula := .imp a .bot

def top : Formula := .imp .bot .bot

def eval (v : Nat → Bool) : Formula → Bool
  | .bot => false
  | .var i => v i
  | .and a b => eval v a && eval v b
  | .or a b => eval v a || eval v b
  | .imp a b => !(eval v a) || eval v b

def denote (v : Nat → Prop) : Formula → Prop
  | .bot => False
  | .var i => v i
  | .and a b => denote v a ∧ denote v b
  | .or a b => denote v a ∨ denote v b
  | .imp a b => denote v a → denote v b

def subst (s : Nat → Formula) : Formula → Formula
  | .bot => .bot
  | .var i => s i
  | .and a b => .and (subst s a) (subst s b)
  | .or a b => .or (subst s a) (subst s b)
  | .imp a b => .imp (subst s a) (subst s b)

def size : Formula → Nat
  | .bot => 1
  | .var _ => 1
  | .and a b | .or a b | .imp a b => 1 + size a + size b

/-- Atom occurrences, with repetition. Deduplicate before counting support. -/
def atomOccurrences : Formula → List Nat
  | .bot => []
  | .var i => [i]
  | .and a b | .or a b | .imp a b => atomOccurrences a ++ atomOccurrences b

theorem subst_id (a : Formula) : subst Formula.var a = a := by
  induction a <;> simp_all [subst]

theorem subst_comp (s t : Nat → Formula) (a : Formula) :
    subst t (subst s a) = subst (fun i => subst t (s i)) a := by
  induction a <;> simp_all [subst]

theorem eval_subst (v : Nat → Bool) (s : Nat → Formula) (a : Formula) :
    eval v (subst s a) = eval (fun i => eval v (s i)) a := by
  induction a <;> simp_all [subst, eval]

theorem denote_subst (v : Nat → Prop) (s : Nat → Formula) (a : Formula) :
    denote v (subst s a) = denote (fun i => denote v (s i)) a := by
  induction a <;> simp_all [subst, denote]

/-- A constructive decision procedure for a formula at a Boolean valuation. -/
def decidableDenote (v : Nat → Bool) :
    (a : Formula) → Decidable (denote (fun i => v i = true) a)
  | .bot => inferInstance
  | .var _ => inferInstance
  | .and a b =>
      letI := decidableDenote v a
      letI := decidableDenote v b
      inferInstance
  | .or a b =>
      letI := decidableDenote v a
      letI := decidableDenote v b
      inferInstance
  | .imp a b =>
      letI := decidableDenote v a
      letI := decidableDenote v b
      inferInstance

end Formula

/-- The propositional natural-deduction calculus. `c = true` enables LEM.
This is a datatype of derivations, not yet a numerical proof checker. -/
inductive ND (c : Bool) : List Formula → Formula → Type where
  | hyp {g a} : a ∈ g → ND c g a
  | botE {g a} : ND c g .bot → ND c g a
  | andI {g a b} : ND c g a → ND c g b → ND c g (.and a b)
  | andL {g a b} : ND c g (.and a b) → ND c g a
  | andR {g a b} : ND c g (.and a b) → ND c g b
  | orL {g a b} : ND c g a → ND c g (.or a b)
  | orR {g a b} : ND c g b → ND c g (.or a b)
  | orE {g a b d} : ND c g (.or a b) →
      ND c (a :: g) d → ND c (b :: g) d → ND c g d
  | impI {g a b} : ND c (a :: g) b → ND c g (.imp a b)
  | impE {g a b} : ND c g (.imp a b) → ND c g a → ND c g b
  | lem {g a} : c = true → ND c g (.or a (Formula.neg a))

def ContextHolds (v : Nat → Prop) (g : List Formula) : Prop :=
  ∀ a, a ∈ g → Formula.denote v a

theorem context_cons {v : Nat → Prop} {g : List Formula} {a : Formula}
    (ha : Formula.denote v a) (hg : ContextHolds v g) :
    ContextHolds v (a :: g) := by
  intro b hb
  cases List.mem_cons.mp hb with
  | inl h => cases h; exact ha
  | inr h => exact hg b h

/-- Soundness under a valuation. The LEM condition is requested only when
`c = true`; IPC imposes no excluded-middle assumption on the interpretation. -/
theorem ND.sound {c : Bool} {g : List Formula} {a : Formula}
    (d : ND c g a) (v : Nat → Prop)
    (em : c = true → ∀ b, Formula.denote v b ∨ ¬ Formula.denote v b) :
    ContextHolds v g → Formula.denote v a := by
  induction d with
  | hyp h =>
      intro hg
      exact hg _ h
  | botE _ ih =>
      intro hg
      exact False.elim (ih hg)
  | andI _ _ iha ihb =>
      intro hg
      exact ⟨iha hg, ihb hg⟩
  | andL _ ih =>
      intro hg
      exact (ih hg).1
  | andR _ ih =>
      intro hg
      exact (ih hg).2
  | orL _ ih =>
      intro hg
      exact Or.inl (ih hg)
  | orR _ ih =>
      intro hg
      exact Or.inr (ih hg)
  | orE _ _ _ ih iha ihb =>
      intro hg
      cases ih hg with
      | inl ha => exact iha (context_cons ha hg)
      | inr hb => exact ihb (context_cons hb hg)
  | impI _ ih =>
      intro hg ha
      exact ih (context_cons ha hg)
  | impE _ _ iha ihb =>
      intro hg
      exact iha hg (ihb hg)
  | lem h =>
      intro _
      exact em h _

/-- IPC soundness for arbitrary proposition-valued assignments. -/
theorem ND.ipc_sound {g : List Formula} {a : Formula}
    (d : ND false g a) (v : Nat → Prop) :
    ContextHolds v g → Formula.denote v a :=
  d.sound v (by
    intro h
    cases h)

/-- CPC soundness for Boolean assignments, using only decidable cases. -/
theorem ND.cpc_sound {g : List Formula} {a : Formula}
    (d : ND true g a) (v : Nat → Bool) :
    ContextHolds (fun i => v i = true) g →
      Formula.denote (fun i => v i = true) a :=
  d.sound (fun i => v i = true) (fun _ b => by
    cases Formula.decidableDenote v b with
    | isTrue h => exact Or.inl h
    | isFalse h => exact Or.inr h)

/-- A direct proof object; the context is discharged by implication introduction. -/
def identity (a : Formula) : ND false [] (.imp a a) :=
  .impI (.hyp List.mem_cons_self)

/-- A direct IPC proof of conjunction commutativity. -/
def andComm (a b : Formula) : ND false [] (.imp (.and a b) (.and b a)) :=
  .impI (.andI (.andR (.hyp List.mem_cons_self))
    (.andL (.hyp List.mem_cons_self)))

end IPRAProp
