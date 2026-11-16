module
public import PA196.Logic.Decode
@[expose] public section

/-! A concrete external model of the PA196 command calculus.
Hereditarily finite lists suffice: no extensionality axiom occurs among the
machine's heads. Equality is Lean equality and membership is list membership.
Arbitrary pointed separation is proved by finite filtering. This module is
independent of the later arithmetization in PA.
-/
namespace PA196.Logic

inductive HF where
  | node (children : List HF)

instance : Inhabited HF := ⟨.node []⟩

def HF.children : HF → List HF
  | .node xs => xs

def HF.mem (a b : HF) : Prop := b ∈ a.children

theorem HF.mem_size {a b : HF} (h : a.mem b) : sizeOf b < sizeOf a := by
  cases a with
  | node xs =>
    have hb := List.sizeOf_lt_of_mem (show b ∈ xs from h)
    simp only [HF.node.sizeOf_spec]
    omega

theorem HF.not_self (a : HF) : ¬ a.mem a := by
  intro h
  have hh := HF.mem_size h
  omega

/-- A genuine finite object represents every selected subcollection and
includes the distinguished point whenever the property holds there. -/
theorem HF.pointedSeparation (p : HF → Prop) (a b : HF) :
    ∃ s : HF, (∀ x, (a.mem x → p x → s.mem x) ∧ (s.mem x → p x)) ∧
      (p b → s.mem b) := by
  classical
  let s := HF.node ((b :: a.children).filter (fun x => decide (p x)))
  have hs (x : HF) : s.mem x ↔ (x = b ∨ a.mem x) ∧ p x := by
    simp [s,HF.mem,HF.children]
  refine ⟨s,fun x => ⟨?_,?_⟩,?_⟩
  · intro h hp
    exact (hs x).mpr ⟨Or.inr h,hp⟩
  · intro h
    exact ((hs x).mp h).2
  · intro hp
    exact (hs b).mpr ⟨Or.inl rfl,hp⟩

def assign {V : Type u} (env : Nat → V) (a : Nat) (x : V) : Nat → V :=
  fun v => if v = a then x else env v

@[simp] theorem assign_same {V : Type u} (env : Nat → V) (a : Nat) (x : V) :
    assign env a x a = x := by simp [assign]

@[simp] theorem assign_ne {V : Type u} (env : Nat → V) {a b : Nat}
    (h : b ≠ a) (x : V) : assign env a x b = env b := by simp [assign,h]

@[simp] theorem assign_restore {V : Type u} (env : Nat → V) (a : Nat) :
    assign env a (env a) = env := by
  funext v
  by_cases hv : v = a <;> simp [assign,hv]

@[simp] theorem assign_overwrite {V : Type u} (env : Nat → V) (a : Nat) (x y : V) :
    assign (assign env a x) a y = assign env a y := by
  funext v
  by_cases hv : v = a <;> simp [assign,hv]

theorem assign_comm {V : Type u} (env : Nat → V) {a b : Nat} (ha : a ≠ b) (x y : V) :
    assign (assign env a x) b y = assign (assign env b y) a x := by
  funext v
  by_cases h1 : v = a <;> by_cases h2 : v = b <;> simp_all [assign]

def evalCode (n : Nat) (env : Nat → HF) : Prop :=
  (NumericDecode.decode n).eval HF.mem env

theorem evalCode_zero (env : Nat → HF) : evalCode 0 env := by trivial

theorem evalCode_one (env : Nat → HF) : ¬ evalCode 1 env := HF.not_self (env 0)

theorem evalCode_imp (a b : Nat) (env : Nat → HF) :
    evalCode (wim a b) env ↔ (evalCode a env → evalCode b env) := by
  by_cases hz : a+b = 0
  · have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    subst a; subst b
    have hw : wim 0 0 = 0 := rfl
    simp only [hw,evalCode_zero env,implies_true,iff_self]
  · rw [evalCode,NumericDecode.decode_imp a b (by omega)]
    rfl

theorem evalCode_all (a b : Nat) (env : Nat → HF) :
    evalCode (wal a b) env ↔ ∀ x, evalCode b (assign env a x) := by
  simp only [evalCode,NumericDecode.decode_all,Named.eval]
  rfl

theorem evalCode_mem (a b : Nat) (env : Nat → HF) :
    evalCode (wel a b) env ↔ (env a).mem (env b) := by
  simp only [evalCode,NumericDecode.decode_mem,Named.eval]

theorem evalCode_eq (a b : Nat) (env : Nat → HF) :
    evalCode (weq a b) env ↔ env a = env b := by
  simp only [evalCode,NumericDecode.decode_eq,Named.eval]

theorem evalCode_neg (a : Nat) (env : Nat → HF) :
    evalCode (wn a) env ↔ ¬ evalCode a env := by
  simp only [wn,evalCode_imp,evalCode_one,imp_false]

theorem evalCode_and (a b : Nat) (env : Nat → HF) :
    evalCode (wa a b) env ↔ evalCode a env ∧ evalCode b env := by
  classical
  simp [wa,evalCode_neg,evalCode_imp]

theorem evalCode_ex (a b : Nat) (env : Nat → HF) :
    evalCode (wex a b) env ↔ ∃ x, evalCode b (assign env a x) := by
  classical
  simp [wex,evalCode_neg,evalCode_all]

theorem evalCode_fresh (c : Nat) (env : Nat → HF) (x : HF) :
    evalCode c (assign env c x) ↔ evalCode c env := by
  have hf : (NumericDecode.decode c).free c = false := by
    cases h : (NumericDecode.decode c).free c with
    | false => rfl
    | true =>
      have hn := (NumericDecode.decode c).free_in_names c h
      rw [NumericDecode.self_fresh] at hn
      contradiction
  exact ((NumericDecode.decode c).eval_fresh _ env c x hf).symm

#print axioms HF.pointedSeparation
#print axioms evalCode_fresh
end PA196.Logic
