module
public import M6.Logic.NativeNames
public import M6PA.HFSComprehension
@[expose] public section

/-! Concrete arithmetic HFS interpretation for native named and numeric syntax.
The model is an arbitrary PA model, including nonstandard elements. -/
namespace M6.PA.NativeHFS
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open NativeCalculus

def bindEnv {n} (env : Nat → ArithmeticSemiterm Nat n) (a : Nat) :
    Nat → ArithmeticSemiterm Nat (n+1) :=
  fun v => if v = a then #0 else Rew.bShift (env v)

def formula : Named → {n : Nat} → (Nat → ArithmeticSemiterm Nat n) → ArithmeticSemiformula Nat n
  | .truth, _, _ => ⊥ 🡒 ⊥
  | .imp p q, _, env => formula p env 🡒 formula q env
  | .neg p, _, env => ∼ formula p env
  | .mem a b, _, env => bitDef.val.emb/[env b,env a]
  | .eq a b, _, env => “!!(env a) = !!(env b)”
  | .all a p, _, env => ∀¹ formula p (bindEnv env a)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

def eval (p : Named) (env : Nat → V) : Prop :=
  p.eval (fun a b => b ∈ a) Eq env

theorem formula_correct (p : Named) {n} (env : Nat → ArithmeticSemiterm Nat n)
    (b : Fin n → V) (params : Nat → V) :
    (formula p env).Eval b params ↔ eval p (fun v => Semiterm.val b params (env v)) := by
  induction p generalizing n with
  | truth => simp [formula,eval,Named.eval]
  | imp p q ihp ihq => simp [formula,eval,Named.eval,ihp,ihq]
  | neg p ih => simp [formula,eval,Named.eval,ih]
  | mem a c => simp [formula,eval,Named.eval]
  | eq a c => simp [formula,eval,Named.eval]
  | all a p ih =>
    simp only [formula,Semiformula.eval_all,eval,Named.eval]
    apply forall_congr'
    intro x
    rw [ih]
    apply iff_of_eq
    congr 1
    funext v
    by_cases hv : v = a <;> simp [bindEnv,hv]

def assign (env : Nat → V) (a : Nat) (x : V) : Nat → V :=
  fun v => if v = a then x else env v

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] in
theorem assign_comm (env : Nat → V) {a b : Nat} (ha : a ≠ b) (x y : V) :
    assign (assign env a x) b y = assign (assign env b y) a x := by
  funext v
  by_cases h1 : v = a <;> by_cases h2 : v = b <;> simp_all [assign]

/-- Every named property with one variable opened is represented by an actual
arithmetic formula with the remaining names as explicit free parameters. -/
theorem eval_pointed_separation (p : Named) (env : Nat → V) (name : Nat) (a b : V) :
    ∃ s : V, (∀ x, (x ∈ a → eval p (assign env name x) → x ∈ s) ∧
      (x ∈ s → eval p (assign env name x))) ∧ (eval p (assign env name b) → b ∈ s) := by
  let φ : ArithmeticSemiformula Nat 1 := formula p (fun v => if v = name then #0 else &v)
  have hc (x : V) : φ.Eval ![x] env ↔ eval p (assign env name x) := by
    rw [formula_correct]
    apply iff_of_eq
    congr 1
    funext v
    by_cases hv : v = name <;> simp [assign,hv]
  simpa only [hc] using HFSComprehension.pointed_separation φ env a b

def evalCode (n : Nat) (env : Nat → V) := eval (NumericDecode.decode n) env

theorem evalCode_zero (env : Nat → V) : evalCode 0 env := by
  trivial

theorem evalCode_one (env : Nat → V) : ¬ evalCode 1 env := by
  intro h
  exact Arithmetic.lt_irrefl (env 0) (lt_of_mem h)

theorem evalCode_neg (a : Nat) (env : Nat → V) :
    evalCode (wn a) env ↔ ¬ evalCode a env := by
  simp only [evalCode,NumericDecode.decode_neg,eval,Named.eval]

theorem evalCode_imp (a b : Nat) (env : Nat → V) :
    evalCode (wim a b) env ↔ (evalCode a env → evalCode b env) := by
  by_cases hb : b = 1
  · subst b
    simpa only [show wim a 1 = wn a from rfl,evalCode_one env,imp_false] using evalCode_neg a env
  · by_cases hz : a+b = 0
    · have ha : a = 0 := by omega
      have hb : b = 0 := by omega
      subst a; subst b
      have hw : wim 0 0 = 0 := by unfold wim; rfl
      simp only [hw,evalCode_zero env,implies_true,iff_self]
    · rw [evalCode,NumericDecode.decode_imp a b hb (by omega)]
      rfl

theorem evalCode_all (a b : Nat) (env : Nat → V) :
    evalCode (wal a b) env ↔ ∀ x, evalCode b (assign env a x) := by
  simp only [evalCode,NumericDecode.decode_all,eval,Named.eval]
  rfl

theorem evalCode_mem (a b : Nat) (env : Nat → V) :
    evalCode (wel a b) env ↔ env b ∈ env a := by
  simp only [evalCode,NumericDecode.decode_mem,eval,Named.eval]

theorem evalCode_eq (a b : Nat) (env : Nat → V) :
    evalCode (weq a b) env ↔ env a = env b := by
  simp only [evalCode,NumericDecode.decode_eq,eval,Named.eval]

theorem evalCode_and (a b : Nat) (env : Nat → V) :
    evalCode (wa a b) env ↔ evalCode a env ∧ evalCode b env := by
  simp [wa,evalCode_neg,evalCode_imp]

theorem evalCode_ex (a b : Nat) (env : Nat → V) :
    evalCode (wex a b) env ↔ ∃ x, evalCode b (assign env a x) := by
  simp [wex,evalCode_neg,evalCode_all]

theorem evalCode_fresh (c : Nat) (env : Nat → V) (x : V) :
    evalCode c (assign env c x) ↔ evalCode c env := by
  have hf : (NumericDecode.decode c).free c = false := by
    cases h : (NumericDecode.decode c).free c with
    | false => rfl
    | true =>
      have hn := (NumericDecode.decode c).free_in_names c h
      rw [NumericDecode.self_fresh] at hn
      contradiction
  exact ((NumericDecode.decode c).eval_fresh _ _ env c x hf).symm

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] in
@[simp] theorem assign_same (env : Nat → V) (a : Nat) (x : V) : assign env a x a = x := by
  simp [assign]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] in
@[simp] theorem assign_ne (env : Nat → V) {a b : Nat} (h : b ≠ a) (x : V) :
    assign env a x b = env b := by simp [assign,h]

omit [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] in
@[simp] theorem assign_restore (env : Nat → V) (a : Nat) : assign env a (env a) = env := by
  funext v
  by_cases hv : v = a <;> simp [assign,hv]

/-- Validity of the full unchanged guarded native bundle in any PA model.
The pointed property is the exact decoded numeric formula c. -/
theorem bundle_valid (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) (env : Nat → V) :
    evalCode (bundle a b c) env := by
  simp only [bundle,evalCode_and,evalCode_ex,evalCode_all,evalCode_imp,evalCode_eq,evalCode_mem]
  simp only [assign_same,assign_ne env ha.symm,assign_ne env hb.symm]
  simp only [assign_comm env hb,evalCode_fresh]
  simp only [assign_same,assign_ne (assign env b _) ha.symm]
  simp only [forall_const,imp_self,and_true]
  have hp := eval_pointed_separation (NumericDecode.decode c) env b (env a) (env b)
  rcases hp with ⟨s,hs,hpoint⟩
  refine ⟨s,fun x => ⟨?_,(hs x).2⟩,?_⟩
  · intro hx hprop
    by_cases hab : a = b
    · subst a
      have hself : x ∈ x := by simpa using hx
      exact False.elim (Arithmetic.lt_irrefl x (lt_of_mem hself))
    · have hxa : x ∈ env a := by simpa [assign,hab] using hx
      exact (hs x).1 hxa hprop
  · simpa only [assign_restore,evalCode] using hpoint

def codeFormula (n : Nat) : ArithmeticProposition :=
  formula (NumericDecode.decode n) (fun v => &v)

theorem codeFormula_correct (n : Nat) (env : Nat → V) :
    (codeFormula n).Eval ![] env ↔ evalCode n env := by
  simp [codeFormula,formula_correct,evalCode]

/-- Actual object-PA derivation of the complete guarded native bundle under
its concrete HFS interpretation, including both unchanged vacuity conjuncts. -/
theorem pa_proves_guardedBundle (a b c : Nat) (ha : c ≠ a) (hb : c ≠ b) :
    theory ⊢ (codeFormula (bundle a b c)).univCl := by
  apply Arithmetic.complete.{0} theory _
  intro W _ _
  simp only [models_iff,Semiformula.eval_univCl]
  intro env
  exact (codeFormula_correct _ env).mpr (bundle_valid a b c ha hb env)

#print axioms pa_proves_guardedBundle
#print axioms bundle_valid
#print axioms formula_correct
#print axioms eval_pointed_separation
#print axioms evalCode_fresh
end M6.PA.NativeHFS

