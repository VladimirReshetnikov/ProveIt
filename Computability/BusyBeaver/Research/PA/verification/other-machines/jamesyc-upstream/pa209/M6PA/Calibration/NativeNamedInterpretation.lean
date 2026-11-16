module
public import M6.Logic.NativeNamed
public import M6PA.Theory
@[expose] public section
namespace M6.PA.NativeCalculus
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
def bindEnv {n : Nat} (env : Nat → ArithmeticSemiterm Empty n) (a : Nat) :
    Nat → ArithmeticSemiterm Empty (n+1) :=
  fun v => if v = a then #0 else Rew.bShift (env v)

def Named.interpret (R E : ArithmeticSemisentence 2) :
    Named → {n : Nat} → (Nat → ArithmeticSemiterm Empty n) → ArithmeticSemisentence n
  | .truth, _, _ => ⊥ 🡒 ⊥
  | .imp p q, _, env => p.interpret R E env 🡒 q.interpret R E env
  | .neg p, _, env => ∼ p.interpret R E env
  | .mem a b, _, env => R/[env a,env b]
  | .eq a b, _, env => E/[env a,env b]
  | .all a p, _, env => ∀¹ p.interpret R E (bindEnv env a)

/-- Named semantics: quantifiers update exactly their bound label. -/
theorem Named.interpret_correct {V : Type*} [ORingStructure V]
    (R E : ArithmeticSemisentence 2) (p : Named) {n : Nat}
    (env : Nat → ArithmeticSemiterm Empty n) (b : Fin n → V) :
    (V ⊧/b (p.interpret R E env)) ↔
      p.eval (fun x y => V ⊧/![x,y] R) (fun x y => V ⊧/![x,y] E)
        (fun v => Semiterm.val b Empty.elim (env v)) := by
  induction p generalizing n with
  | truth => simp [interpret,eval]
  | imp p q ihp ihq => simp [interpret,eval,ihp,ihq]
  | neg p ih => simp [interpret,eval,ih]
  | mem a c => simp [interpret,eval]
  | eq a c => simp [interpret,eval]
  | all a p ih =>
    simp only [interpret,Semiformula.eval_all,eval]
    apply forall_congr'
    intro x
    rw [ih]
    apply iff_of_eq
    congr 1
    funext v
    by_cases hv : v = a <;> simp [bindEnv,hv]

theorem pa_proves_namedRho2 (R E : ArithmeticSemisentence 2)
    (env : Nat → ArithmeticSemiterm Empty 0) (a : Nat) (p q : Named) :
    theory ⊢ (namedRho2 a p q).interpret R E env := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp [namedRho2,Named.interpret,models_iff]
  intro hpq hp v
  exact hpq v (hp v)

#print axioms Named.interpret_correct
#print axioms namedRho2_encode
#print axioms pa_proves_namedRho2
end M6.PA.NativeCalculus

