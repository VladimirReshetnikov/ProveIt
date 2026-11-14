import PA194ConditionalSingletonLogic
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194ComprehensionEquality
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem equality_point (P : Bootstrapping.Semiformula V ℒₒᵣ 1) (a : V) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∀⁰
      (((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar a) 🡒
        (P 🡘 ((P.subst ![Bootstrapping.Semiterm.fvar a]).subst ![]))) := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let W : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
      ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar a) 🡒
        (P 🡘 ((P.subst ![Bootstrapping.Semiterm.fvar a]).subst ![]))
  change T ⊢ ∀⁰ W
  apply Nonempty.intro
  apply FiniteContext.emptyPrf
  apply TProof.generalize
  simp only [List.map_nil]
  have hforward : [] ⊢[T]! ((Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar (a+1)) 🡒
      (P.shift.subst ![Bootstrapping.Semiterm.fvar 0]) 🡒 (P.shift.subst ![Bootstrapping.Semiterm.fvar (a+1)]) :=
    FiniteContext.of (Bootstrapping.Arithmetic.replace (𝗣𝗔 : ArithmeticTheory) P.shift (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar (a+1))).some
  have hsym : [] ⊢[T]! ((Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar (a+1)) 🡒
      ((Bootstrapping.Semiterm.fvar (a+1) : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar 0) :=
    FiniteContext.of (Bootstrapping.Arithmetic.eq_symm (𝗣𝗔 : ArithmeticTheory) (Bootstrapping.Semiterm.fvar 0) (Bootstrapping.Semiterm.fvar (a+1))).some
  have hreverse : [] ⊢[T]! ((Bootstrapping.Semiterm.fvar (a+1) : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar 0) 🡒
      (P.shift.subst ![Bootstrapping.Semiterm.fvar (a+1)]) 🡒 (P.shift.subst ![Bootstrapping.Semiterm.fvar 0]) :=
    FiniteContext.of (Bootstrapping.Arithmetic.replace (𝗣𝗔 : ArithmeticTheory) P.shift (Bootstrapping.Semiterm.fvar (a+1)) (Bootstrapping.Semiterm.fvar 0)).some
  have hboth : [] ⊢[T]! ((Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar (a+1)) 🡒
      ((P.shift.subst ![Bootstrapping.Semiterm.fvar 0]) 🡘 (P.shift.subst ![Bootstrapping.Semiterm.fvar (a+1)])) := by
    apply FiniteContext.deduct
    have he : [((Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar (a+1))] ⊢[T]! ((Bootstrapping.Semiterm.fvar 0 : Bootstrapping.Term V ℒₒᵣ) ≐ Bootstrapping.Semiterm.fvar (a+1)) := FiniteContext.byAxm (by simp)
    have hf := (FiniteContext.weakening (by simp) hforward) ⨀ he
    have hr := (FiniteContext.weakening (by simp) (C_trans hsym hreverse)) ⨀ he
    exact E_intro hf hr
  simpa [W,Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using hboth
#print axioms equality_point
end PA194ComprehensionEquality
