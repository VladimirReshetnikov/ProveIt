import PA194ComprehensionExs
import PA194ComprehensionShift
import PA194ConditionalInsert
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace PA194ComprehensionWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ConditionalSingleton PA194ConditionalInsert PA194ComprehensionStep PA194ComprehensionShift PA194ComprehensionExs
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def OldBody (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (Lt (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋏ P.subst ![Bootstrapping.Semiterm.bvar 0]))
noncomputable def NextBody (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (Lt (Bootstrapping.Semiterm.bvar 0) (Succ (Bootstrapping.Semiterm.fvar a)) ⋏ P.subst ![Bootstrapping.Semiterm.bvar 0]))

theorem witness_step (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (∃⁰ OldBody a P) 🡒 ∃⁰ NextBody a P := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let O := OldBody a P
  let N := NextBody a P
  change T ⊢ (∃⁰ O) 🡒 ∃⁰ N
  apply exs_elim O (∃⁰ N)
  apply Nonempty.intro
  apply FiniteContext.deduct'
  let A : Bootstrapping.Formula V ℒₒᵣ := P.shift.subst ![Bootstrapping.Semiterm.fvar (a+1)]
  let I := PA194ConditionalInsert.desiredBody (0 : V) (a+1) A
  have hins : [O.free] ⊢[T]! ∃⁰ I := FiniteContext.of (conditional_insert (0 : V) (a+1) A).some
  have himp : [O.free] ⊢[T]! (∃⁰ I) 🡒 ∃⁰ N.shift := by
    apply TProof.exsImpExs
    simp only [List.map_cons,List.map_nil]
    apply FiniteContext.deduct
    have hi : [I.free,O.free.shift] ⊢[T]! I.free := FiniteContext.byAxm (by simp)
    have ho : [I.free,O.free.shift] ⊢[T]! O.free.shift := FiniteContext.byAxm (by simp)
    have hs := (step_body P.shift.shift (a+1+1) (1 : V) 0).some
    have hstep : [I.free,O.free.shift] ⊢[T]! O.free.shift 🡒 I.free 🡒 N.shift.free := by
      apply FiniteContext.of
      simpa [O,N,I,A,OldBody,NextBody,PA194ConditionalInsert.desiredBody,
        PA194ConditionalSingleton.Bit,Lt,Succ,Bootstrapping.Semiformula.free,
        Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
        Bootstrapping.Semiterm.shift_substs,Bootstrapping.Semiterm.substs_substs,
        bit_shift,lt_shift,succ_shift,SemitermVec.q,Matrix.vecHead,Matrix.vecTail,
        add_assoc] using hs
    exact hstep ⨀ ho ⨀ hi
  have h := himp ⨀ hins
  simpa using h
#print axioms witness_step
end PA194ComprehensionWitness
