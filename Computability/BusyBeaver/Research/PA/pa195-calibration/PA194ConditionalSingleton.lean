import PA194InternalEmpty
import PA194ConditionalSingletonLogic
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194ConditionalSingleton
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194InternalSingleton PA194InternalEmpty PA194ConditionalSingletonLogic
open DiophantineConsistency
section model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def Bit {n : Nat} (x s : Bootstrapping.Semiterm V ℒₒᵣ n) : Bootstrapping.Semiformula V ℒₒᵣ n :=
  (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).subst ![x,s]

noncomputable def singletonBody (a : V) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 2) ≐ Bootstrapping.Semiterm.fvar a))
noncomputable def emptyBody : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ ∼(Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1))
noncomputable def desiredBody (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ((P.subst ![Bootstrapping.Semiterm.fvar a]).subst ![] 🡒
    Bit (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.bvar 0)) ⋏
  (∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒
    P.subst ![Bootstrapping.Semiterm.bvar 0]))

lemma singleton_case (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ (P.subst ![Bootstrapping.Semiterm.fvar a]) 🡒 ∃⁰ desiredBody a P := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let Pa : Bootstrapping.Formula V ℒₒᵣ := P.subst ![Bootstrapping.Semiterm.fvar a]
  let S := singletonBody (V := V) a
  let W := desiredBody a P
  change T ⊢ Pa 🡒 ∃⁰ W
  apply Nonempty.intro
  apply FiniteContext.deduct'
  have hs : [Pa] ⊢[T]! ∃⁰ S := by
    apply FiniteContext.of
    simpa [S,singletonBody,Bit] using (internal_PA_singleton_explicit a).some
  have himp : [Pa] ⊢[T]! ∃⁰ S 🡒 ∃⁰ W := by
    apply TProof.exsImpExs
    have hbase := from_singleton P.shift
      ((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).shift) (a+1) 0
    have hb : T ⊢ Pa.shift 🡒 S.free 🡒 W.free := by
      simpa [S,W,Pa,singletonBody,desiredBody,Bit, Bootstrapping.Semiformula.free,
        Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
        SemitermVec.q, Matrix.vecHead, Matrix.vecTail] using hbase
    have hp : [Pa.shift] ⊢[T]! Pa.shift := FiniteContext.byAxm (by simp)
    exact FiniteContext.of hb.some ⨀ hp
  exact himp ⨀ hs
lemma empty_exists : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∃⁰ (emptyBody (V := V)) := by
  apply TProof.exs! (Bootstrapping.Arithmetic.typedNumeral 0)
  simpa [emptyBody,Bit,Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using
    (internal_PA_empty_explicit (V := V))

lemma empty_case (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∼(P.subst ![Bootstrapping.Semiterm.fvar a]) 🡒 ∃⁰ desiredBody a P := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let Pa : Bootstrapping.Formula V ℒₒᵣ := P.subst ![Bootstrapping.Semiterm.fvar a]
  let S := emptyBody (V := V)
  let W := desiredBody a P
  change T ⊢ ∼Pa 🡒 ∃⁰ W
  apply Nonempty.intro
  apply FiniteContext.deduct'
  have hs : [∼Pa] ⊢[T]! ∃⁰ S := FiniteContext.of (empty_exists (V := V)).some
  have himp : [∼Pa] ⊢[T]! ∃⁰ S 🡒 ∃⁰ W := by
    apply TProof.exsImpExs
    have hbase := from_empty P.shift
      ((⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).shift) (a+1) 0
    have hb : T ⊢ (∼Pa).shift 🡒 S.free 🡒 W.free := by
      simpa [S,W,Pa,emptyBody,desiredBody,Bit, Bootstrapping.Semiformula.free,
        Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
        SemitermVec.q, Matrix.vecHead, Matrix.vecTail] using hbase
    have hp : [(∼Pa).shift] ⊢[T]! (∼Pa).shift := FiniteContext.byAxm (by simp)
    exact FiniteContext.of hb.some ⨀ hp
  exact himp ⨀ hs

lemma conditional_singleton (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∃⁰ desiredBody a P := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let Pa : Bootstrapping.Formula V ℒₒᵣ := P.subst ![Bootstrapping.Semiterm.fvar a]
  have hp : T ⊢ Pa 🡒 ∃⁰ desiredBody a P := singleton_case a P
  have hn : T ⊢ ∼Pa 🡒 ∃⁰ desiredBody a P := empty_case a P
  exact ⟨of_C_of_C_of_A hp.some hn.some lem⟩

#print axioms conditional_singleton
#print axioms empty_case
#print axioms singleton_case
end model
end PA194ConditionalSingleton
