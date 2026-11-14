import PA194ConditionalInsertLift
import PA194ConditionalSingleton
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace PA194ConditionalInsert
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194InternalBitInsert PA194ConditionalInsertLift PA194ConditionalSingleton
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def insertBody (a b : V) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋎
      ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 2) ≐ Bootstrapping.Semiterm.fvar b)))
noncomputable def desiredBody (a b : V) (A : Bootstrapping.Formula V ℒₒᵣ) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋎
      ((A.subst ![]) ⋏ ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 2) ≐ Bootstrapping.Semiterm.fvar b))))
lemma positive_case (a b : V) (A : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ A 🡒 ∃⁰ desiredBody a b A := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let S := insertBody (V := V) a b
  let W := desiredBody a b A
  change T ⊢ A 🡒 ∃⁰ W
  apply Nonempty.intro
  apply FiniteContext.deduct'
  have hs : [A] ⊢[T]! ∃⁰ S := by
    apply FiniteContext.of
    simpa [S,insertBody,PA194ConditionalSingleton.Bit] using (internal_PA_insert_explicit a b).some
  have himp : [A] ⊢[T]! ∃⁰ S 🡒 ∃⁰ W := by
    apply TProof.exsImpExs
    let B : Bootstrapping.Semiformula V ℒₒᵣ 1 := (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).shift.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar (a+1)]
    let C : Bootstrapping.Semiformula V ℒₒᵣ 1 := (⌜(Rew.emb ▹ bitDef.val : ArithmeticSemiformula Nat 2)⌝ : Bootstrapping.Semiformula V ℒₒᵣ 2).shift.subst ![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar 0]
    let E : Bootstrapping.Semiformula V ℒₒᵣ 1 := ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar (b+1))
    have hbase := positive_all A.shift B C E
    have hb : T ⊢ A.shift 🡒 S.free 🡒 W.free := by
      simpa [B,C,E,S,W,insertBody,desiredBody,PA194ConditionalSingleton.Bit, Bootstrapping.Semiformula.free,
        Bootstrapping.Semiformula.shift_substs, Bootstrapping.Semiformula.substs_substs,
        SemitermVec.q, Matrix.vecHead, Matrix.vecTail] using hbase
    have hp : [A.shift] ⊢[T]! A.shift := FiniteContext.byAxm (by simp)
    exact FiniteContext.of hb.some ⨀ hp
  exact himp ⨀ hs
noncomputable def exsWithCtxAux {C : Bootstrapping.Formula V ℒₒᵣ}
    {φ : Bootstrapping.Semiformula V ℒₒᵣ 1} (t : Bootstrapping.Term V ℒₒᵣ)
    (d : (𝗣𝗔 : ArithmeticTheory).internalize V ⊢! C 🡒 φ.subst ![t]) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢! C 🡒 ∃⁰ φ := by
  rw [Bootstrapping.Semiformula.imp_def] at d ⊢
  apply TDerivation.or
  apply TDerivation.rotate₁
  apply TDerivation.exs t
  exact TDerivation.rotate₁ (TDerivation.orInv d)
noncomputable def exsWithCtx {Γ : List (Bootstrapping.Formula V ℒₒᵣ)}
    {φ : Bootstrapping.Semiformula V ℒₒᵣ 1} (t : Bootstrapping.Term V ℒₒᵣ)
    (d : Γ ⊢[(𝗣𝗔 : ArithmeticTheory).internalize V]! φ.subst ![t]) :
    Γ ⊢[(𝗣𝗔 : ArithmeticTheory).internalize V]! ∃⁰ φ := exsWithCtxAux t d
lemma negative_case (a b : V) (A : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∼A 🡒 ∃⁰ desiredBody a b A := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let B : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a)
  let E : Bootstrapping.Semiformula V ℒₒᵣ 1 := ((Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar b)
  have hid : T ⊢ ∀⁰ (B 🡘 B) := by
    apply Nonempty.intro
    apply FiniteContext.emptyPrf
    apply TProof.generalize
    simp only [List.map_nil]
    have ht : [] ⊢[T]! B.free 🡒 B.free := C_id
    simpa [Bootstrapping.Semiformula.free] using E_intro ht ht
  have hbase := negative_all A B B E
  have hbody : T ⊢ ∼A 🡒 ∀⁰ (B 🡘 (B ⋎ ((A.subst ![]) ⋏ E))) := by
    exact ⟨C_swap hbase.some ⨀ hid.some⟩
  apply Nonempty.intro
  apply FiniteContext.deduct'
  have hh : [∼A] ⊢[T]! ∀⁰ (B 🡘 (B ⋎ ((A.subst ![]) ⋏ E))) := FiniteContext.of hbody.some ⨀ (FiniteContext.byAxm (by simp))
  have hsub : [∼A] ⊢[T]! (desiredBody a b A).subst ![Bootstrapping.Semiterm.fvar a] := by
    simpa [B,E,desiredBody,PA194ConditionalSingleton.Bit, Bootstrapping.Semiformula.substs_substs,
      SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using hh
  exact exsWithCtx (Bootstrapping.Semiterm.fvar a) hsub
lemma conditional_insert (a b : V) (A : Bootstrapping.Formula V ℒₒᵣ) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∃⁰ desiredBody a b A := by
  classical
  exact ⟨of_C_of_C_of_A (positive_case a b A).some (negative_case a b A).some lem⟩
#print axioms positive_case
#print axioms negative_case
#print axioms conditional_insert
end PA194ConditionalInsert
