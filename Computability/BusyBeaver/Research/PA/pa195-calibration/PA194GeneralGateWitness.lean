import PA194SeparationWitness
import PA194GateWitnessBody
import PA194GateInsertPoint
import PA194ConditionalInsert
import PA194ComprehensionExs
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194GeneralGateWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationWitness PA194GateWitnessBody PA194GateInsertPoint PA194ConditionalInsert PA194ConditionalSingleton PA194ComprehensionExs PA194ComprehensionShift
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def relConj {n : Nat} (A B D : Bootstrapping.Semiformula V ℒₒᵣ n) := (A 🡒 B 🡒 D) 🡒 D
noncomputable def witnessBody (a b : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (D : Bootstrapping.Semiformula V ℒₒᵣ 2) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  (((P.subst ![Bootstrapping.Semiterm.fvar b]).subst ![]) 🡒
    Bit (Bootstrapping.Semiterm.fvar b) (Bootstrapping.Semiterm.bvar 0)) ⋏
  (∀⁰ (relConj
    (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) 🡒
      P.subst ![Bootstrapping.Semiterm.bvar 0] 🡒 Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1))
    (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡒 P.subst ![Bootstrapping.Semiterm.bvar 0]) D))

theorem witness (a b : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1)
    (D : Bootstrapping.Semiformula V ℒₒᵣ 2) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∃⁰ witnessBody a b P D := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let S := sepBody a P
  let W := witnessBody a b P D
  have hs : T ⊢ ∃⁰ S := internal_separation a P
  have houter : T ⊢ (∃⁰ S) 🡒 ∃⁰ W := by
    apply PA194ComprehensionExs.exs_elim S (∃⁰ W)
    apply Nonempty.intro
    apply FiniteContext.deduct'
    let A : Bootstrapping.Formula V ℒₒᵣ := P.shift.subst ![Bootstrapping.Semiterm.fvar (b+1)]
    let I := desiredBody (0 : V) (b+1) A
    have hi : [S.free] ⊢[T]! ∃⁰ I := FiniteContext.of (conditional_insert (0 : V) (b+1) A).some
    have hinner : [S.free] ⊢[T]! (∃⁰ I) 🡒 ∃⁰ W.shift := by
      apply TProof.exsImpExs
      simp only [List.map_cons,List.map_nil]
      apply FiniteContext.deduct
      have hI : [I.free,S.free.shift] ⊢[T]! I.free := FiniteContext.byAxm (by simp)
      have hS : [I.free,S.free.shift] ⊢[T]! S.free.shift := FiniteContext.byAxm (by simp)
      let P' := P.shift.shift
      let A' : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar (1 : V))
      let B' : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar (a+1+1))
      let C' : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar (0 : V))
      let E' : Bootstrapping.Semiformula V ℒₒᵣ 1 := (Bootstrapping.Semiterm.bvar 0 : Bootstrapping.Semiterm V ℒₒᵣ 1) ≐ Bootstrapping.Semiterm.fvar (b+1+1)
      let Q' : Bootstrapping.Semiformula V ℒₒᵣ 1 := (P'.subst ![Bootstrapping.Semiterm.fvar (b+1+1)]).subst ![]
      let U1 := ∀⁰ (A' 🡘 (B' ⋏ P'))
      let U2 := ∀⁰ (C' 🡘 (A' ⋎ (Q' ⋏ E')))
      have hI' : [I.free,S.free.shift] ⊢[T]! U2 := by
        simpa [U2,A',C',Q',P',E',I,A,PA194ConditionalInsert.desiredBody,PA194ConditionalSingleton.Bit,
          Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
          Bootstrapping.Semiformula.substs_substs,bit_shift,SemitermVec.q,Matrix.vecHead,Matrix.vecTail,add_assoc] using hI
      have hS' : [I.free,S.free.shift] ⊢[T]! U1 := by
        simpa [U1,A',B',P',S,sepBody,PA194ConditionalSingleton.Bit,
          Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
          Bootstrapping.Semiformula.substs_substs,bit_shift,SemitermVec.q,Matrix.vecHead,Matrix.vecTail,add_assoc] using hS
      simp only [W,witnessBody,Bootstrapping.Semiformula.free, Bootstrapping.Semiformula.shift_and, Bootstrapping.Semiformula.substs_and]
      apply K_intro
      · have h : [I.free,S.free.shift] ⊢[T]! U2 🡒 A.shift 🡒 Bit (Bootstrapping.Semiterm.fvar (b+1+1)) (Bootstrapping.Semiterm.fvar (0 : V)) := by
          apply FiniteContext.of
          simpa [U2,A',C',Q',P',E',A,Bootstrapping.Semiformula.shift_substs,
            Bootstrapping.Semiformula.substs_substs,bit_shift,SemitermVec.q,Matrix.vecHead,Matrix.vecTail,add_assoc] using
            (insertion_point A.shift (b+1+1) (1 : V) 0).some
        have hp := h ⨀ hI'
        simpa [W,A,witnessBody,PA194ConditionalSingleton.Bit,Bootstrapping.Semiformula.free,
          Bootstrapping.Semiformula.shift_substs,Bootstrapping.Semiformula.substs_substs,
          bit_shift,SemitermVec.q,Matrix.vecHead,Matrix.vecTail,add_assoc] using hp
      · let D' : Bootstrapping.Semiformula V ℒₒᵣ 1 := D.shift.shift.subst (SemitermVec.q ![Bootstrapping.Semiterm.fvar 0])
        let Z := ∀⁰ (((B' 🡒 P' 🡒 C') 🡒 (C' 🡒 P') 🡒 D') 🡒 D')
        have h : [I.free,S.free.shift] ⊢[T]! U1 🡒 U2 🡒 Z := by
          apply FiniteContext.of
          simpa [U1,U2,Z,A',B',C',P',Q',E',D'] using
            (gate_body P.shift.shift D' (a+1+1) (b+1+1) (1 : V) 0).some
        have hp := h ⨀ hS' ⨀ hI'
        simpa [W,witnessBody,PA194ConditionalSingleton.Bit,D',Z,B',C',P',relConj,
          Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
          Bootstrapping.Semiformula.substs_substs,bit_shift,SemitermVec.q,Matrix.vecHead,Matrix.vecTail,add_assoc] using hp
    have h := hinner ⨀ hi
    simpa using h
  exact ⟨houter.some ⨀ hs.some⟩
#print axioms witness
end PA194GeneralGateWitness
