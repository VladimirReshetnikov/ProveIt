import PA194SeparationBody
import PA194BoundedComprehension
import PA194ComprehensionExs
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194SeparationWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194SeparationBody PA194ConditionalSingleton PA194ComprehensionStep PA194ComprehensionShift PA194ComprehensionBase PA194ComprehensionWitness
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def sepBody (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) : Bootstrapping.Semiformula V ℒₒᵣ 1 :=
  ∀⁰ (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1) 🡘
    (Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋏ P.subst ![Bootstrapping.Semiterm.bvar 0]))

theorem internal_separation (a : V) (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∃⁰ sepBody a P := by
  classical
  let T := (𝗣𝗔 : ArithmeticTheory).internalize V
  let Q : Bootstrapping.Semiformula V ℒₒᵣ 1 := Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a) ⋏ P
  let O := OldBody a Q
  let S := sepBody a P
  have hc : T ⊢ ∃⁰ O := by
    have hs := TProof.specialize! (PA194BoundedComprehension.bounded_comprehension Q) (Bootstrapping.Semiterm.fvar a)
    simpa [O,OldBody,predicate,PA194ConditionalSingleton.Bit,Lt,
      Bootstrapping.Semiformula.substs_substs,SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using hs
  have himp : T ⊢ (∃⁰ O) 🡒 ∃⁰ S := by
    apply Nonempty.intro
    apply FiniteContext.emptyPrf
    apply TProof.exsImpExs
    simp only [List.map_nil]
    have h := (separation_body P.shift (a+1) (0 : V)).some
    apply FiniteContext.of
    simpa [O,S,Q,OldBody,sepBody,PA194ConditionalSingleton.Bit,Lt,
      Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
      Bootstrapping.Semiformula.substs_substs,Bootstrapping.Semiterm.shift_substs,
      Bootstrapping.Semiterm.substs_substs,bit_shift,lt_shift,SemitermVec.q,
      Matrix.vecHead,Matrix.vecTail] using h
  exact ⟨himp.some ⨀ hc.some⟩
#print axioms internal_separation
end PA194SeparationWitness
