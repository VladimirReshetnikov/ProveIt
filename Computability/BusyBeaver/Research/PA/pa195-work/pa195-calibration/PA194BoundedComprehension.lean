import PA194ComprehensionBase
import PA194ComprehensionWitness
import PA194InternalInductionRule
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace PA194BoundedComprehension
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ConditionalSingleton PA194ComprehensionStep PA194ComprehensionShift PA194ComprehensionBase PA194ComprehensionWitness
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem induction_step (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∀⁰ ((predicate P) 🡒
      (predicate P).subst ![⌜(‘#0 + 1’ : ArithmeticSemiterm Nat 1)⌝]) := by
  apply Nonempty.intro
  apply FiniteContext.emptyPrf
  apply TProof.generalize
  simp only [List.map_nil]
  apply FiniteContext.of
  have h := (witness_step (0 : V) P.shift).some
  simpa [predicate,OldBody,NextBody,PA194ConditionalSingleton.Bit,Lt,Succ,
    Bootstrapping.Semiformula.free,Bootstrapping.Semiformula.shift_substs,
    Bootstrapping.Semiformula.substs_substs,Bootstrapping.Semiterm.shift_substs,
    Bootstrapping.Semiterm.substs_substs,bit_shift,lt_shift,succ_shift,
    SemitermVec.q,Matrix.vecHead,Matrix.vecTail] using h

theorem bounded_comprehension (P : Bootstrapping.Semiformula V ℒₒᵣ 1) :
    (𝗣𝗔 : ArithmeticTheory).internalize V ⊢ ∀⁰ predicate P := by
  exact PA194InternalInductionRule.induction_rule (predicate P) (induction_base P) (induction_step P)
#print axioms induction_step
#print axioms bounded_comprehension
end PA194BoundedComprehension
