import PA194PAeqFiniteTransferred
import PA194PAeqAddExtInternal
import PA194PAeqMulExtInternal
import PA194PAeqAddRightZeroInternal
import PA194PAeqMulRightZeroInternal
import PA194PAeqMulRightOneInternal
import PA194PAeqPAExceptFinite
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

def remainingFiniteNext : List ArithmeticSentence :=
 [Theory.Eq.relExt Language.ORing.Rel.eq, Theory.Eq.relExt Language.ORing.Rel.lt,
  PeanoMinus.Axiom.addAssoc, PeanoMinus.Axiom.addComm,
  PeanoMinus.Axiom.addEqOfLt, PeanoMinus.Axiom.zeroLe, PeanoMinus.Axiom.oneLeOfZeroLt,
  PeanoMinus.Axiom.addLtAdd,
  PeanoMinus.Axiom.mulAssoc, PeanoMinus.Axiom.mulComm, PeanoMinus.Axiom.mulLtMul,
  PeanoMinus.Axiom.distr, PeanoMinus.Axiom.ltIrrefl, PeanoMinus.Axiom.ltTrans,
  PeanoMinus.Axiom.ltTri]

theorem finite_cases_next {σ : ArithmeticSentence} (hσ : σ ∈ PeanoMinus) :
    σ = Theory.Eq.refl ℒₒᵣ ∨ σ = Theory.Eq.symm ℒₒᵣ ∨ σ = Theory.Eq.trans ℒₒᵣ ∨
    σ = Theory.Eq.funcExt Language.ORing.Func.zero ∨ σ = Theory.Eq.funcExt Language.ORing.Func.one ∨
    σ = Theory.Eq.funcExt Language.ORing.Func.add ∨ σ = Theory.Eq.funcExt Language.ORing.Func.mul ∨
    σ = PeanoMinus.Axiom.zeroLtOne ∨ σ = PeanoMinus.Axiom.addZero ∨ σ = PeanoMinus.Axiom.mulZero ∨ σ = PeanoMinus.Axiom.mulOne ∨ σ ∈ remainingFiniteNext := by
  cases hσ with
  | equal φ h =>
    cases h with
    | refl => simp
    | symm => simp
    | trans => simp
    | funcExt f => cases f <;> simp [remainingFiniteNext]
    | relExt r => cases r <;> simp [remainingFiniteNext]
  | addZero => simp
  | addAssoc => simp [remainingFiniteNext]
  | addComm => simp [remainingFiniteNext]
  | addEqOfLt => simp [remainingFiniteNext]
  | zeroLe => simp [remainingFiniteNext]
  | zeroLtOne => simp
  | oneLeOfZeroLt => simp [remainingFiniteNext]
  | addLtAdd => simp [remainingFiniteNext]
  | mulZero => simp
  | mulOne => simp
  | mulAssoc => simp [remainingFiniteNext]
  | mulComm => simp [remainingFiniteNext]
  | mulLtMul => simp [remainingFiniteNext]
  | distr => simp [remainingFiniteNext]
  | ltIrrefl => simp [remainingFiniteNext]
  | ltTrans => simp [remainingFiniteNext]
  | ltTri => simp [remainingFiniteNext]

theorem finite_supplier_of_remaining_next
    (hrest : ∀ σ ∈ remainingFiniteNext, Provable ordinaryPAeq (formulaCode 0 (Encodable.encode σ : V))) :
    ∀ σ ∈ PeanoMinus, Provable ordinaryPAeq (formulaCode 0 (Encodable.encode σ : V)) := by
  intro σ hσ
  rcases finite_cases_next hσ with h | h | h | h | h | h | h | h | h | h | h | h
  · subst σ; simpa only [Sentence.quote_eq_encode] using (reflexivity_provable (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (symmetry_provable (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (transitivity_provable (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (zeroExt_provable (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (oneExt_provable (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (AddExtNormalized.internal_addExt_proof (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (MulExtNormalized.internal_mulExt_proof (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (zeroLtOne_provable (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (AddRightZero.internal_addRightZero_proof (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (MulRightZero.internal_mulRightZero_proof (V := V))
  · subst σ; simpa only [Sentence.quote_eq_encode] using (MulRightOne.internal_mulRightOne_proof (V := V))
  · exact hrest σ h

theorem pa_refutation_of_remaining_next
    (hrest : ∀ σ ∈ remainingFiniteNext, Provable ordinaryPAeq (formulaCode 0 (Encodable.encode σ : V)))
    (hp : Provable 𝗣𝗔 (qqFalsum : V)) : Provable ordinaryPAeq (qqFalsum : V) :=
  pa_refutation_except_finite (finite_supplier_of_remaining_next hrest) hp
#print axioms finite_cases_next
#print axioms finite_supplier_of_remaining_next
#print axioms pa_refutation_of_remaining_next
end PA194PAeq.InductionReopen
