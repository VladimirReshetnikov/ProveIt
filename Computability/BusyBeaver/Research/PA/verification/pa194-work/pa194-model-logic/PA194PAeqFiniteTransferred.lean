import PA194PAeqOrdinaryTheoryClass
import PA194PAeqReflSource
import PA194PAeqEqualitySource
import PA194PAeqZeroInternal
import PA194PAeqOneInternal
import PA194PAeqZeroLtOneInternal
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194PAeq.InductionReopen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194PAeqBind PA194PAeqTermBlueprint
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta

theorem fixed_provable_to_ordinary {p : V} (h : Provable targetFixedTheory p) : Provable ordinaryPAeq p := by
  obtain ⟨d,hd⟩ := h
  refine ⟨d,hd.1,hd.2.of_ss ?_⟩
  intro q hq
  exact (ordinaryPAeq_class q).mpr (Or.inl hq)

theorem reflexivity_provable : Provable ordinaryPAeq (formulaCode 0 (⌜Theory.Eq.refl ℒₒᵣ⌝ : V)) :=
  fixed_provable_to_ordinary PA194PAeqTermBlueprint.translated_reflexivity_provable

theorem symmetry_provable : Provable ordinaryPAeq (formulaCode 0 (⌜Theory.Eq.symm ℒₒᵣ⌝ : V)) :=
  fixed_provable_to_ordinary ⟨_,PA194PAeqEqualitySource.symm_witness⟩

theorem transitivity_provable : Provable ordinaryPAeq (formulaCode 0 (⌜Theory.Eq.trans ℒₒᵣ⌝ : V)) :=
  fixed_provable_to_ordinary ⟨_,PA194PAeqEqualitySource.trans_witness⟩

theorem zeroExt_provable : Provable ordinaryPAeq (formulaCode 0 (⌜Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.zero⌝ : V)) :=
  fixed_provable_to_ordinary ZeroCongruence.internal_zeroExt_proof

theorem oneExt_provable : Provable ordinaryPAeq (formulaCode 0 (⌜Theory.Eq.funcExt (L := ℒₒᵣ) Language.ORing.Func.one⌝ : V)) :=
  fixed_provable_to_ordinary OneCongruence.internal_oneExt_proof

theorem zeroLtOne_provable : Provable ordinaryPAeq (formulaCode 0 (⌜PeanoMinus.Axiom.zeroLtOne⌝ : V)) :=
  fixed_provable_to_ordinary ZeroLtOne.internal_zeroLtOne_proof
#print axioms fixed_provable_to_ordinary
#print axioms reflexivity_provable
#print axioms symmetry_provable
#print axioms transitivity_provable
#print axioms zeroExt_provable
#print axioms oneExt_provable
#print axioms zeroLtOne_provable
end PA194PAeq.InductionReopen
