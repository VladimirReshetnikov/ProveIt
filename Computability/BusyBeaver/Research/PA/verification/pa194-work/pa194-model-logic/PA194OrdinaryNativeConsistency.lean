import PA194SourceCompilerInterface
import PA194PAeqCompleteSupplier
import DiophantineConsistency.PRABoundedPiOneUnary
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194OrdinaryNativeConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula
open ConPA.ISigma1Models ConPA.MachineEndpoint ConPA.ISigma1Transfer
open LO.FirstOrder.Arithmetic.Bootstrapping
open PA194PAeqBind PA194PAeqTermBlueprint DiophantineConsistency.StrictSigmaOneInduction
attribute [local instance] PA194PAeqBind.ordinaryPAeq_delta
noncomputable def ordinaryRefutation : ArithmeticSentence :=
  provabilityPred PA194PAeq.ordinaryPAeq (⊥ : Sentence PA194PAeq.language)
theorem ordinaryRefutation_sigma : Hierarchy 𝚺 1 ordinaryRefutation := by
  simpa only [ordinaryRefutation,provabilityPred'_val] using
    (provabilityPred' PA194PAeq.ordinaryPAeq (⊥ : Sentence PA194PAeq.language)).sigma_prop
theorem ordinaryBound_sigma : Hierarchy 𝚺 0 (bnd ordinaryRefutation) :=
  hierarchy_bnd ordinaryRefutation_sigma (by decide) (by intro _; rfl)

theorem ordinary_matrix_exists : ∃ q : Semisentence language 1, q.Open ∧
    PRA ⊢ (Semiformula.lMap embedding (∀⁰ ∼bnd ordinaryRefutation) 🡘 ∀⁰ q) ∧
    standardTheory ⊢ ∼native (∃⁰ ∼q) 🡒 nativePAConsistency := by
  obtain ⟨q,hq,hqα⟩ := PRABoundedPiOneUnary.unary_open (bnd ordinaryRefutation) ordinaryBound_sigma
  refine ⟨q,hq,hqα,?_⟩
  apply ConPA.Directions.ipra_nonhalt_implies_consistency (∼q)
  · simpa using hq
  · exact Hierarchy.of_open (by simpa using hq)
  · intro M _ _ _ _ hr hp
    letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
    have hpa : Provable (𝗣𝗔 : ArithmeticTheory) (qqFalsum : M) := by
      rw [models_iff, PA195RefutationBridge.mapped_refutation_iff] at hp
      obtain ⟨d,hd⟩ := hp
      simp [Sentence.quote_def] at hd
      exact ⟨d,hd⟩
    have hor : ordinaryRefutation.Evalb (M := M) ![] := by
      simpa [ordinaryRefutation,provabilityPred,Sentence.quote_def] using
        (PA194PAeq.InductionReopen.pa_refutation_to_ordinary hpa)
    have hb := DiophantineConsistency.StrictPiTwoBridge.eval_bnd_iff (M := M) ordinaryRefutation_sigma
    obtain ⟨w,hw⟩ := hb.mp hor
    have hqmodel := models_of_provable (M := M) (inferInstance : M↓[language] ⊧* PRA) hqα
    simp only [LogicalConnective.iff, Semantics.And.models_and, Semantics.Imp.models_imply] at hqmodel
    by_contra hn
    have hallq : M↓[language] ⊧ ∀⁰ q := by simpa using (ConPA.Directions.hall (∼q) M).mpr hn
    have hmap := hqmodel.2 hallq
    have harith : (∀⁰ ∼bnd ordinaryRefutation).Evalb (M := M) ![] := by
      rw [models_iff, PRAWitnessTransfer.eval_lMap_std] at hmap
      exact hmap
    exact (evalb_all_neg (bnd ordinaryRefutation)).mp harith w hw
#print axioms ordinary_matrix_exists
end PA194OrdinaryNativeConsistency
