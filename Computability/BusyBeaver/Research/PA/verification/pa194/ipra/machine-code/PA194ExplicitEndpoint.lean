import PackedIterationModel
import PackedStandard
import PA194ForwardGG
import PA194StandardSemantics
import DiophantineConsistency.IPRAPA196Consistency
import DiophantineConsistency.IPRABoundedInduction
import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.IPRAImpGG
import DiophantineConsistency.IPRANativeDisjunctionWitness

set_option autoImplicit false
noncomputable section
namespace PA194ExplicitEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PackedClock PackedIterationModel TableDispatch
open IPRAStandardTheory IPRAPA196Consistency IPRANativeTheory IPRANativeFormula IPRANativeFormulaRew
open IPRATheoryHilbertBridge IPRAExistentialComparison IPRANativeForwardTheory IPRANativeDisjunctionWitness

local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def haltTerm : Semiterm language Empty 1 := .func haltIndicator (fun _ => #0)
def haltMatrix : Semisentence language 1 := .rel .eq ![haltTerm, .func oneCode Fin.elim0]
def haltClassical : Sentence language := ∃⁰ haltMatrix
def haltSentence : Sentenceᵢ language := native haltClassical

theorem haltMatrix_bounded : Hierarchy 𝚺 0 haltMatrix := Hierarchy.rel _ _ _ _

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem haltMatrix_eval (t : M) : haltMatrix.Eval ![t] Empty.elim ↔
    Structure.func (L := language) haltIndicator (fun _ => t) = (1 : M) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim ![t] haltMatrix ↔ _
  simp only [haltMatrix, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz (v : Fin 1 → M) : (Semiterm.val v Empty.elim ∘ (Fin.elim0 : Fin 0 → Semiterm language Empty 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [haltTerm, Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one, hz]
  rfl

theorem haltClassical_model_iff :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    Semiformula.Eval (s := (inferInstance : Structure language M)) ![] Empty.elim haltClassical ↔
      ∃ t : M, ¬ pi₁ (Structure.func (L := language) clock (fun _ => t)) < modelNumeral M 194 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [haltClassical, Semiformula.eval_ex, haltMatrix_eval, modelHaltIndicator]

theorem intuitionistic_sentence_model_iff :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    PA194StandardSemantics.evalI (M := M) Empty.elim ![] haltSentence ↔
      ∃ t : M, ¬ pi₁ (Structure.func (L := language) clock (fun _ => t)) < modelNumeral M 194 := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change PA194StandardSemantics.evalI Empty.elim ![] (native haltClassical) ↔ _
  rw [PA194StandardSemantics.eval_native]
  exact haltClassical_model_iff

end models
theorem classical_standard_iff_literal :
    letI : Structure language Nat := natStructure
    letI : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
    Semiformula.Eval (s := (inferInstance : Structure language Nat)) ![] Empty.elim haltClassical ↔
      M6.Zip.Halts PA194.Literal.machine PA194Bounded.blankZip := by
  letI : Structure language Nat := natStructure
  letI : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
  letI : Nat↓[language] ⊧* PRA := nat_models_PRA
  simp only [haltClassical, Semiformula.eval_ex, haltMatrix_eval]
  change (∃ n : Nat, eval haltIndicator (n ::ᵥ List.Vector.nil) = 1) ↔ _
  exact PackedStandard.explicitClock_iff_literal_halts

theorem intuitionistic_sentence_standard_iff_literal :
    letI : Structure language Nat := natStructure
    letI : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
    PA194StandardSemantics.evalI (M := Nat) Empty.elim ![] haltSentence ↔
      M6.Zip.Halts PA194.Literal.machine PA194Bounded.blankZip := by
  letI : Structure language Nat := natStructure
  letI : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
  change PA194StandardSemantics.evalI Empty.elim ![] (native haltClassical) ↔ _
  rw [PA194StandardSemantics.eval_native]
  exact classical_standard_iff_literal
#print axioms intuitionistic_sentence_model_iff
#print axioms intuitionistic_sentence_standard_iff_literal

def halt_backward : nativeTheory ⊢! haltClassicalᴺ 🡒 ∼∼haltSentence := by
  simpa only [haltClassical, haltSentence, native] using
    PA194ForwardGG.exists_backward haltMatrix haltMatrix_bounded

/-- Conditional on the missing classical PRA reduction for this explicit
code, its GG image yields the forward intuitionistic reduction. -/
theorem forward_of_classical_pra
    (h : PRA ⊢ mappedPARefutation 🡒 haltClassical) :
    standardTheory ⊢ nativePARefutation 🡒 ∼∼haltSentence := by
  have hgg : nativeTheory ⊢ mappedPARefutationᴺ 🡒 haltClassicalᴺ :=
    IPRAImpGG.unpack_imp_image nativeTheory _ _ (IPRAFullGGTransfer.from_classical h)
  have hnative : nativeTheory ⊢! nativePARefutation 🡒 ∼∼haltSentence :=
    Entailment.C_trans (theoryNativeForward mappedPARefutation)
      (Entailment.C_trans (Classical.choice hgg) halt_backward)
  exact (IPRAStandardTheory.provable_iff _).2 ⟨hnative⟩

/-- Both machine-specific hypotheses remain explicit and are not proved. -/
def consistency_iff_nonhalting
    (forward : standardTheory ⊢! nativePARefutation 🡒 ∼∼haltSentence)
    (reverse : standardTheory ⊢! haltSentence 🡒 ∼∼nativePARefutation) :
    standardTheory ⊢! nativePAConsistency 🡘 ∼haltSentence := by
  unfold nativePAConsistency
  exact Entailment.K_intro
    (Entailment.C_trans Entailment.dni (Entailment.contra reverse))
    (Entailment.C_trans Entailment.dni (Entailment.contra forward))

#print axioms classical_standard_iff_literal
#print axioms halt_backward
#print axioms forward_of_classical_pra
#print axioms consistency_iff_nonhalting

#print axioms haltClassical_model_iff
end PA194ExplicitEndpoint
