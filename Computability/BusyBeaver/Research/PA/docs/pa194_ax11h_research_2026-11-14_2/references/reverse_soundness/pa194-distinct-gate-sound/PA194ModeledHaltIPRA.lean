import ConPAISigma1Directions
import PA194ModeledHaltRefutesPA
import PA195RefutationBridge
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194ModeledHaltIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula
open ConPA.ISigma1Models ConPA.MachineEndpoint
open LO.FirstOrder.Arithmetic.Bootstrapping
open PA194SchedulerHaltCode
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

def haltTerm : Semiterm language Empty 1 := .func haltAfter (fun _ => #0)
def haltMatrix : Semisentence language 1 := .rel .eq ![haltTerm, .func oneCode Fin.elim0]
def haltClassical : Sentence language := ∃⁰ haltMatrix
def haltSentence : Sentenceᵢ language := native haltClassical

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
    Structure.func (L := language) haltAfter (fun _ => t) = (1 : M) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim ![t] haltMatrix ↔ _
  simp only [haltMatrix, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz (v : Fin 1 → M) : (Semiterm.val v Empty.elim ∘ (Fin.elim0 : Fin 0 → Semiterm language Empty 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [haltTerm, Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one, hz]
  rfl
end models

theorem consistency_implies_modeled_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡒 ∼haltSentence := by
  apply ConPA.Directions.ipra_consistency_implies_nonhalt haltMatrix
  · simp [haltMatrix, Semiformula.Open]
  · intro M _ _ _ _ hM hhalt
    letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
    letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
    letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
    letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
    letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hM
    have hmodel : ∃ t : M, Structure.func (L := language) haltAfter (fun _ => t) = (1 : M) := by
      rw [models_iff] at hhalt
      simpa only [Semiformula.eval_ex, haltMatrix_eval] using hhalt
    obtain ⟨t, ht⟩ := hmodel
    rw [models_iff, PA195RefutationBridge.mapped_refutation_iff]
    apply PA194ModeledHaltRefutesPA.modeled_halt_refutes_PA t
    simpa [Matrix.fun_eq_vec_one] using ht
#print axioms haltMatrix_eval
#print axioms consistency_implies_modeled_nonhalt
end PA194ModeledHaltIPRA
