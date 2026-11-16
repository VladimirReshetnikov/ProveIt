import PA194AdjunctiveFullSep
import ConPAISigma1Directions
import PA194ExplicitEndpoint
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
noncomputable section
namespace PA194FullSepIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula
open ConPA.ISigma1Models ConPA.MachineEndpoint
open LO.FirstOrder.Arithmetic.Bootstrapping
open PA194SchedulerHaltCode PA194ModelLogic PA194BindSource

def modeledHaltTerm : Semiterm language Empty 1 := .func haltAfter (fun _ => #0)
def modeledHaltMatrix : Semisentence language 1 := .rel .eq ![modeledHaltTerm, .func oneCode Fin.elim0]
def modeledHaltSentence : Sentenceᵢ language := native (∃⁰ modeledHaltMatrix)

section modeledEval
variable {M : Type} [Structure language M] [Structure.Eq language M]
local instance fullSepIPRAOne : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
theorem modeledHaltMatrix_eval (t : M) : modeledHaltMatrix.Eval ![t] Empty.elim ↔
    Structure.func (L := language) haltAfter (fun _ => t) = (1 : M) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim ![t] modeledHaltMatrix ↔ _
  simp only [modeledHaltMatrix, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz (v : Fin 1 → M) : (Semiterm.val v Empty.elim ∘ (Fin.elim0 : Fin 0 → Semiterm language Empty 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [modeledHaltTerm, Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one, hz]
  rfl
end modeledEval

/-- Internal refutability of the concrete adjunctive plus fully closed separation theory. -/
def sourceRefutes (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (hr : ReductISigma1 M) : Prop :=
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  letI := adjunctiveFullSepTheoryDelta
  Provable adjunctiveFullSepTheory (^⊥ : M)

/-- Every candidate model transfers its internal PA refutation to this source theory. -/
def SourceCalibration : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (hr : ReductISigma1 M),
    (M↓[language] ⊧ mappedPARefutation) → sourceRefutes M hr

/-- The scheduler reaches its own encoded halt value. -/
def schedulerHalt (M : Type) [Structure language M] : Prop :=
  ∃ k : M, Structure.func (L := language) haltAfter ![k] =
    Structure.func (L := language) oneCode Fin.elim0

/-- Scheduler halting synchronizes with halting of the pinned physical machine. -/
def SchedulerToPhysical : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA], ReductISigma1 M →
      schedulerHalt M → (M↓[language] ⊧ PA194ExplicitEndpoint.haltClassical)

theorem source_refutation_to_scheduler (hsrc : SourceCalibration)
    (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (hr : ReductISigma1 M)
    (hp : M↓[language] ⊧ mappedPARefutation) : schedulerHalt M := by
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  letI := adjunctiveFullSepTheoryDelta
  have hs : Provable adjunctiveFullSepTheory (^⊥ : M) := hsrc M hr hp
  exact adjunctiveFullSep_provable_halts hs

theorem modeled_nonhalt_implies_PA_consistency (hsrc : SourceCalibration) :
    standardTheory ⊢ ∼modeledHaltSentence 🡒 nativePAConsistency := by
  apply ConPA.Directions.ipra_nonhalt_implies_consistency modeledHaltMatrix
  · simp [modeledHaltMatrix, Semiformula.Open]
  · exact Hierarchy.rel _ _ _ _
  · intro M _ _ _ _ hr hp
    have hs := source_refutation_to_scheduler hsrc M hr hp
    obtain ⟨k,hk⟩ := hs
    rw [models_iff, Semiformula.eval_ex]
    refine ⟨k, ?_⟩
    apply (modeledHaltMatrix_eval k).mpr
    change Structure.func (L := language) haltAfter (fun _ => k) =
      Structure.func (L := language) oneCode Fin.elim0
    have hv : (![k] : Fin 1 → M) = (fun _ => k) := by
      funext i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    rw [←hv]
    exact hk

theorem physical_nonhalt_implies_PA_consistency
    (hsrc : SourceCalibration) (hsync : SchedulerToPhysical) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡒 nativePAConsistency := by
  apply ConPA.Directions.ipra_nonhalt_implies_consistency PA194ExplicitEndpoint.haltMatrix
  · simp [PA194ExplicitEndpoint.haltMatrix, Semiformula.Open]
  · exact PA194ExplicitEndpoint.haltMatrix_bounded
  · intro M _ _ _ _ hr hp
    exact hsync M hr (source_refutation_to_scheduler hsrc M hr hp)

#print axioms source_refutation_to_scheduler
#print axioms modeled_nonhalt_implies_PA_consistency
#print axioms physical_nonhalt_implies_PA_consistency
end PA194FullSepIPRA
