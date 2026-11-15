import PA194SourceCompilerInterface
import PA194PAeqFiniteSupplier
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194FullSepIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open IPRAStandardTheory IPRAPA196Consistency IPRANativeFormula
open ConPA.ISigma1Models ConPA.MachineEndpoint
open LO.FirstOrder.Arithmetic.Bootstrapping
open PA194ModelLogic PA194BindSource PA194PAeqBind

def ordinaryRefutationCompiler (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (hr : ReductISigma1 M) : Prop :=
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  letI := adjunctiveFullSepTheoryDelta
  letI := ordinaryPAeq_delta
  Provable PA194PAeq.ordinaryPAeq (qqFalsum : M) → Provable adjunctiveFullSepTheory (^⊥ : M)

def OrdinaryCompiler : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (hr : ReductISigma1 M), ordinaryRefutationCompiler M hr

theorem internalCompiler_of_ordinaryCompiler (hc : OrdinaryCompiler) : InternalCompiler := by
  intro M _ _ _ _ hr
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  letI := adjunctiveFullSepTheoryDelta
  letI := ordinaryPAeq_delta
  intro d hd
  have hp : Provable (𝗣𝗔 : ArithmeticTheory) (qqFalsum : M) := by
    simp [Sentence.quote_def] at hd
    exact ⟨d,hd⟩
  exact hc M hr (PA194PAeq.InductionReopen.pa_refutation_to_ordinary hp)

theorem physical_nonhalt_consistency_of_ordinaryCompiler
    (hc : OrdinaryCompiler) (hsync : SchedulerToPhysical) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡒 nativePAConsistency :=
  physical_nonhalt_consistency_of_internalCompiler (internalCompiler_of_ordinaryCompiler hc) hsync
#print axioms internalCompiler_of_ordinaryCompiler
#print axioms physical_nonhalt_consistency_of_ordinaryCompiler
end PA194FullSepIPRA
