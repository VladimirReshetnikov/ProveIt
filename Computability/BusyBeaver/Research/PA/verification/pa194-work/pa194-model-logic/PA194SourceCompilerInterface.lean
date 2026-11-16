import PA194FullSepIPRA
import PA195RefutationBridge
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
open PA194ModelLogic PA194BindSource

/-- Every coded PA derivation of falsum admits a coded source-theory refutation. -/
def internalRefutationCompiler (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (hr : ReductISigma1 M) : Prop :=
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  letI := adjunctiveFullSepTheoryDelta
  ∀ d : M, Proof (𝗣𝗔 : ArithmeticTheory) d (⌜(⊥ : ArithmeticSentence)⌝ : M) →
    ∃ e : M, Proof adjunctiveFullSepTheory e (^⊥ : M)

def InternalCompiler : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA] (hr : ReductISigma1 M), internalRefutationCompiler M hr

theorem sourceCalibration_of_internalCompiler (hc : InternalCompiler) : SourceCalibration := by
  intro M _ _ _ _ hr hpa
  letI : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
  letI : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
  letI : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
  letI : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
  letI : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := standard_isigma1 hr
  letI := adjunctiveFullSepTheoryDelta
  have hp : Provable (𝗣𝗔 : ArithmeticTheory) (⌜(⊥ : ArithmeticSentence)⌝ : M) := by
    rw [models_iff, PA195RefutationBridge.mapped_refutation_iff] at hpa
    exact hpa
  obtain ⟨d,hd⟩ := hp
  exact hc M hr d hd

theorem physical_nonhalt_consistency_of_internalCompiler
    (hc : InternalCompiler) (hsync : SchedulerToPhysical) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡒 nativePAConsistency :=
  physical_nonhalt_implies_PA_consistency (sourceCalibration_of_internalCompiler hc) hsync

#print axioms sourceCalibration_of_internalCompiler
#print axioms physical_nonhalt_consistency_of_internalCompiler
end PA194FullSepIPRA
