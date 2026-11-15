import PA194SourceCompilerInterface
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
open PA194SchedulerHaltCode PA194ModelLogic PA194BindSource PackedClock

/-- A modeled scheduler halt is matched by a physical packed-clock halt at some
possibly different internal time, uniformly in all candidate models. -/
def SchedulerToPackedClock : Prop :=
  ∀ (M : Type) [Nonempty M] [Structure language M] [Structure.Eq language M]
    [M↓[language] ⊧* PRA], ReductISigma1 M → ∀ k : M,
      Structure.func (L := language) haltAfter ![k] = Structure.func (L := language) oneCode Fin.elim0 →
        ∃ t : M, Structure.func (L := language) haltIndicator ![t] =
          Structure.func (L := language) oneCode Fin.elim0

theorem schedulerToPhysical_of_packedClock (h : SchedulerToPackedClock) : SchedulerToPhysical := by
  intro M _ _ _ _ hr ⟨k,hk⟩
  obtain ⟨t,ht⟩ := h M hr k hk
  rw [models_iff]
  change (∃⁰ PA194ExplicitEndpoint.haltMatrix).Eval ![] Empty.elim
  rw [Semiformula.eval_ex]
  refine ⟨t, ?_⟩
  apply (PA194ExplicitEndpoint.haltMatrix_eval t).mpr
  change Structure.func (L := language) haltIndicator (fun _ => t) =
    Structure.func (L := language) oneCode Fin.elim0
  have hv : (![t] : Fin 1 → M) = (fun _ => t) := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [←hv]
  exact ht

theorem physical_nonhalt_consistency_of_packedClock
    (hc : InternalCompiler) (hs : SchedulerToPackedClock) :
    standardTheory ⊢ ∼PA194ExplicitEndpoint.haltSentence 🡒 nativePAConsistency :=
  physical_nonhalt_consistency_of_internalCompiler hc (schedulerToPhysical_of_packedClock hs)

#print axioms schedulerToPhysical_of_packedClock
#print axioms physical_nonhalt_consistency_of_packedClock
end PA194FullSepIPRA
