import DiophantineConsistency.ArithmeticCommandPreservationPerm222
import DiophantineConsistency.ArithmeticProofWordEnumPerm222

/-! Soundness of the actual permuted C222 scheduler at all internal times.
The Sigma1 invariant retains an actual falsity witness after halt, and a
bounded proof certificate while live. The reverse theorem allows arbitrary
pointers/candidates but requires certified work. Combining certified work0
with the actual forward compiler gives a closed IΣ1/PA equivalence between
the actual C222 checker and this enumerator. No source-theory, binary-machine,
polynomial, or HA endpoint is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumSoundnessPerm222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCantor
open ArithmeticHistory222 (value value_defined)
open ArithmeticStackCertificate222 ArithmeticCommandPreservationPerm222
open ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

section Reverse
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The actual work field of a nonzero live scalar. The total definition at
zero does not make the halted state certified without a falsity witness. -/
noncomputable def working (config : V) : V := second (second (config-1))

local instance second_definable : 𝚺₀-Function₁[V] second := second_defined.to_definable
local instance value_definable : 𝚺₁-Function₁[V] value := value_defined.to_definable

instance working_definable : 𝚺₁-Function₁[V] working := by
  unfold working
  definability

@[simp] theorem working_live (pl np w : V) : working (liveValue pl np w)=w := by
  simp [working,liveValue]

theorem live_ne_zero (pl np w : V) : liveValue pl np w≠0 := by
  simp [liveValue]

/-- All quantified bounds and proof witnesses are internal model elements. -/
def SoundConfig (config : V) : Prop :=
  (config=0 ∧ ∃ proof : V, value proof=2) ∨
    (config≠0 ∧ CertifiedWorking (working config))

instance soundConfig_definable : 𝚺₁-Predicate (SoundConfig (V := V)) := by
  unfold SoundConfig
  definability

theorem sound_zero_iff : SoundConfig (0 : V) ↔ ∃ proof : V, value proof=2 := by
  simp [SoundConfig]

theorem sound_live (pl np w : V) (hw : CertifiedWorking w) :
    SoundConfig (liveValue pl np w) :=
  Or.inr ⟨live_ne_zero pl np w, by simpa only [working_live] using hw⟩

theorem sound_exec (raw np w : V) (hw : CertifiedWorking w) :
    SoundConfig (execValue raw np w) := by
  classical
  by_cases hz : ArithmeticCommandStepPerm222.stepValue raw w=0
  · exact Or.inl ⟨by simp only [execValue,hz,if_true], certified_halt hw hz⟩
  · rw [execValue,if_neg hz]
    exact sound_live _ _ _ (certified_step hw hz)

/-- Actual fetch changes pointer/candidate only; no old scheduler split or
separately assumed command invariant is used. Halt0 preserves its witness. -/
theorem sound_step {config : V} (hs : SoundConfig config) :
    SoundConfig (enumValue config) := by
  classical
  rcases hs with ⟨rfl,hp⟩ | ⟨hc,hw⟩
  · rw [enum_zero]
    exact Or.inl ⟨rfl,hp⟩
  · rw [enumValue,if_neg hc]
    exact sound_exec _ _ _ hw

/-- Genuine Sigma1 induction, not induction over an arbitrary predicate. -/
theorem sound_run (time initial : V) (hi : SoundConfig initial) :
    SoundConfig (run time initial) := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa only [run_zero] using hi
  case succ time ih =>
    rw [run_succ]
    exact sound_step ih

theorem accepted_of_run_zero (time initial : V) (hi : SoundConfig initial)
    (hh : run time initial=0) : ∃ proof : V, value proof=2 := by
  have hs := sound_run time initial hi
  rw [hh] at hs
  exact sound_zero_iff.mp hs

theorem accepted_of_certified_run_zero (time pl np w : V)
    (hw : CertifiedWorking w) (hh : run time (liveValue pl np w)=0) :
    ∃ proof : V, value proof=2 :=
  accepted_of_run_zero time _ (sound_live pl np w hw) hh

/-- Work0 is certified; its live scalar is never the absorbing halt0. -/
theorem accepted_of_zero_work_run_zero (time pl np : V)
    (hh : run time (liveValue pl np 0)=0) : ∃ proof : V, value proof=2 :=
  accepted_of_certified_run_zero time pl np 0 certified_zero hh
end Reverse

section Equivalence
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Type0 matches the fixed finite rho8 circuit used by the forward compiler.
Both predicates are the actual represented checker/run, with no calibration
or desired consistency equivalence supplied as a premise. -/
theorem refutation_iff_zero_work_halts :
    (∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1]) ↔
      ∃ time : V, run time (liveValue 0 4 0)=0 := by
  constructor
  · rintro ⟨proof,hp⟩
    exact ArithmeticProofWordEnumPerm222.enum_halts_of_refutation proof 0 hp
  · rintro ⟨time,ht⟩
    obtain ⟨proof,hp⟩ := accepted_of_zero_work_run_zero time 0 4 ht
    exact ⟨proof,by simpa [one_add_one_eq_two] using hp⟩

/-- The forward direction permits arbitrary dirty work; reverse soundness
uses only its certified work0 instance. No dirty-work certificate is assumed. -/
theorem refutation_iff_all_work_halts :
    (∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1]) ↔
      ∀ work : V, ∃ time : V, run time (liveValue 0 4 work)=0 := by
  constructor
  · rintro ⟨proof,hp⟩ work
    exact ArithmeticProofWordEnumPerm222.enum_halts_of_refutation proof work hp
  · intro h
    exact refutation_iff_zero_work_halts.mpr (h 0)
end Equivalence

/-- Only the fixed actual check/live/run graphs occur in the closed formula. -/
def refutationEnumerationSentence : ArithmeticSentence :=
  “(∃ code, !ArithmeticHistory222.checkDef code 1) ↔
    (∃ initial, !ArithmeticEnumStepPerm222.liveDef initial 0 4 0 ∧
      ∃ time, !ArithmeticEnumRunPerm222.runDef 0 time initial)”

theorem refutationEnumerationSentence_true {V : Type} [ORingStructure V]
    [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : refutationEnumerationSentence.Evalb (M := V) ![] := by
  simpa [refutationEnumerationSentence,eq_comm] using
    (refutation_iff_zero_work_halts (V := V))

/-- Existence of a genuine arithmetic proof via completeness for Type0
models; this theorem does not assert an HA derivation. -/
theorem isigma1_proves_refutation_enumeration : 𝗜𝚺₁ ⊢ refutationEnumerationSentence := by
  apply LO.FirstOrder.Arithmetic.complete.{0} 𝗜𝚺₁ _
  intro M _ _
  simpa [models_iff] using (refutationEnumerationSentence_true (V := M))

theorem peano_proves_refutation_enumeration : Peano ⊢ refutationEnumerationSentence :=
  Entailment.weakening (inferInstance : 𝗜𝚺₁ ⪯ Peano) isigma1_proves_refutation_enumeration

end DiophantineConsistency.ArithmeticEnumSoundnessPerm222
