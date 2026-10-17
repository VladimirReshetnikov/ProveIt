import BusyBeaver.ZFC.ArithmeticCommandPreservation254
import BusyBeaver.ZFC.ArithmeticEnumeratorRun254

/-!
The reverse arithmetic scheduler direction, from certified initial working
states. A bounded actual proof certificate is preserved at every live step;
a halting step supplies an accepted falsity proof. The Sigma1 time invariant
retains that witness after the absorbing scheduler halt. All times, command
codes and proof witnesses range over arbitrary IΣ1 model elements.
No claim is made for arbitrary uncertified dirty initial states, ZFC proof
codes, the binary machine, or a PA consistency equivalence.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticHistory254 (value value_defined)
open ArithmeticStackCertificate254
open ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254
open ArithmeticCommandPreservation254
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance value_definable : 𝚺₁-Function₁[V] value := value_defined.to_definable
local instance working_definable : 𝚺₁-Function₁[V] working := working_defined.to_definable

/-- A halted scalar carries an actual proof of falsity; a live scalar carries
one finite bound on all current theorem-stack witnesses. -/
def SoundConfig (config : V) : Prop :=
  (config = 0 ∧ ∃ p : V, value p = 2) ∨
    (config ≠ 0 ∧ CertifiedWorking (working config))

instance soundConfig_definable : 𝚺₁-Predicate (SoundConfig (V := V)) := by
  unfold SoundConfig
  definability

lemma sound_zero_iff : SoundConfig (0 : V) ↔ ∃ p : V, value p = 2 := by
  simp [SoundConfig]

lemma sound_live (pl np w : V) (hw : CertifiedWorking w) :
    SoundConfig (liveValue pl np w) := by
  exact Or.inr ⟨live_ne_zero pl np w, by simpa only [working_live] using hw⟩

lemma sound_advance (raw np w : V) (hw : CertifiedWorking w) :
    SoundConfig (advanceValue raw np w) := by
  by_cases hz : ArithmeticCommandStep254.stepValue raw w = 0
  · exact Or.inl ⟨by simp only [advanceValue, hz, if_true], certified_halt hw hz⟩
  · rw [advanceValue, if_neg hz]
    exact sound_live _ _ _ (certified_step hw hz)

/-- The nonzero guard is essential: the already halted zero scalar is handled
by its retained falsity witness, never by command preservation at working0. -/
theorem sound_step {config : V} (hs : SoundConfig config) : SoundConfig (step config) := by
  rcases hs with ⟨rfl, hp⟩ | ⟨hc, hw⟩
  · rw [step_zero]
    exact Or.inl ⟨rfl, hp⟩
  · rw [step, if_neg hc]
    by_cases hz : pointer config = 0
    · rw [if_pos hz]
      exact sound_advance _ _ _ hw
    · rw [if_neg hz]
      exact sound_advance _ _ _ hw

/-- The induction predicate is Sigma1, with the stack proof bound and any
halting proof witness existential. No unbounded forall-exists stream is used. -/
theorem sound_run (time initial : V) (hi : SoundConfig initial) :
    SoundConfig (run time initial) := by
  induction time using ISigma1.sigma1_succ_induction
  · definability
  case zero => simpa only [run_zero] using hi
  case succ time ih =>
    rw [run_succ]
    exact sound_step ih

theorem accepted_of_run_zero (time initial : V) (hi : SoundConfig initial)
    (hh : run time initial = 0) : ∃ p : V, value p = 2 := by
  have hs := sound_run time initial hi
  rw [hh] at hs
  exact sound_zero_iff.mp hs

/-- Certified working states are permitted at arbitrary active pointers and
candidate indices, not merely at a candidate boundary. -/
theorem accepted_of_certified_run_zero (time pl np w : V)
    (hw : CertifiedWorking w) (hh : run time (liveValue pl np w) = 0) :
    ∃ p : V, value p = 2 :=
  accepted_of_run_zero time _ (sound_live pl np w hw) hh

/-- In particular all-zero logical working fields are certified. -/
theorem accepted_of_zero_work_run_zero (time pl np : V)
    (hh : run time (liveValue pl np 0) = 0) : ∃ p : V, value p = 2 :=
  accepted_of_certified_run_zero time pl np 0 certified_zero hh

end SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254
