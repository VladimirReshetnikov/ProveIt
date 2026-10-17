import BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open SetTheory.BusyBeaver.ZFC
open ArithmeticHistory254 (value value_defined)
open ArithmeticStackCertificate254
open ArithmeticEnumeratorStep254 ArithmeticEnumeratorRun254 ArithmeticEnumeratorSoundness254
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.soundConfig_definable
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.sound_zero_iff
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.sound_live
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.sound_advance
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.sound_step
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.sound_run
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.accepted_of_run_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.accepted_of_certified_run_zero
#print axioms SetTheory.BusyBeaver.ZFC.ArithmeticEnumeratorSoundness254.accepted_of_zero_work_run_zero
example : SoundConfig (0 : V) ↔ ∃ p : V, value p = 2 := sound_zero_iff
example (pl np w : V) (hw : CertifiedWorking w) : SoundConfig (liveValue pl np w) := sound_live pl np w hw
example (raw np w : V) (hw : CertifiedWorking w) : SoundConfig (advanceValue raw np w) := sound_advance raw np w hw
example (cfg : V) (hs : SoundConfig cfg) : SoundConfig (step cfg) := sound_step hs
example (time initial : V) (hi : SoundConfig initial) : SoundConfig (run time initial) := sound_run time initial hi
example (time initial : V) (hi : SoundConfig initial) (hh : run time initial = 0) : ∃ p : V, value p = 2 := accepted_of_run_zero time initial hi hh
example (time pl np w : V) (hw : CertifiedWorking w) (hh : run time (liveValue pl np w) = 0) : ∃ p : V, value p = 2 := accepted_of_certified_run_zero time pl np w hw hh
example (time pl np : V) (hh : run time (liveValue pl np 0) = 0) : ∃ p : V, value p = 2 := accepted_of_zero_work_run_zero time pl np hh
example (pl np : V) : SoundConfig (liveValue pl np 0) := sound_live pl np 0 certified_zero
example (time : V) (hh : run time (liveValue 0 0 0) = 0) : ∃ p : V, value p = 2 := accepted_of_zero_work_run_zero time 0 0 hh
