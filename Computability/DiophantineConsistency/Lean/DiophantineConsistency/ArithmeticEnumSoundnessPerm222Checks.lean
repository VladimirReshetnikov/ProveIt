import DiophantineConsistency.ArithmeticEnumSoundnessPerm222

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticEnumSoundnessPerm222Checks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticEnumSoundnessPerm222 ArithmeticEnumStepPerm222 ArithmeticEnumRunPerm222
open ArithmeticStackCertificate222

section Reverse
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- The zero work certificate is for an actual live state, not halt0.
example : liveValue (0 : V) 4 0≠0 := live_ne_zero 0 4 0
example : SoundConfig (liveValue (0 : V) 4 0) := sound_live 0 4 0 certified_zero
example (h : SoundConfig (0 : V)) : ∃ proof : V, ArithmeticHistory222.value proof=2 :=
  sound_zero_iff.mp h

-- All internal times and arbitrary pointer/candidate values, including zero.
example (time pl np w : V) (hw : CertifiedWorking w)
    (ht : run time (liveValue pl np w)=0) :
    ∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1] := by
  obtain ⟨proof,hp⟩ := accepted_of_certified_run_zero time pl np w hw ht
  exact ⟨proof,by simpa [one_add_one_eq_two] using hp⟩
end Reverse

section TypeZero
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example : (∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1]) ↔
    ∃ time : V, run time (liveValue 0 4 0)=0 := refutation_iff_zero_work_halts
example (h : ∀ work : V, ∃ time : V, run time (liveValue 0 4 work)=0) :
    ∃ proof : V, ArithmeticHistory222.checkDef.val.Evalb ![proof,1] :=
  refutation_iff_all_work_halts.mpr h
end TypeZero

example : 𝗜𝚺₁ ⊢ refutationEnumerationSentence := isigma1_proves_refutation_enumeration
example : Peano ⊢ refutationEnumerationSentence := peano_proves_refutation_enumeration

#print axioms soundConfig_definable
#print axioms sound_zero_iff
#print axioms sound_live
#print axioms sound_exec
#print axioms sound_step
#print axioms sound_run
#print axioms accepted_of_certified_run_zero
#print axioms accepted_of_zero_work_run_zero
#print axioms refutation_iff_zero_work_halts
#print axioms refutation_iff_all_work_halts
#print axioms isigma1_proves_refutation_enumeration
#print axioms peano_proves_refutation_enumeration
end DiophantineConsistency.ArithmeticEnumSoundnessPerm222Checks
