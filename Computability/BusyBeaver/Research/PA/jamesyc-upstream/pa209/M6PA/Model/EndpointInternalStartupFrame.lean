module
public import M6PA.Model.EndpointInternalCodedSourceFrame
public import M6PA.Model.PATheory
public import M6PA.Model.EndpointInternalStartupTrace
public import M6PA.Model.EndpointInternalFixedFile
@[expose] public section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace M6.Arithmetic.PA.InternalTrace.FixedTrace
open M6 M6.Arithmetic.PA
open M6.Arithmetic.PA.InternalTrace.CodedSource
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open CodedSource

def startupRegisters : List Nat := [2,0,0,0,0,0,0,0,0]
noncomputable def entryState {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] : V :=
  stateCode 1 (fixedFile startupRegisters)

def startupFrameSentence : ArithmeticSentence :=
  “∃ file regs c, !(fixedFileGraph Startup.startupFile) file ∧
    !(fixedFileGraph startupRegisters) regs ∧ !adjoinDef c 1 regs ∧
    !frameGraph c 10 file 81 1 ↑(Startup.finalConfig.right)”

private def frameSentence (file regs : List Nat) (r : Nat) : ArithmeticSentence :=
  “∃ fileCode regsCode c, !(fixedFileGraph file) fileCode ∧
    !(fixedFileGraph regs) regsCode ∧ !adjoinDef c 1 regsCode ∧
    !frameGraph c 10 fileCode 81 1 ↑r”

private lemma frameSentence_sigma (file regs : List Nat) (r : Nat) :
    ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (frameSentence file regs r) := by
  simp [frameSentence]

lemma startupFrame_sigma : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 startupFrameSentence :=
  frameSentence_sigma Startup.startupFile startupRegisters Startup.finalConfig.right

/-- The corrected full 26-spare startup refines original source ordinal0,
with candidate N=2, residual L=0 and all seven other registers zero. Width48
is represented by model-frame gap10 above the width38 floor. -/
lemma startup_refines_nat : Refines (entryState (V := Nat)) 10 (fixedFile Startup.startupFile)
    ⟨81,1,Startup.finalConfig.right⟩ := by
  have he := frame_nat (OriginalCheck.path 0) 10 Startup.startupFile
  have hn : Zip.zc 84 [true]
      (OriginalCheck.path 0 ++ List.replicate (10+(38-(OriginalCheck.path 0).length)) false ++
        true :: Runtime.sepsR Startup.startupFile)=Startup.nativeFrame := by decide +kernel
  rw [hn] at he
  change PhysicalFrame.frame (OriginalCheck.path 0) 10 (fixedFile Startup.startupFile)=
    (⟨81,1,Startup.finalConfig.right⟩ : Symbolic.ModelConf Nat) at he
  refine ⟨?_,?_,?_,?_⟩
  · simp [entryState,ValidStore,fixedFile_length,startupRegisters]
  · rw [fixedFile_length,Startup.full_file_length]
    simp only [natCast_nat]
    exact Or.inr (by decide)
  · funext r
    simp only [entryState,store_state,registers,PhysicalRegisters.readFile]
    rw [fixedFile_nth,fixedFile_nth]
    simpa only [natCast_nat] using (by decide +kernel : ∀ r : Fin 9,
      startupRegisters.getD r.val 0=Startup.startupFile.getD (Source.physicalRegister r) 0) r
  · simp only [entryState,control_state]
    change Frames frameEntries 1 10 (fixedFile Startup.startupFile) ⟨81,1,Startup.finalConfig.right⟩
    rw [←he]
    exact frames_at 0 _ (by rfl) 10 (fixedFile Startup.startupFile)

private theorem frameSentence_correct {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]
    (file regs : List Nat) (r : Nat) :
    (V↓[ℒₒᵣ] ⊧ frameSentence file regs r) ↔
      Refines (stateCode 1 (fixedFile regs)) 10 (fixedFile file) ⟨81,1,(r : V)⟩ := by
  simp [frameSentence,models_iff,fixedFile_correct,adjoin_defined.df,frame_correct,
    numeral_eq_natCast,Nat.cast_ofNat,stateCode]

lemma startupFrame_nat : Nat↓[ℒₒᵣ] ⊧ startupFrameSentence :=
  (frameSentence_correct Startup.startupFile startupRegisters Startup.finalConfig.right).mpr
    (by simpa only [entryState,natCast_nat] using! startup_refines_nat)

theorem pa_proves_startup_frame : theory ⊢ startupFrameSentence :=
  Arithmetic.sigma_one_completeness startupFrame_sigma startupFrame_nat

theorem startup_refines_all_models {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] :
    Refines (entryState (V := V)) 10 (fixedFile Startup.startupFile)
      ⟨81,1,(Startup.finalConfig.right : V)⟩ := by
  have h := consequence_iff.mp (Theory.Proof.sound pa_proves_startup_frame) V inferInstance
  exact (frameSentence_correct Startup.startupFile startupRegisters Startup.finalConfig.right).mp h
#print axioms startup_refines_nat
#print axioms pa_proves_startup_frame
#print axioms startup_refines_all_models
end M6.Arithmetic.PA.InternalTrace.FixedTrace

