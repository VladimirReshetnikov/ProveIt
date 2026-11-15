import PA194SourceSite25Positive
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Site25FrameRelation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion
open PA194SourceControllerCode PA194SourceSite25Physical PA194SourceSite25Positive
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- A matched source configuration and physical root frame, with the physical
    zero-run count kept explicit because source transitions change it. -/
def Matched (site : Nat) (gap source physical : M) : Prop :=
  ∃ (args : Fin 11 → M) (tail : M),
    source = sourceState site args tail ∧ physical = physicalFrame site gap args

/-- One actual site-25 controller instruction has a matching literal physical
    segment, uniformly for both register-8 branches. -/
theorem site25Step (k source physical : M)
    (hm : Matched 25 ((k+1)+1) source physical) :
    ∃ clock nextPhysical : M,
      F PA194Stepper.stepper ![clock,physical] = nextPhysical ∧
        (Matched 27 (k+1) (F step ![source]) nextPhysical ∨
         Matched 26 (((k+1)+1)+1) (F step ![source]) nextPhysical) := by
  classical
  obtain ⟨args,tail,rfl,rfl⟩ := hm
  by_cases hz : args 8 = (0 : M)
  · obtain ⟨hsource,clock,hphysical⟩ := zeroBranch k tail args hz
    refine ⟨clock,physicalFrame 27 (k+1) args,hphysical,Or.inl ?_⟩
    exact ⟨args,tail,hsource,rfl⟩
  · let m := F predCode (fun _ => args 8)
    have hsucc : F Code.succ (fun _ => m) = args 8 :=
      (modelZeroOrSuccPred (args 8)).resolve_left hz
    have hm : args 8 = m+1 := hsucc.symm.trans (modelAddOne m).symm
    obtain ⟨hsource,clock,hphysical⟩ := positiveBranch k tail m args hm
    refine ⟨clock,physicalFrame 26 (((k+1)+1)+1) (Function.update args 8 m),hphysical,Or.inr ?_⟩
    exact ⟨Function.update args 8 m,tail,hsource,rfl⟩
#print axioms site25Step
end models
end PA194Site25FrameRelation
