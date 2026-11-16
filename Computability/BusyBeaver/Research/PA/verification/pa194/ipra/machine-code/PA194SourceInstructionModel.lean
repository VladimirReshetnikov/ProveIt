import PA194SourceRegisters
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194SourceInstructionModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRASelectCode PRAModelIOpenPairing PackedClock PackedRootModel PackedDecoderModel
open TableDispatch ConfigurationStep PA194SourceControllerCode PA194SourceRegisters
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem fileModel (s : M) : F file ![s] = pi₂ s := by
  have hv : (![s] : Fin 1 → M) = fun _ => s := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [file,hv,modelDecodeRight]

theorem stateModel (n : Nat) (f : Code 1) (s : M) :
    F (state n f) ![s] = pair (modelNumeral M n) (F f ![s]) := by
  rw [state,modelBin,modelPairCode]
  have hv : (![s] : Fin 1 → M) = fun _ => s := by funext i; exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [show F (constantCode n) ![s] = modelNumeral M n by rw [hv,modelConstant]]

theorem getModel (n : Nat) (s : M) :
    F (getRegister n) ![s] = getSem n (pi₂ s) := by
  rw [getRegister,getAuxModel,fileModel]

theorem setModel (n : Nat) (v : Code 1) (s : M) :
    F (setRegister n v) ![s] = putSem n (pi₂ s) (F v ![s]) := by
  rw [setRegister,putAuxModel,fileModel]

noncomputable def instructionSem : Option M6.Source.Instruction → M → M
  | none, s => pair (modelNumeral M 3673) (pi₂ s)
  | some (.inc r next), s => pair (modelNumeral M (destination next))
      (putSem r.val (pi₂ s) (F Code.succ (fun _ => getSem r.val (pi₂ s))))
  | some (.dec r zero positive), s =>
      if getSem r.val (pi₂ s) = (0 : M) then pair (modelNumeral M (destination zero)) (pi₂ s)
      else pair (modelNumeral M (destination positive))
        (putSem r.val (pi₂ s) (F predCode (fun _ => getSem r.val (pi₂ s))))
  | some (.jump next), s => pair (modelNumeral M (destination next)) (pi₂ s)
  | some .halt, s => pair (modelNumeral M 3674) (pi₂ s)

theorem instructionModel (i : Option M6.Source.Instruction) (s : M) :
    F (instruction i) ![s] = instructionSem i s := by
  classical
  cases i with
  | none => simp only [instruction,instructionSem,stateModel,fileModel]
  | some i =>
    cases i with
    | inc r next =>
      simp only [instruction,instructionSem,stateModel,setModel,modelUnary,getModel]
    | dec r zero positive =>
      simp only [instruction,instructionSem,modelSelectAmong,modelSelectAll,stateModel,setModel,modelUnary,getModel,fileModel]
      by_cases hz : getSem r.val (pi₂ s) = (0 : M)
      · have hz' : getSem r.val (pi₂ s) = F (Code.zero 0) Fin.elim0 := hz
        have hz0 : F (Code.zero 0) Fin.elim0 = (0 : M) := rfl
        simp only [hz',hz,hz0,if_true]
      · have hz' : getSem r.val (pi₂ s) ≠ F (Code.zero 0) Fin.elim0 := hz
        simp only [hz,hz',if_false]
    | jump next => simp only [instruction,instructionSem,stateModel,fileModel]
    | halt => simp only [instruction,instructionSem,stateModel,fileModel]
#print axioms instructionModel
#print axioms getModel
#print axioms setModel
end models
end PA194SourceInstructionModel
