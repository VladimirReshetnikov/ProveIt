import PA194ProgramCons
import PA194MachineShiftMPCode
set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 2500000
set_option linter.unusedSectionVars false
namespace PA194M5MPArithmetic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194TargetCantor PA194MachineShiftMPCode PA194NumeralCode PA194MachineProjections
open PA194PathIterator PRAEqualityCode PRASelectCode PRAHerbrandSelection
open PA194TermShiftCodeModel PA194CloseVariable PA194TargetStep PA194TargetExtendedStep
open PA194MachineStack PA194MachineAXCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
noncomputable def machineImp5 {n : Nat} (a b : Code n) : Code n :=
  bin mulCode (numeralCode n 5) (bin fixedCantor a b)
noncomputable def mpMatches5 {n : Nat} (t h d x : Code n) : Code n :=
  bin equalityCode (machineImp5 t (mpArg d x)) h
noncomputable def mpTop5 {n : Nat} (t h d x : Code n) : Code n :=
  selectAmong (mpMatches5 t h d x) (mpArg d x) (.zero n)
noncomputable def mpStack5 {n : Nat} (t w h d x : Code n) : Code n :=
  selectAmong (mpMatches5 t h d x) (pair (.zero n) w) w
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
private theorem numeral_cast (n : Nat) : modelNumeral M n = (n : M) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [PA194FiniteControls.modelNumeralSucc, ih, Nat.cast_succ]

theorem machineImp5_model {n : Nat} (a b : Code n) (e : Fin n → M) :
    F (machineImp5 a b) e = PA194ProgramCons.implicationValue 5 (F a e) (F b e) := by
  rw [machineImp5,modelBin,modelNumeralCode,modelBin,modelCantorSelected fixedCantor fixedCantor_certified]
  rw [PA194ProgramCons.implicationValue, numeral_cast]
  rfl

theorem mpTop5_model {n : Nat} (t h d x : Code n) (e : Fin n → M) :
    F (mpTop5 t h d x) e =
      if PA194ProgramCons.implicationValue 5 (F t e) (F d e+F x e) = F h e then F d e+F x e else 0 := by
  simp only [mpTop5,mpMatches5,modelChooseEqual,machineImp5_model,mpArg,add_model,PRAMultiplication.modelZero]
  by_cases he : PA194ProgramCons.implicationValue 5 (F t e) (F d e+F x e) = F h e <;> simp [he] <;> rfl

theorem mpStack5_model {n : Nat} (t w h d x : Code n) (e : Fin n → M) :
    F (mpStack5 t w h d x) e =
      if PA194ProgramCons.implicationValue 5 (F t e) (F d e+F x e) = F h e then cantor 0 (F w e) else F w e := by
  simp only [mpStack5,mpMatches5,modelChooseEqual,machineImp5_model,mpArg,add_model,pair_model,PRAMultiplication.modelZero]
  rfl
#print axioms machineImp5_model
#print axioms mpTop5_model
#print axioms mpStack5_model
end models
end PA194M5MPArithmetic
