import PA194MachineAXCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194MachineShiftMPCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

noncomputable def shiftHalt {n : Nat} (t h : Code n) : Code n :=
  bin equalityCode (bin addCode t h) (numeralCode n 1)
noncomputable def shiftStack {n : Nat} (w : Code n) : Code n := unary fixedSecond w
noncomputable def shiftCache {n : Nat} (w : Code n) : Code n := unary fixedFirst w
noncomputable def mpArg {n : Nat} (d x : Code n) : Code n := bin addCode d x
noncomputable def mpMatches {n : Nat} (t h d x : Code n) : Code n :=
  bin equalityCode (machineImp t (mpArg d x)) h
noncomputable def mpTop {n : Nat} (t h d x : Code n) : Code n :=
  selectAmong (mpMatches t h d x) (mpArg d x) (.zero n)
noncomputable def mpStack {n : Nat} (t w h d x : Code n) : Code n :=
  selectAmong (mpMatches t h d x) (pair (.zero n) w) w

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem shiftHalt_correct {n : Nat} (t h : Code n) (e : Fin n → M) :
    F (shiftHalt t h) e = 1 ↔ F t e + F h e = 1 := by
  rw [shiftHalt,modelBin,add_model,modelNumeralCode]
  simp only [Nat.cast_one]
  change F equalityCode ![F t e + F h e,1] = F oneCode Fin.elim0 ↔ _
  exact (modelEqualityCode (F t e + F h e) (1 : M)).2

theorem shift_preserves [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n : Nat} (t w h : Code n) (e : Fin n → M)
    (hs : SoundStore (F t e) (F w e) (F h e)) :
    SoundStore (F h e) (F (shiftStack w) e) (F (shiftCache w) e) := by
  have hv : (fun _ : Fin 1 => F w e) = ![F w e] := by
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  rw [shiftStack,shiftCache,modelUnary,modelUnary,hv]
  exact PA194MachineStack.shift_preserves (F t e) (F w e) (F h e) hs

theorem mpTop_model {n : Nat} (t h d x : Code n) (e : Fin n → M) :
    F (mpTop t h d x) e =
      if impValue (F t e) (F d e+F x e) = F h e then F d e+F x e else 0 := by
  simp only [mpTop,mpMatches,modelChooseEqual,machineImp_model,mpArg,add_model,PRAMultiplication.modelZero]
  by_cases he : impValue (F t e) (F d e+F x e) = F h e <;> simp [he] <;> rfl

theorem mpStack_model {n : Nat} (t w h d x : Code n) (e : Fin n → M) :
    F (mpStack t w h d x) e =
      if impValue (F t e) (F d e+F x e) = F h e then cantor 0 (F w e) else F w e := by
  simp only [mpStack,mpMatches,modelChooseEqual,machineImp_model,mpArg,add_model,pair_model,PRAMultiplication.modelZero]
  rfl

theorem mp_preserves [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {n : Nat} (t w h d x : Code n) (e : Fin n → M)
    (hs : SoundStore (F t e) (F w e) (F h e)) :
    SoundStore (F (mpTop t h d x) e) (F (mpStack t w h d x) e) 0 := by
  rw [mpTop_model,mpStack_model]
  by_cases he : impValue (F t e) (F d e+F x e) = F h e
  · rw [if_pos he,if_pos he]
    have hp := PA194MachineStack.mp_success_preserves (F t e) (F w e) (F h e) (F d e+F x e) hs he.symm
    rw [modelCantorSelected fixedCantor fixedCantor_certified] at hp
    exact hp
  · rw [if_neg he,if_neg he]
    exact PA194MachineStack.mp_failure_preserves (F t e) (F w e) (F h e) hs

#print axioms shiftHalt_correct
#print axioms shift_preserves
#print axioms mpTop_model
#print axioms mpStack_model
#print axioms mp_preserves
end models
end PA194MachineShiftMPCode
