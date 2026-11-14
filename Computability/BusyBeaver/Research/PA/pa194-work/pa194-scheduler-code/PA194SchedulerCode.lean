import PA194MachineShiftMPCode
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194SchedulerCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194PathIterator PA194TermShiftCodeModel PA194CloseVariable PA194NumeralCode PA194TargetCantor
 PA194TargetStep PA194TargetExtendedStep PA194MachineProjections PA194MachineStack PA194MachineAXCode
 PA194MachineShiftMPCode

def choose0 {m : Nat} (tag yes no : Code m) : Code m :=
  selectAmong (bin equalityCode tag (.zero m)) yes no
def choose1 {m : Nat} (tag yes no : Code m) : Code m :=
  selectAmong (bin equalityCode tag (numeralCode m 1)) yes no
noncomputable def fetchSeed {m : Nat} (n l : Code m) : Code m :=
  choose0 l n (unary predCode l)
noncomputable def nextN {m : Nat} (n l : Code m) : Code m :=
  choose0 l (unary .succ n) n
noncomputable def head {m : Nat} (n l : Code m) : Code m := unary fixedFirst (fetchSeed n l)
noncomputable def tail {m : Nat} (n l : Code m) : Code m := unary fixedSecond (fetchSeed n l)
noncomputable def yArg {m : Nat} (n l : Code m) : Code m := unary fixedFirst (tail n l)
noncomputable def tail2 {m : Nat} (n l : Code m) : Code m := unary fixedSecond (tail n l)
noncomputable def xArg {m : Nat} (n l : Code m) : Code m := unary fixedFirst (tail2 n l)
noncomputable def tail3 {m : Nat} (n l : Code m) : Code m := unary fixedSecond (tail2 n l)
noncomputable def axArg {m : Nat} (n l : Code m) : Code m := unary predCode (unary predCode (head n l))
noncomputable def nextL {m : Nat} (n l : Code m) : Code m :=
  choose0 (head n l) (tail n l) (choose1 (head n l) (tail2 n l) (tail3 n l))
noncomputable def nextTop {m : Nat} (n l t w d h : Code m) : Code m :=
  choose0 (head n l) h (choose1 (head n l) (mpTop t h d (yArg n l))
    (axTopCode (axArg n l) d h (yArg n l) (xArg n l)))
noncomputable def nextStack {m : Nat} (n l t w d h : Code m) : Code m :=
  choose0 (head n l) (shiftStack w) (choose1 (head n l) (mpStack t w h d (yArg n l))
    (axStackCode t (axArg n l) d h (yArg n l) (xArg n l) w))
noncomputable def nextD {m : Nat} (n l d : Code m) : Code m :=
  choose0 (head n l) d (choose1 (head n l) (mpArg d (yArg n l)) (.zero m))
noncomputable def nextCache {m : Nat} (n l w : Code m) : Code m :=
  choose0 (head n l) (shiftCache w) (.zero m)
noncomputable def halt {m : Nat} (n l t h : Code m) : Code m :=
  choose0 (head n l) (shiftHalt t h) (.zero m)

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

theorem choose0_model {m : Nat} (tag yes no : Code m) (e : Fin m → M) :
    F (choose0 tag yes no) e = if F tag e = 0 then F yes e else F no e := by
  rw [choose0,modelChooseEqual,PRAMultiplication.modelZero]
  rfl
theorem choose1_model {m : Nat} (tag yes no : Code m) (e : Fin m → M) :
    F (choose1 tag yes no) e = if F tag e = 1 then F yes e else F no e := by
  rw [choose1,modelChooseEqual,modelNumeralCode]
  simp only [Nat.cast_one]

theorem store_preserves [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] {m : Nat} (n l t w d h : Code m) (e : Fin m → M)
    (hs : SoundStore (F t e) (F w e) (F h e)) :
    SoundStore (F (nextTop n l t w d h) e) (F (nextStack n l t w d h) e)
      (F (nextCache n l w) e) := by
  simp only [nextTop,nextStack,nextCache,choose0_model,choose1_model,PRAMultiplication.modelZero]
  by_cases h0 : F (head n l) e = 0
  · simp only [h0,if_pos]
    exact PA194MachineShiftMPCode.shift_preserves t w h e hs
  · simp only [h0,if_false]
    by_cases h1 : F (head n l) e = 1
    · simp only [h1,if_pos]
      exact PA194MachineShiftMPCode.mp_preserves t w h d (yArg n l) e hs
    · simp only [h1,if_false]
      exact PA194MachineAXCode.axCode_preserves t (axArg n l) d h (yArg n l) (xArg n l) w e hs

#print axioms choose0_model
#print axioms choose1_model
#print axioms store_preserves
end models
end PA194SchedulerCode
