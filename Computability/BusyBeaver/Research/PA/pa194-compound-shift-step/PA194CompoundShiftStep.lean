import PA194AtomShiftCodeModel
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace PA194CompoundShiftStep
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
  PRAHistoryPairCode PRAExhaustion PRAModelIOpenPairing
open PA194PathIterator PA194TermShiftCodeModel

def binaryCode : Code 3 := unary .succ (bin pairCode (.proj 0) (bin pairCode (.proj 1) (.proj 2)))
def unaryCode : Code 2 := unary .succ (bin pairCode (.proj 0) (.proj 1))
def two : Code 1 := unary .succ (unary .succ (.zero 1))
def three : Code 1 := unary .succ two
def verumCode : Code 1 := bin unaryCode two (.zero 1)
def falsumCode : Code 1 := bin unaryCode three (.zero 1)

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
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem binary_model (tag a b : M) : F binaryCode ![tag,a,b] = pair tag (pair a b) + 1 := by
  simp only [binaryCode, modelUnary, modelBin, modelProjection, modelSucc, modelPairCode,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Function.comp_def, Matrix.cons_val_succ]

theorem unary_model (tag a : M) : F unaryCode ![tag,a] = pair tag a + 1 := by
  simp only [unaryCode, modelUnary, modelBin, modelProjection, modelSucc, modelPairCode,
    Matrix.cons_val_zero, Matrix.cons_val_one]

theorem verum_model (x : M) : F verumCode ![x] = shift M6.PA.RelationalSource.language (^⊤ : M) := by
  rw [shift_verum]
  simp only [verumCode, two, modelBin, unary_model, modelUnary, modelSucc,
    PRAMultiplication.modelZero, qqVerum]
  change pair ((0 : M) + 1 + 1) 0 + 1 = pair 2 0 + 1
  norm_num

theorem falsum_model (x : M) : F falsumCode ![x] = shift M6.PA.RelationalSource.language (^⊥ : M) := by
  rw [shift_falsum]
  simp only [falsumCode, three, two, modelBin, unary_model, modelUnary, modelSucc,
    PRAMultiplication.modelZero, qqFalsum]
  change pair ((0 : M) + 1 + 1 + 1) 0 + 1 = pair 3 0 + 1
  norm_num

theorem and_model {p q : M} (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    F binaryCode ![4,shift M6.PA.RelationalSource.language p,shift M6.PA.RelationalSource.language q] =
      shift M6.PA.RelationalSource.language (p ^⋏ q) := by
  rw [binary_model, shift_and hp hq]
  rfl

theorem or_model {p q : M} (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) :
    F binaryCode ![5,shift M6.PA.RelationalSource.language p,shift M6.PA.RelationalSource.language q] =
      shift M6.PA.RelationalSource.language (p ^⋎ q) := by
  rw [binary_model, shift_or hp hq]
  rfl

theorem all_model {p : M} (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F unaryCode ![6,shift M6.PA.RelationalSource.language p] =
      shift M6.PA.RelationalSource.language (^∀ p) := by
  rw [unary_model, shift_all hp]
  rfl

theorem exs_model {p : M} (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F unaryCode ![7,shift M6.PA.RelationalSource.language p] =
      shift M6.PA.RelationalSource.language (^∃ p) := by
  rw [unary_model, shift_exs hp]
  rfl

#print axioms verum_model
#print axioms falsum_model
#print axioms binary_model
#print axioms unary_model
#print axioms and_model
#print axioms or_model
#print axioms all_model
#print axioms exs_model
end models
end PA194CompoundShiftStep
