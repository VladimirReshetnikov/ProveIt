import PA194ADStore
import PA194RegisterPermutation
import Mathlib.Tactic.FinCases

set_option autoImplicit false
namespace PA194ADFile
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PA194RegisterFile

/-- Logical inputs in PA194-AD physical order, retaining spare and suffix. -/
def inputOrder : Fin 11 → Fin 11 := ![2,8,1,3,4,7,0,5,6,9,10]

def sourceFileCode : Code 11 := .comp (fileCode 10) (pack 11 (fun i => .proj (inputOrder i)))

def physicalArgs {M : Type} (e : Fin 11 → M) : Fin 11 → M := fun i => e (inputOrder i)

def swapLogical {M : Type} (e : Fin 11 → M) : Fin 11 → M :=
  fun i => if i = 3 then e 4 else if i = 4 then e 3 else e i

theorem physicalArgs_swap {M : Type} (e : Fin 11 → M) :
    physicalArgs e = PA194RegisterPermutation.physicalArgs (swapLogical e) := by
  funext i
  fin_cases i <;> simp [physicalArgs, PA194RegisterPermutation.physicalArgs,
    PA194RegisterPermutation.inputOrder, inputOrder, swapLogical]

theorem sourceRegisterAt {M : Type} (e : Fin 11 → M) (r : Fin 9) :
    physicalArgs e ⟨(PA194ADStore.companion r).val, by exact (PA194ADStore.companion r).isLt.trans (by decide)⟩ =
      e ⟨r.val, r.isLt.trans (by decide)⟩ := by
  fin_cases r <;> simp [physicalArgs, PA194ADStore.companion, inputOrder]

theorem sourceSpareAt {M : Type} (e : Fin 11 → M) : physicalArgs e 9 = e 9 := rfl
theorem sourceSuffixAt {M : Type} (e : Fin 11 → M) : physicalArgs e 10 = e 10 := rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)

theorem modelSourceFile (e : Fin 11 → M) :
    F sourceFileCode e = F (fileCode 10) (physicalArgs e) := by
  rw [sourceFileCode, modelComposition, getCode_pack]
  congr 1
  funext i
  exact modelProjection (inputOrder i) e

theorem modelSourceFile_swap (e : Fin 11 → M) :
    F sourceFileCode e = F PA194RegisterPermutation.sourceFileCode (swapLogical e) := by
  rw [modelSourceFile, PA194RegisterPermutation.modelSourceFile, physicalArgs_swap]

#print axioms modelSourceFile
#print axioms modelSourceFile_swap
end models
#print axioms physicalArgs_swap
#print axioms sourceRegisterAt
#print axioms sourceSpareAt
#print axioms sourceSuffixAt
end PA194ADFile
