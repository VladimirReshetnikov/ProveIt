import PA194RegisterPermutation
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194HXAllocation
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PA194RegisterFile

/-- Physical block occupied by each logical register in the primary and HX
    allocations. HX exchanges the H and X blocks, including their data. -/
def primary : Fin 9 → Fin 9 := ![6,2,0,4,3,7,8,5,1]
def hx : Fin 9 → Fin 9 := ![6,2,0,4,3,8,7,5,1]
def swapPhysical (i : Fin 9) : Fin 9 := if i = 7 then 8 else if i = 8 then 7 else i

theorem swap_involutive (i : Fin 9) : swapPhysical (swapPhysical i) = i := by
  fin_cases i <;> decide

theorem map_swap (r : Fin 9) : swapPhysical (hx r) = primary r := by
  fin_cases r <;> decide

def transport {α : Type} (s : Fin 9 → α) : Fin 9 → α := fun i => s (swapPhysical i)
def change {α : Type} (s : Fin 9 → α) (i : Fin 9) (f : α → α) : Fin 9 → α :=
  fun j => if j = i then f (s i) else s j

theorem logical_value {α : Type} (s : Fin 9 → α) (r : Fin 9) :
    transport s (hx r) = s (primary r) := by simp [transport,map_swap]

theorem update_transport {α : Type} (s : Fin 9 → α) (r : Fin 9) (f : α → α) :
    transport (change s (primary r) f) = change (transport s) (hx r) f := by
  funext i
  fin_cases r <;> fin_cases i <;> simp [transport,change,primary,hx,swapPhysical]

theorem test_transport {α : Type} (s : Fin 9 → α) (r : Fin 9) (p : α → Prop) :
    p (transport s (hx r)) ↔ p (s (primary r)) := by rw [logical_value]

/-- Physical slot order for the HX allocation, retaining the spare and suffix. -/
def inputOrder : Fin 11 → Fin 11 := ![2,8,1,4,3,7,0,6,5,9,10]
def sourceFileCode : Code 11 := .comp (fileCode 10) (pack 11 (fun i => .proj (inputOrder i)))
def physicalArgs {M : Type} (e : Fin 11 → M) : Fin 11 → M := fun i => e (inputOrder i)
def swapLogical {M : Type} (e : Fin 11 → M) : Fin 11 → M :=
  fun i => if i = 5 then e 6 else if i = 6 then e 5 else e i

theorem physicalArgs_swap {M : Type} (e : Fin 11 → M) :
    physicalArgs e = PA194RegisterPermutation.physicalArgs (swapLogical e) := by
  funext i
  fin_cases i <;> simp [physicalArgs,PA194RegisterPermutation.physicalArgs,
    PA194RegisterPermutation.inputOrder,inputOrder,swapLogical]

theorem sourceRegisterAt {M : Type} (e : Fin 11 → M) (r : Fin 9) :
    physicalArgs e ⟨(hx r).val, by exact (hx r).isLt.trans (by decide)⟩ =
      e ⟨r.val, r.isLt.trans (by decide)⟩ := by
  fin_cases r <;> simp [physicalArgs,hx,inputOrder]

theorem sourceSpareAt {M : Type} (e : Fin 11 → M) : physicalArgs e 9 = e 9 := rfl
theorem sourceSuffixAt {M : Type} (e : Fin 11 → M) : physicalArgs e 10 = e 10 := rfl

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)

theorem modelSourceFile (e : Fin 11 → M) :
    F sourceFileCode e = F (fileCode 10) (physicalArgs e) := by
  rw [sourceFileCode,modelComposition,getCode_pack]
  congr 1
  funext i
  exact modelProjection (inputOrder i) e

theorem modelSourceFile_swap (e : Fin 11 → M) :
    F sourceFileCode e = F PA194RegisterPermutation.sourceFileCode (swapLogical e) := by
  rw [modelSourceFile,PA194RegisterPermutation.modelSourceFile,physicalArgs_swap]

#print axioms modelSourceFile
#print axioms modelSourceFile_swap
end models
#print axioms logical_value
#print axioms update_transport
#print axioms test_transport
#print axioms physicalArgs_swap
#print axioms sourceRegisterAt
#print axioms sourceSpareAt
#print axioms sourceSuffixAt
end PA194HXAllocation
