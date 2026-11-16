import PA194Path27Frame
import Mathlib.Tactic.FinCases
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Path27Frame
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PA194RegisterFile PA194RegisterFileStandard PA194RegisterPermutation
local instance : Structure language Nat := natStructure
local instance : Structure.Eq language Nat := ⟨fun _ _ => iff_of_eq rfl⟩
local instance : Nat↓[language] ⊧* PRA := nat_models_PRA
local notation "F" => Structure.func (L := language)
def selectedFile (args : Fin 11 → Nat) : List Nat :=
  List.ofFn (fun i : Fin 10 => physicalArgs args i.castSucc)
theorem sourceFileSelected (args : Fin 11 → Nat) :
    F sourceFileCode args = word (M6.Runtime.sepsR (selectedFile args)) (args 10) := by
  rw [modelSourceFile]
  have h := sourceFile (selectedFile args) (args 10)
  have hv : valuesArg (selectedFile args) (args 10) = physicalArgs args := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact h
theorem bitsEqWord (xs : List Bool) :
    PA194Bounded.bits xs = word xs 0 := by
  simpa [PA194Bounded.bits] using bitsAppend xs []

theorem frameSelectedBlank (path : M6.Source.Path) (n : Nat)
    (args : Fin 11 → Nat) (h : args 10 = 0) :
    PA194Bounded.bits (PA194PrimitiveSimulation.frame path n (selectedFile args)).r =
      PA194Path27Header.modelWord (M := Nat) path
        (F PA194ZeroRuns.zeros ![n+(48-path.length),1+2*F sourceFileCode args]) := by
  have hs := sourceFileSelected args
  rw [h, ← bitsEqWord] at hs
  rw [frame_bits_general, hs]
#print axioms bitsEqWord
#print axioms frameSelectedBlank
#print axioms sourceFileSelected
end PA194Path27Frame
