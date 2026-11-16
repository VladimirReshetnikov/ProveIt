import PA194AX11HGateWindow
import PA194SourcePCBound
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HGateInterval
open PA194AX11HGateWindow
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SourceControllerCode PA194SourcePCBound PA194FiniteControls PA194AX11HGateBinding
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

/-- Step agreement throughout the model-valued half-open gate interval. -/
theorem gate_step_interval (s : M) (hlo : modelNumeral M 3519 ≤ F pc ![s])
    (hhi : F pc ![s] < modelNumeral M 3553) :
    F PA194AX11HSource.step ![s] = F PA194SourceControllerCode.step ![s] := by
  obtain ⟨k,hk⟩ := le_iff_exists_add.mp hlo
  have hlt : k < modelNumeral M 34 := by
    apply (add_lt_add_iff_left (modelNumeral M 3519)).mp
    rw [←hk,←modelNumeralAdd]
    exact hhi
  exact gate_step_bounded s k hlt hk

#print axioms gate_step_interval
end models
end PA194AX11HGateInterval
