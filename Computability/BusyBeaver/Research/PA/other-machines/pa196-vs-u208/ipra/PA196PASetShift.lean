import PA196PAShiftGraphComplete
import PA196PAFormulaShiftGrowth
import DiophantineConsistency.PRAWitnessSetShiftGraph

/-! Arithmetic formula-set shifting: exact graph witness bound and total
fixed-height exponential output bound. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PASetShift
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAWitnessCalculus
  PRAWitnessArithmetic PRAWitnessTransfer PRAWitnessCodeGrowth

section arithmetic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem setShift_le (s : V) : setShift ℒₒᵣ s ≤
    Exp.exp (Exp.exp (tau (3*s+8) (22*s+30)+1)) := by
  let E : V := tau (3*s+8) (22*s+30)
  have hel : ∀ y ∈ setShift ℒₒᵣ s, y < E+1 := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := mem_setShift_iff.mp hy
    apply lt_succ_iff_le.mpr
    by_cases hxf : IsUFormula ℒₒᵣ x
    · have hxs : x ≤ s := le_of_lt (lt_of_mem hx)
      exact le_trans (PA196PAFormulaShiftGrowth.shift_le x hxf)
        (tau_mono (add_le_add (mul_le_mul' le_rfl hxs) le_rfl)
          (add_le_add (mul_le_mul' le_rfl hxs) le_rfl))
    · rw [shift_not_uformula hxf]; simp
  have h := lt_exp_iff.mpr hel
  exact le_trans (le_of_lt h) (exp_monotone_le.mpr (le_of_lt (lt_exp (E+1))))
end arithmetic

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_setShiftGraph : WB M (setShiftGraph ℒₒᵣ).val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝗢𝗽𝗲𝗻) inferInstance
  have := PA196PAShiftGraphComplete.wb_shiftGraph (M := M)
  have := wb_bitDef (M := M)
  have := wb_neg_bitDef (M := M)
  simp only [setShiftGraph, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  refine wb_exs_poly _ (by simp) ‘#1’
    (fun V _ _ e u h => ⟨u, ?_, h⟩) (by wb_auto)
  have h' := h
  simp at h'
  exact le_of_lt (lt_of_mem h'.2)
end models

#print axioms setShift_le
#print axioms wb_setShiftGraph
end PA196PASetShift
