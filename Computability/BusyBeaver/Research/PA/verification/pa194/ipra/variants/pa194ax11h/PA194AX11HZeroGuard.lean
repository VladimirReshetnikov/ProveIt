import PA194AX11HThroughPrepValues
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
namespace PA194AX11HZeroGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor PA194TargetCantor
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

/-- The zero antecedent implication is zero precisely for zero consequent. -/
theorem zero_guard_iff (z : M) : impValue 0 z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hp : cantor (0 : M) z = 0 := by
      rcases mul_eq_zero.mp h with hfour | hz
      · norm_num at hfour
      · exact hz
    have hc : (0 : M) = 0 ∧ z = 0 := by
      apply cantor_injective
      simpa [cantor,triangle] using hp
    exact hc.2
  · rintro rfl
    simp [impValue,cantor,triangle]

/-- Successful comparison still produces zero when the incoming cache is zero. -/
theorem guarded_value_zero (z : M) : (if impValue 0 z = 0 then z else 0) = 0 := by
  by_cases h : impValue 0 z = 0
  · rw [if_pos h,(zero_guard_iff z).mp h]
  · rw [if_neg h]

#print axioms zero_guard_iff
#print axioms guarded_value_zero
end models
end PA194AX11HZeroGuard
