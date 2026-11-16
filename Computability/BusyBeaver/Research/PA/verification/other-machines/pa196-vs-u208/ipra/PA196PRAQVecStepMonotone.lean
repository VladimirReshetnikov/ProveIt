import PA196PRAQVecTower

/-! Candidate-PRA monotonicity and inflation of the one-step tower majorant.
No assumption of IΣ₁ on the arithmetic reduct is used. -/
set_option autoImplicit false
namespace PA196PRAQVecStepMonotone
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PA196PRAQVecTower
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

noncomputable def majorant (x : M) : M := PRAHistoryTruncation.expF
  ((x + 8 + 4) * PRAHistoryTruncation.expF (22*x+22))

theorem majorant_mono {a b : M} (hab : a ≤ b) : majorant a ≤ majorant b := by
  apply PRAHistoryTruncation.expF_mono
  apply mul_le_mul' (add_le_add (add_le_add hab le_rfl) le_rfl)
  exact PRAHistoryTruncation.expF_mono (add_le_add (mul_le_mul' le_rfl hab) le_rfl)

theorem majorant_increases (x : M) : x ≤ majorant x := by
  have hp : 1 ≤ PRAHistoryTruncation.expF (22*x+22) :=
    pos_iff_one_le.mp (PRAHistoryTruncation.exponential_expF _).range_pos
  have hx : x ≤ (x + 8 + 4) * PRAHistoryTruncation.expF (22*x+22) :=
    le_trans (le_trans le_self_add le_self_add) (le_mul_of_one_le_right (by simp) hp)
  exact le_trans hx (le_of_lt (PRAHistoryTruncation.exponential_expF _).lt)

theorem tower_succ_majorant (n seed : M) : tower (n+1) seed = majorant (tower n seed) := by
  rw [tower_succ, stepTerm_eval]
  simp [majorant, numeral_eq_natCast]

#print axioms majorant_mono
#print axioms majorant_increases
#print axioms tower_succ_majorant
end PA196PRAQVecStepMonotone
