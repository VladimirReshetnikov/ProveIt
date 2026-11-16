import PA196PRAQVecTower
import PA196PAQVecGrowth

/-! In a candidate-PRA model that also satisfies IΣ₁, one application of
qVec is bounded by one successor step of the coded iterated majorant. -/
set_option autoImplicit false
namespace PA196PAQVecTowerModel
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne

variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem expF_eq_exp (x : M) : PRAHistoryTruncation.expF x = Exp.exp x :=
  (PRAHistoryTruncation.exponential_expF x).uniq (exponential_exp x)

theorem tower_succ_eq_tau (n seed : M) :
    PA196PRAQVecTower.tower (n+1) seed =
      PRAWitnessCodeGrowth.tau (PA196PRAQVecTower.tower n seed + 8)
        (22 * PA196PRAQVecTower.tower n seed + 22) := by
  rw [PA196PRAQVecTower.tower_succ, PA196PRAQVecTower.stepTerm_eval]
  simp [expF_eq_exp, PRAWitnessCodeGrowth.tau, numeral_eq_natCast]

/-- A bound on a parameter remains a bound after applying qVec and taking
one tower step, without assuming that qVec itself is monotone. -/
theorem qVec_le_next_of_le (n seed w : M) (hw : w ≤ PA196PRAQVecTower.tower n seed) :
    qVec ℒₒᵣ w ≤ PA196PRAQVecTower.tower (n+1) seed := by
  rw [tower_succ_eq_tau]
  exact le_trans (PA196PAQVecGrowth.qVec_le w)
    (PRAWitnessCodeGrowth.tau_mono (add_le_add hw le_rfl)
      (add_le_add (mul_le_mul' le_rfl hw) le_rfl))

theorem qVec_le_next (n seed : M) :
    qVec ℒₒᵣ (PA196PRAQVecTower.tower n seed) ≤ PA196PRAQVecTower.tower (n+1) seed :=
  qVec_le_next_of_le n seed _ le_rfl

#print axioms expF_eq_exp
#print axioms qVec_le_next
#print axioms qVec_le_next_of_le
end PA196PAQVecTowerModel
