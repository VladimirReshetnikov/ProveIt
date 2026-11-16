import PA196PRAQVecStepMonotone
import PA196PAQVecSeqTrace

/-! Candidate-PRA semantics of the arithmetic tower recurrence graph. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA196PRAQVecTowerGraphStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PA196PAQVecSeqTrace PA196PRAQVecStepMonotone
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero

theorem boundSucc_eval (out previous index seed : M) :
    boundSuccDef.val.Evalb ![out,previous,index,seed] ↔ out = majorant previous := by
  simp only [boundSuccDef, HierarchySymbol.Semiformula.val_mkSigma]
  simp [numeral_eq_natCast]
  constructor
  · rintro ⟨d,hd,he⟩
    rw [hd.uniq (PRAHistoryTruncation.exponential_expF _)] at he
    exact he.uniq (PRAHistoryTruncation.exponential_expF _)
  · intro h
    subst out
    exact ⟨_, PRAHistoryTruncation.exponential_expF _, PRAHistoryTruncation.exponential_expF _⟩

#print axioms boundSucc_eval
end PA196PRAQVecTowerGraphStep
