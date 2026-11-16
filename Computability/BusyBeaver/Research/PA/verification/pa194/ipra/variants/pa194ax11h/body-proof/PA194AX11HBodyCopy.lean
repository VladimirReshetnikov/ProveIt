import PA194AX11HCandidateDrain
import PA194ModelAXCopy
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194AX11HBodyCopy
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain PA194ModelAXCopy PA194AX11HCandidateDrain

/-- The candidate rows agree with the primary source throughout the AX body. -/
def BodyRowsAgree : Prop := ∀ (i : Nat) (hlo : 50 ≤ i) (hhi : i < 3519),
  PA194AX11HSource.program[i]'(by rw [PA194AX11HSource.program_length]; omega) = row i

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem copy (agree : BodyRowsAgree) (base : Nat) (r : Fin 9) (rows : Rows base r)
    (hbase : 50 ≤ base) (hend : base+7 ≤ 3519) (a : Fin 11 → M) (tail : M)
    (hX : a 6 = 0) :
    PA194PausedReach.Reaches PA194AX11HSource.step (sourceState base a tail)
      (sourceState (base+7) (Function.update a 1 (a 1+a (location r))) tail) := by
  have row0 := (agree base (by omega) (by omega)).trans rows.input
  have row1 := (agree (base+1) (by omega) (by omega)).trans rows.increaseT
  have row2 := (agree (base+2) (by omega) (by omega)).trans rows.increaseX
  have row3 := (agree (base+3) (by omega) (by omega)).trans rows.repeatR
  have row4 := (agree (base+4) (by omega) (by omega)).trans rows.scratch
  have row5 := (agree (base+5) (by omega) (by omega)).trans rows.increaseR
  have row6 := (agree (base+6) (by omega) (by omega)).trans rows.repeatX
  let mid := Function.update (Function.update (Function.update a (location r) (0 : M))
    1 (a 1+a (location r))) 6 (a (location r))
  have path1 : CandidateIncrements base (base+1) [1,6] :=
    .inc _ _ _ _ (by omega) row1
      (.inc _ _ _ _ (by omega) row2
        (.jump _ (by omega) row3))
  have hne : r ∉ [1,6] := by rcases rows.allowed with h | h | h <;> subst r <;> decide
  have h1 := PA194AX11HCandidateDrain.drain base (base+1) (base+4) r [1,6] (by omega)
    row0 path1 hne a tail
  have mid_eq : argsAfter a r [1,6] (a (location r)) = mid := by
    rcases rows.allowed with h | h | h <;> subst r <;>
      funext i <;> fin_cases i <;> simp [argsAfter,location,tally,mid,subSelf,hX,
        PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [mid_eq] at h1
  have path2 : CandidateIncrements (base+4) (base+5) [r] :=
    .inc _ _ _ _ (by omega) row5
      (.jump _ (by omega) row6)
  have hne2 : (6 : Fin 9) ∉ [r] := by rcases rows.allowed with h | h | h <;> subst r <;> decide
  have h2 := PA194AX11HCandidateDrain.drain (base+4) (base+5) (base+7) 6 [r] (by omega)
    row4 path2 hne2 mid tail
  have final_eq : argsAfter mid 6 [r] (mid (location 6)) = Function.update a 1 (a 1+a (location r)) := by
    rcases rows.allowed with h | h | h <;> subst r <;>
      funext i <;> fin_cases i <;> simp [argsAfter,location,tally,mid,subSelf,hX,
        PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [final_eq] at h2
  exact PA194PausedReach.append PA194AX11HSource.step h1 h2

#print axioms copy
end models
end PA194AX11HBodyCopy
