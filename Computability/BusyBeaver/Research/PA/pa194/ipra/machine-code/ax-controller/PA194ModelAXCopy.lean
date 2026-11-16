import PA194ModelMPDrain
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelAXCopy
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain

/-- Copy a preserved AX register into T, using X as scratch. -/
structure Rows (base : Nat) (r : Fin 9) : Prop where
  allowed : r = 3 ∨ r = 4 ∨ r = 5
  valid : base+6 < 3673
  input : row base = some (.dec r (some (base+4)) (some (base+1)))
  increaseT : row (base+1) = some (.inc 1 (some (base+2)))
  increaseX : row (base+2) = some (.inc 6 (some (base+3)))
  repeatR : row (base+3) = some (.jump (some base))
  scratch : row (base+4) = some (.dec 6 (some (base+7)) (some (base+5)))
  increaseR : row (base+5) = some (.inc r (some (base+6)))
  repeatX : row (base+6) = some (.jump (some (base+4)))

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

theorem copy (base : Nat) (r : Fin 9) (rows : Rows base r) (a : Fin 11 → M) (tail : M)
    (hX : a 6 = 0) :
    ReachesPositive (sourceState base a tail)
      (sourceState (base+7) (Function.update a 1 (a 1+a (location r))) tail) := by
  let mid := Function.update (Function.update (Function.update a (location r) (0 : M))
    1 (a 1+a (location r))) 6 (a (location r))
  have path1 : Increments base (base+1) [1,6] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.increaseT
      (.inc _ _ _ _ (by have := rows.valid; omega) rows.increaseX
        (.jump _ (by have := rows.valid; omega) rows.repeatR))
  have hne : r ∉ [1,6] := by rcases rows.allowed with h | h | h <;> subst r <;> decide
  have h1 := drain base (base+1) (base+4) r [1,6] (by have := rows.valid; omega)
    rows.input path1 hne a tail
  have mid_eq : argsAfter a r [1,6] (a (location r)) = mid := by
    rcases rows.allowed with h | h | h <;> subst r <;>
      funext i <;> fin_cases i <;> simp [argsAfter,location,tally,mid,subSelf,hX,
        PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [mid_eq] at h1
  have path2 : Increments (base+4) (base+5) [r] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.increaseR
      (.jump _ rows.valid rows.repeatX)
  have hne2 : (6 : Fin 9) ∉ [r] := by rcases rows.allowed with h | h | h <;> subst r <;> decide
  have h2 := drain (base+4) (base+5) (base+7) 6 [r] (by have := rows.valid; omega)
    rows.scratch path2 hne2 mid tail
  have final_eq : argsAfter mid 6 [r] (mid (location 6)) = Function.update a 1 (a 1+a (location r)) := by
    rcases rows.allowed with h | h | h <;> subst r <;>
      funext i <;> fin_cases i <;> simp [argsAfter,location,tally,mid,subSelf,hX,
        PA194StateOne.modelNumeralOne,show modelNumeral M 0 = (0:M) from rfl]
  rw [final_eq] at h2
  exact appendPositive h1.reaches h2

#print axioms copy
end models
end PA194ModelAXCopy
