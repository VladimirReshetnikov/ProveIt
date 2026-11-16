import PA194ModelMPDrain

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1300000
set_option linter.unusedSectionVars false

namespace PA194ModelMPTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch
open PA194SchedulerFetchPositive PA194ModelMPDrain

structure TransferRows (base exit : Nat) (r q : Fin 9) : Prop where
  valid : base+2 < 3673
  input : row base = some (.dec r (some exit) (some (base+1)))
  output : row (base+1) = some (.inc q (some (base+2)))
  repeatInput : row (base+2) = some (.jump (some base))

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

def transferArgs (a : Fin 11 → M) (r q : Fin 9) : Fin 11 → M :=
  Function.update (Function.update a (location r) 0) (location q)
    (a (location q)+a (location r))

theorem transferArgs_eq (a : Fin 11 → M) (r q : Fin 9) (hne : r ≠ q) :
    argsAfter a r [q] (a (location r)) = transferArgs a r q := by
  have hd : location r ≠ location q := fun h => hne (Fin.ext (congrArg (Fin.val : Fin 11 → Nat) h))
  funext i
  by_cases hi : i = location r
  · subst i
    simp only [argsAfter,if_true,subSelf,transferArgs,Function.update_of_ne hd,Function.update_self]
  · by_cases hq : i = location q
    · subst i
      have hc : tally (location q) [q] = 1 := by simp [tally]
      simp only [argsAfter,hi,if_false,hc,transferArgs,Function.update_self,
        PA194StateOne.modelNumeralOne,one_mul]
    · have hc : tally i [q] = 0 := by simp [tally,Ne.symm hq]
      simp only [argsAfter,hi,if_false,hc,transferArgs,Function.update_of_ne hq,Function.update_of_ne hi,
        show modelNumeral M 0 = (0:M) from rfl,zero_mul,add_zero]

theorem transfer (base exit : Nat) (r q : Fin 9) (rows : TransferRows base exit r q)
    (hne : r ≠ q) (a : Fin 11 → M) (tail : M) :
    ReachesPositive (sourceState base a tail) (sourceState exit (transferArgs a r q) tail) := by
  have path : Increments base (base+1) [q] :=
    .inc _ _ _ _ (by have := rows.valid; omega) rows.output
      (.jump _ rows.valid rows.repeatInput)
  have h := drain base (base+1) exit r [q] (by have := rows.valid; omega) rows.input path
    (by simp [hne]) a tail
  rwa [transferArgs_eq a r q hne] at h

#print axioms transfer
end models
end PA194ModelMPTransfer
