import PA194RegisterContracts
import PA194RegisterRootEncoding
import PA194CompressedControllerStep

set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194RegisterControllerStep
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing TableDispatch PA194FiniteControls PA194StateOne
open PA194SourceControllerCode PA194RegisterLayout PA194RegisterRoot PA194RegisterRootEncoding
open PA194CompressedBoxOracle PA194CompressedBoxFiles PA194CompressedIncrementOracle
open PA194CompressedSourceArgs (spareTail)
open PA194SourceContracts
open ConPA.Machine ConPA.Machine.Compressed
open M6.Runtime

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

/-- Literal register-box correctness with the repeated-spare file suffix. -/
def Boxes (T : Table) (label : Nat → Nat) : Prop :=
  ∀ (a : Fin 11 → M) (count : M) (br : Branch), a 10 = spareTail count → BranchOK a br →
    BoxAgreement T label br (boxValue a (incremented a count))

variable (A : Allocation) {T : Table} {machine : M6.Zip.TMN} {label : Nat → Nat}

theorem stepAt (rows : RowAgreement T machine label) (control : label 84 = 24) (boxes : Boxes (M := M) T label)
    (s s' gap count spare nextCount : M) (i j : Fin 3673)
    (hi : F pc ![s] = modelNumeral M i.val) (hj : F pc ![s'] = modelNumeral M j.val)
    (br : Branch) (hb : BranchOK (tapeArgs A s count spare) br) (extra : Bool) (eff : Eff)
    (hc : contract machine PA194SourceProgram.path br i.val j.val (if extra then 1 else 0) 512 eff = true)
    (hout : boxValue (tapeArgs A s count spare) (incremented (tapeArgs A s count spare) count) (.plain eff) =
      file (tapeArgs A s' nextCount spare)) :
    Reach1 T (F (sourceRootCode A) ![s,gap,count,spare])
      (F (sourceRootCode A) ![s',(if extra then gap+1 else gap),nextCount,spare]) := by
  rw [sourceRootCodeCorrect A s gap count spare i hi, sourceRootCodeCorrect A _ _ _ _ j hj]
  let a := tapeArgs A s count spare
  let box := boxValue a (incremented a count)
  have hbox : BoxAgreement T label br box := boxes a count br (readTail A s count spare) hb
  have hin : box (.plain .none) = file a := rfl
  have h := contract_sound rows PA194SourceProgram.path gap hbox i.val j.val (if extra then 1 else 0) 512 eff hc
  rw [root_eq control, root_eq control, hin, show box (.plain eff) = file (tapeArgs A s' nextCount spare) from hout] at h
  simp only [Nat.add_zero] at h
  cases extra
  · exact h
  · simp only [if_true] at h ⊢
    rw [PA194CompressedControllerStep.shiftOffset] at h
    exact h

theorem haltAt (rows : RowAgreement T machine label) (control : label 84 = 24)
    (terminal : label 254 = 194) (boxes : Boxes (M := M) T label)
    (check : haltContract machine PA194SourceProgram.path 10 512 = true)
    (s gap count spare : M) (hpc : F pc ![s] = modelNumeral M 10) :
    ∃ final, Reach1 T (F (sourceRootCode A) ![s,gap,count,spare]) final ∧ π₁ final = (194 : M) := by
  let a := tapeArgs A s count spare
  let box := boxValue a (incremented a count)
  have hb : BoxAgreement T label none box := boxes a count none (readTail A s count spare) trivial
  have eq : root label PA194SourceProgram.path gap box 10 = F (sourceRootCode A) ![s,gap,count,spare] := by
    rw [root_eq control, sourceRootCodeCorrect A s gap count spare ⟨10,by decide⟩ hpc]
    rfl
  simpa only [eq, Nat.cast_ofNat] using halt_sound rows PA194SourceProgram.path terminal gap hb 10 512 check

#print axioms stepAt
#print axioms haltAt
end models
end PA194RegisterControllerStep
