import PA194ModelMPDrain

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 1500000

namespace PA194ProgramControl
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne
open PRAHistoryPairCode PRAModelIOpenPairing TableDispatch PRASelectCode
open PA194SourceControllerCode PA194StateOne PRAEqualityCode PRABooleanOps
open PA194SourceControllerBinding PA194SourceInstructionModel PA194SourceRegisters
open PA194IteratedSimulation
open ConfigurationStep (modelSelectAll)

abbrev Program := List (Option M6.Source.Instruction)

def row (program : Program) (site : Nat) : Option M6.Source.Instruction :=
  (program[site]?).join

abbrev malformed (program : Program) : Nat := program.length
def halted (program : Program) : Nat := program.length + 1

def action (program : Program) : Option M6.Source.Instruction → Code 1
  | none => state (malformed program) file
  | some .halt => state (halted program) file
  | i => instruction i

def fallback (program : Program) : Code 1 :=
  selectAmong (isOrdinal (malformed program)) (.proj 0)
    (selectAmong (isOrdinal (halted program)) (.proj 0) (state (malformed program) file))

def dispatchFrom (program : Program) : Nat → Program → Code 1
  | _, [] => fallback program
  | n, i :: is => selectAmong (isOrdinal n) (action program i) (dispatchFrom program (n+1) is)

def step (program : Program) : Code 1 := dispatchFrom program 0 program
def run (program : Program) : Code 2 := iterate (step program)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable (program : Program)

theorem selectOrdinal (n : Nat) (yes no : Code 1) (s : M) :
    F (selectAmong (isOrdinal n) yes no) ![s] =
      if F pc ![s] = modelNumeral M n then F yes ![s] else F no ![s] := by
  classical
  rw [modelSelectAmong,modelSelectAll]
  by_cases he : F pc ![s] = modelNumeral M n
  · have hn := (ordinalTest n s).mpr he
    change F (isOrdinal n) ![s] ≠ F (Code.zero 0) Fin.elim0 at hn
    simp only [he,if_true,hn,if_false]
  · have hz : F (isOrdinal n) ![s] = 0 := by
      by_contra hn
      exact he ((ordinalTest n s).mp hn)
    change F (isOrdinal n) ![s] = F (Code.zero 0) Fin.elim0 at hz
    simp only [he,if_false,hz,if_true]

theorem dispatchAt (base : Nat) (rows : Program) (j : Nat)
    (hj : j < rows.length) (s : M) (hs : F pc ![s] = modelNumeral M (base+j)) :
    F (dispatchFrom program base rows) ![s] = F (action program rows[j]) ![s] := by
  induction rows generalizing base j with
  | nil => simp at hj
  | cons i is ih =>
    cases j with
    | zero =>
      rw [dispatchFrom,selectOrdinal]
      simp only [Nat.add_zero] at hs
      simp [hs]
    | succ j =>
      have hn : F pc ![s] ≠ modelNumeral M base := by
        rw [hs]
        exact ne_of_gt (modelNumeralStrict base (base+(j+1)) (by omega))
      rw [dispatchFrom,selectOrdinal,if_neg hn]
      have hj' : j < is.length := by simpa using hj
      have hs' : F pc ![s] = modelNumeral M ((base+1)+j) := by
        exact hs.trans (congrArg (modelNumeral M) (by omega))
      simpa only [List.getElem_cons_succ] using ih (base+1) j hj' hs'

theorem dispatchOutside (base : Nat) (rows : Program) (s : M)
    (hs : ∀ j, base ≤ j → j < base+rows.length → F pc ![s] ≠ modelNumeral M j) :
    F (dispatchFrom program base rows) ![s] = F (fallback program) ![s] := by
  induction rows generalizing base with
  | nil => rfl
  | cons i is ih =>
    rw [dispatchFrom,selectOrdinal,if_neg (hs base le_rfl (by simp))]
    apply ih
    intro j hlo hhi
    apply hs j (by omega)
    simp only [List.length_cons]
    omega

theorem actionAt (q : Nat) (hq : q < program.length) (s : M)
    (hpc : F pc ![s] = modelNumeral M q) :
    F (step program) ![s] = F (action program (row program q)) ![s] := by
  have h := dispatchAt program 0 program q hq s (by simpa using hpc)
  rw [step,h]
  simp [row,List.getElem?_eq_getElem hq]

theorem haltStep (q : Nat) (hq : q < program.length) (s : M)
    (hpc : F pc ![s] = modelNumeral M q) (hrow : row program q = some .halt) :
    F (step program) ![s] = pair (modelNumeral M (halted program)) (pi₂ s) := by
  rw [actionAt program q hq s hpc,hrow]
  simp only [action,stateModel,fileModel]

theorem outsideStep (s : M)
    (hs : ∀ j, j < program.length → F pc ![s] ≠ modelNumeral M j) :
    F (step program) ![s] =
      if F pc ![s] = modelNumeral M (malformed program) then s else
      if F pc ![s] = modelNumeral M (halted program) then s else
        pair (modelNumeral M (malformed program)) (pi₂ s) := by
  rw [step,dispatchOutside program 0 program s (by simpa using hs)]
  simp only [fallback,selectOrdinal,modelProjection,stateModel,fileModel,Matrix.cons_val_zero]

theorem haltedFixed (s : M) (hs : F pc ![s] = modelNumeral M (halted program)) :
    F (step program) ![s] = s := by
  have hnone : ∀ j, j < program.length → F pc ![s] ≠ modelNumeral M j := by
    intro j hj
    rw [hs]
    exact ne_of_gt (modelNumeralStrict j _ (by unfold halted; omega))
  rw [outsideStep program s hnone]
  simp [hs]

theorem malformedFixed (s : M) (hs : F pc ![s] = modelNumeral M (malformed program)) :
    F (step program) ![s] = s := by
  have hnone : ∀ j, j < program.length → F pc ![s] ≠ modelNumeral M j := by
    intro j hj
    rw [hs]
    exact ne_of_gt (modelNumeralStrict j _ hj)
  rw [outsideStep program s hnone]
  simp [hs]

#print axioms actionAt
#print axioms haltStep
#print axioms outsideStep
#print axioms haltedFixed
#print axioms malformedFixed

end models
end PA194ProgramControl
