import PA194IncrementSource
import PA194IncrementReturnSentence
set_option autoImplicit false
namespace PA194IncrementSourceSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory BinaryTapeCodes
open PA194RegisterFile PA194MarkedFile PA194RegisterPermutation PA194RegisterUpdate PA194DecrementSource PA194RegisterSplit PA194CarryFile PA194IncrementReturnSentence PA194IncrementSource

def vars : Fin 11 → TermN 12 := fun i => .bvar i.succ
def left : TermN 12 := .bvar 0
def input (r : Fin 9) : Fin (8-(slot r).val+2) → TermN 12 := Fin.lastCases zero (fun i =>
  vars (inputOrder ⟨(slot r).val+i.val,by have := (slot r).isLt; have := i.isLt; omega⟩))
def marked (r : Fin 9) : TermN 12 := .func (markedFile (8-(slot r).val)) (input r)
def prefixArgs (r : Fin 9) : Fin ((slot r).val+1) → TermN 12 := Fin.snoc (fun i =>
  vars (inputOrder ⟨i.val,by have := (slot r).isLt; have := i.isLt; omega⟩)) (marked r)
def selected (r : Fin 9) : TermN 12 := input r 0
def updatedArgs (r : Fin 9) : Fin 11 → TermN 12 :=
  Function.update (Function.update (Function.update vars (logicalIndex r) (app2 addCode (selected r) one)) 9 one) 10 zero
def updated (r : Fin 9) : TermN 12 := .func sourceFileCode (updatedArgs r)
def prefixCost (r : Fin 9) : TermN 12 := .func (costCode (slot r).val) (prefixArgs r)
def tailCost (r : Fin 9) : TermN 12 := .func (costCode (8-(slot r).val)) (fun i => input r i.succ)
def front (r : Fin 9) : TermN 12 := app2 addCode (app2 addCode (app2 addCode one one) (selected r)) (tailCost r)
def incCost (r : Fin 9) : TermN 12 := app2 addCode (app2 addCode (app2 addCode (front r) (state 6)) (tailCost r)) (app2 addCode (app2 addCode (app2 addCode (selected r) one) one) one)
def lhs (r : Fin 9) : TermN 12 := app2 PA194Stepper.stepper
  (app2 addCode (app2 addCode (prefixCost r) (incCost r)) (prefixCost r))
  (PA194IncrementReturnSentence.pack (state 2) left (.func (fileCode (slot r).val) (prefixArgs r)))
def rhs (r : Fin 9) : TermN 12 := PA194IncrementReturnSentence.pack (state 7) (app1 halfCode left)
  (app2 addCode (app1 parityCode left) (PA194IncrementReturnSentence.twice (updated r)))
def sentence (r : Fin 9) : Sentence language := equalClosure (lhs r) (rhs r)
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem modelSentence (r : Fin 9) : M↓[language] ⊧ sentence r := by
  classical
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := PRAModelIOpenPairing.standardModelIOpen
  apply (eqClosureModels _ _).mpr
  intro e
  let es : Fin 11 → M := fun i => Semiterm.val e Empty.elim (vars i)
  let l := Semiterm.val e Empty.elim left
  have h := modelSourceIncrement r es l
  have hi : (fun i => Semiterm.val e Empty.elim (input r i)) = inputArgs (slot r) (physicalArgs es) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [input,Fin.lastCases_last,valZero,inputLast]
    · simp only [input,Fin.lastCases_castSucc]
      have hj : j.val < 8-(slot r).val+1 := j.isLt
      rw [inputNonlast _ _ _ hj]
      rfl
  have hp : (fun i => Semiterm.val e Empty.elim (prefixArgs r i)) =
      frontArgs (slot r) (physicalArgs es) (F (markedFile (8-(slot r).val)) (inputArgs (slot r) (physicalArgs es))) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [prefixArgs,Fin.snoc_last,frontArgs,marked,Semiterm.val_func,Function.comp_def]
      rw [hi]
    · simp only [prefixArgs,Fin.snoc_castSucc,frontArgs]
      rfl
  have hu : (fun i => Semiterm.val e Empty.elim (updatedArgs r i)) =
      Function.update (Function.update (Function.update es (logicalIndex r) (inputArgs (slot r) (physicalArgs es) 0+1)) 9 1) 10 0 := by
    funext i
    by_cases h10 : i = 10
    · subst i; simp [updatedArgs,valZero]
    · by_cases h9 : i = 9
      · subst i; simp [updatedArgs,valOne]
      · by_cases hr : i = logicalIndex r
        · subst i
          simp only [updatedArgs,Function.update_of_ne h10,Function.update_of_ne h9,Function.update_self,valApp2,valOne]
          change Semiterm.val e Empty.elim (input r 0)+1 = _
          rw [show Semiterm.val e Empty.elim (input r 0) = inputArgs (slot r) (physicalArgs es) 0 from congrFun hi 0]
        · simp only [updatedArgs,Function.update_of_ne h10,Function.update_of_ne h9,Function.update_of_ne hr]
          rfl
  simp only [lhs,rhs,prefixCost,incCost,front,tailCost,selected,updated,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,
    valApp2,valApp1,valState,valOne,Semiterm.val_func,Function.comp_def]
  rw [hu,hp]
  have hi0 : Semiterm.val e Empty.elim (input r 0) = inputArgs (slot r) (physicalArgs es) 0 := congrFun hi 0
  have hit : (fun i : Fin (8-(slot r).val+1) => Semiterm.val e Empty.elim (input r i.succ)) =
      (fun i : Fin (8-(slot r).val+1) => inputArgs (slot r) (physicalArgs es) i.succ) := by
    funext i
    exact congrFun hi i.succ
  rw [hi0,hit]
  dsimp only at h
  exact h
end models
theorem classicalPRA (r : Fin 9) : PRA ⊢ sentence r := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence r
/-- The explicit source increment equation is provable in native iPRA
for each fixed source register. -/
theorem nativeIPRA (r : Fin 9) : standardTheory ⊢ equalClosureI (lhs r) (rhs r) := nativeOfClassical (lhs r) (rhs r) (classicalPRA r)
#print axioms modelSentence
#print axioms nativeIPRA
end PA194IncrementSourceSentence
