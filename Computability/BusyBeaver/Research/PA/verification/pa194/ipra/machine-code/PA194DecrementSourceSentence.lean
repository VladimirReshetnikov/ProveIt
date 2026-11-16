import PA194DecrementSource
import PA194DecrementChoiceSentence
set_option autoImplicit false
namespace PA194DecrementSourceSentence
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAEqualityToIPRA IPRANativeTheory IPRAStandardTheory PRASelectCode BinaryTapeCodes
open PA194RegisterFile PA194MarkedFile PA194RegisterPermutation PA194RegisterUpdate
open PA194DecrementChoiceSentence PA194IncrementReturnSentence ConfigurationStep PA194DecrementSource PA194RegisterSplit PA194CarryFile

def vars : Fin 11 → TermN 12 := fun i => .bvar i.succ
def left : TermN 12 := .bvar 0
def value (r : Fin 9) : TermN 12 := vars (logicalIndex r)
def restArgs (r : Fin 9) : Fin (8-(slot r).val+2) → TermN 12 := fun i =>
  vars (inputOrder ⟨(slot r).val+1+i.val,by have := (slot r).isLt; have := i.isLt; omega⟩)
def rest (r : Fin 9) : TermN 12 := .func (fileCode (8-(slot r).val+1)) (restArgs r)
def marked (r : Fin 9) : TermN 12 := app2 markedBlock (value r) (rest r)
def prefixArgs (r : Fin 9) : Fin ((slot r).val+1) → TermN 12 :=
  Fin.snoc (fun i => vars (inputOrder ⟨i.val,by have := (slot r).isLt; have := i.isLt; omega⟩)) (marked r)
def updatedArgs (r : Fin 9) : Fin 11 → TermN 12 := Function.update vars (logicalIndex r) (app1 predCode (value r))
def source : TermN 12 := .func sourceFileCode vars
def updated (r : Fin 9) : TermN 12 := .func sourceFileCode (updatedArgs r)
def cost (r : Fin 9) : TermN 12 := .func (costCode (slot r).val) (prefixArgs r)
def lhs (r : Fin 9) : TermN 12 := app2 PA194Stepper.stepper
  (app2 addCode (app2 addCode (cost r) (choose (value r) (state 4) (state 7))) (cost r))
  (PA194IncrementReturnSentence.pack (state 1) left (.func (fileCode (slot r).val) (prefixArgs r)))
def rhs (r : Fin 9) : TermN 12 := choose (value r)
  (PA194IncrementReturnSentence.pack (state 7) left (app2 addCode (twice (updated r)) one))
  (PA194IncrementReturnSentence.pack (state 11) (app1 halfCode left) (app2 addCode (app1 parityCode left) (twice source)))
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
  have h := modelSourceDecrement r es l
  have hu : (fun i => Semiterm.val e Empty.elim (updatedArgs r i)) =
      Function.update es (logicalIndex r) (F predCode (fun _ => es (logicalIndex r))) := by
    funext i
    by_cases hi : i = logicalIndex r
    · subst i; simp only [updatedArgs,Function.update_self,valApp1]; rfl
    · simp only [updatedArgs,Function.update_of_ne hi]; rfl
  have hp : (fun i => Semiterm.val e Empty.elim (prefixArgs r i)) =
      frontArgs (slot r) (physicalArgs es)
        (F markedBlock ![es (logicalIndex r),F (fileCode (8-(slot r).val+1)) (tailArgs (slot r) (physicalArgs es))]) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [prefixArgs,Fin.snoc_last,frontArgs,marked,valApp2,rest,Semiterm.val_func,Function.comp_def]
      rfl
    · simp only [prefixArgs,Fin.snoc_castSucc,frontArgs]
      rfl
  simp only [lhs,rhs,cost,choose,PA194IncrementReturnSentence.pack,PA194IncrementReturnSentence.twice,source,updated,
    valApp3,valApp2,valApp1,valState,valOne,Semiterm.val_func,Function.comp_def,PA194StateOne.modelNumeralOne]
  rw [hu,hp,modelSelectAll,modelSelectAll]
  dsimp only at h
  by_cases hv : es (logicalIndex r) = (0 : M)
  · simp only [hv,if_true] at h
    have hv' : Semiterm.val e Empty.elim (value r) = F (Code.zero 0) Fin.elim0 := hv
    simp only [hv',if_true]
    change F PA194Stepper.stepper ![(F (costCode (slot r).val) _+TableDispatch.modelNumeral M 7)+F (costCode (slot r).val) _,
      F pairCode ![(1 : M),F pairCode ![l,F (fileCode (slot r).val) _]]] =
      F pairCode ![TableDispatch.modelNumeral M 11,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(F sourceFileCode es+F sourceFileCode es)]]
    simpa only [hv,add_assoc] using h
  · simp only [hv,if_false] at h
    have hv' : Semiterm.val e Empty.elim (value r) ≠ F (Code.zero 0) Fin.elim0 := hv
    simp only [hv',if_false]
    exact h
end models
theorem classicalPRA (r : Fin 9) : PRA ⊢ sentence r := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelSentence r
/-- The explicit decrement equation is provable in native iPRA for each
fixed logical source register. -/
theorem nativeIPRA (r : Fin 9) : standardTheory ⊢ equalClosureI (lhs r) (rhs r) := nativeOfClassical (lhs r) (rhs r) (classicalPRA r)
#print axioms modelSentence
#print axioms nativeIPRA
end PA194DecrementSourceSentence
