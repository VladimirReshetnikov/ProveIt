import PA194CompressedRootContracts

set_option autoImplicit false
set_option maxRecDepth 12000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedRootCode
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode PRASelectCode
open PRAModelIOpenPairing PRAExhaustion TableDispatch
open PA194Path27Header PA194UnaryRuns PA194ZeroRuns PA194SourceSite31Physical PA194RegisterPermutation
open PA194BinaryDouble (unary modelUnary)
open PA194FiniteControls PA194StateOne
open PA194BidirectionalRow PA194SymbolicMove

def wordCode : List Bool → Code 1
  | [] => .proj 0
  | b :: bs => unary (if b then pushOne else pushZero) (wordCode bs)

/-- Dispatch on a bounded ordinal while preserving a model-valued operand. -/
def indexed : List (Code 1) → Code 2
  | [] => .proj 1
  | c :: cs => selectAmong (.proj 0) (bin (indexed cs) (unary predCode (.proj 0)) (.proj 1))
      (unary c (.proj 1))

def pathCodes : List (Code 1) := (List.range 3673).map (wordCode ∘ PA194SourceProgram.path)
def pathDispatch : Code 2 := indexed pathCodes

def offsets : List Nat := (List.range 3673).map (fun i => 48-(PA194SourceProgram.path i).length)

def rightHalf : Code 3 := bin pathDispatch (.proj 0)
  (bin zeros (bin addCode (.proj 1) (unary (lookupCode 0 offsets) (.proj 0))) (unary pushOne (.proj 2)))

/-- The physical root frame as a primitive-recursive function of source
ordinal, additional header gap, and packed physical register file. -/
def rootCode : Code 3 :=
  bin pairCode (unary (constantCode 24) (.proj 0))
    (bin pairCode (unary (constantCode 1) (.proj 0)) rightHalf)

theorem pathCodes_get (i : Fin 3673) :
    pathCodes.getD i.val (.proj 0) = wordCode (PA194SourceProgram.path i.val) := by
  have hi : i.val < pathCodes.length := by
    simpa only [pathCodes,List.length_map,List.length_range] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp only [pathCodes,List.getElem_map,List.getElem_range,Function.comp_apply]

theorem offsets_get (i : Fin 3673) :
    offsets.getD i.val 0 = 48-(PA194SourceProgram.path i.val).length := by
  have hi : i.val < offsets.length := by
    simpa only [offsets,List.length_map,List.length_range] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp only [offsets,List.getElem_map,List.getElem_range]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem wordCodeCorrect (bits : List Bool) (x : M) :
    F (wordCode bits) (fun _ => x) = modelWord bits x := by
  induction bits with
  | nil => exact modelProjection 0 (fun _ => x)
  | cons b bs ih =>
    rw [wordCode,modelUnary,ih,wordPush]
    cases b
    · exact modelPushZero _
    · exact modelPushOne _

theorem indexedCorrect (cs : List (Code 1)) (i : Nat) (x : M) :
    F (indexed cs) ![modelNumeral M i,x] = F (cs.getD i (.proj 0)) (fun _ => x) := by
  induction cs generalizing i with
  | nil =>
    cases i <;> simp only [indexed,List.getD,Option.getD_none,List.getElem?_nil,modelProjection,
      Matrix.cons_val_one,Matrix.cons_val_zero]
  | cons c cs ih =>
    simp only [indexed,modelSelectAmong,modelBin,modelUnary,modelProjection,
      Matrix.cons_val_zero,Matrix.cons_val_one]
    cases i with
    | zero =>
      change F selectCode ![F (Code.zero 0) Fin.elim0,_,_] = _
      rw [modelSelectZero]
      rfl
    | succ i =>
      change F selectCode ![F Code.succ (fun _ => modelNumeral M i),
        F (indexed cs) ![F predCode (fun _ => F Code.succ (fun _ => modelNumeral M i)),x],
        F c (fun _ => x)] = F (cs.getD i (.proj 0)) (fun _ => x)
      rw [modelSelectSucc,modelPredSucc]
      exact ih i

theorem rootCodeCorrect (i : Fin 3673) (gap : M) (args : Fin 11 → M) :
    F rootCode ![modelNumeral M i.val,gap,F sourceFileCode args] =
      physicalFrame i.val (gap+modelNumeral M (48-(PA194SourceProgram.path i.val).length)) args := by
  simp only [rootCode,rightHalf,modelBin,modelUnary,modelProjection,modelConstant,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,modelNumeralOne,pathDispatch,
    modelLookupNumeral,offsets_get,modelPushOne]
  rw [indexedCorrect,pathCodes_get,wordCodeCorrect]
  unfold physicalFrame
  have hr (a : M) : a+a+1 = 1+(a+a) := by ac_rfl
  rw [hr]
  rfl

#print axioms indexedCorrect
#print axioms rootCodeCorrect
end models
end PA194CompressedRootCode
