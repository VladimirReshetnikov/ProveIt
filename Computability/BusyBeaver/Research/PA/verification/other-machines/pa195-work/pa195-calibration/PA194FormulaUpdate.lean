import PA194FormulaBudget
import PA194TermRecursion
/-! Explicit candidate-PRA formula closing using a packed depth budget.

The constructor equations below are uniform in arbitrary candidate-PRA models.
The root wrapper has not yet been proved equal to Foundation formula closing.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace PA194FormulaUpdate
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194StackCode PA194StackHistory PA194ParamHistory PA194NumeralCode PA194TagCode
 PA194TermRecursion PA194CloseFunction PA194VariableDispatch PA194CloseVariable PA194BranchSeed PRASubAddition

def apply4 (f : Code 1) (x : Code 4) : Code 4 := .comp f (.cons x (.nil 4))
def src (first : Code 1) : Code 4 := apply4 first (.proj 0)
def budget (second : Code 1) : Code 4 := apply4 second (.proj 0)
def tag (first : Code 1) : Code 4 := apply4 (stackComponent first) (src first)
def payload (first second : Code 1) : Code 4 := apply4 (stackComponent second) (src first)
def left (first second : Code 1) : Code 4 := apply4 first (payload first second)
def right (first second : Code 1) : Code 4 := apply4 second (payload first second)
def depth (second : Code 1) : Code 4 := bin subCode (.proj 3) (budget second)
def childAt (first second : Code 1) (child b : Code 4) : Code 4 :=
  let rank := bin pairCode child b
  bin (lookupCode (stackComponent first) (stackComponent second))
    (bin distanceCode (.proj 0) rank) (.proj 1)
def binaryResult (first second : Code 1) : Code 4 :=
  tag2 (tag first) (bin pairCode
    (childAt first second (left first second) (budget second))
    (childAt first second (right first second) (budget second)))
def unaryResult (first second : Code 1) : Code 4 :=
  tag2 (tag first) (childAt first second (payload first second)
    (bin subCode (budget second) (numeralCode 4 1)))

def termClose (first second : Code 1) : Code 3 :=
  .comp (closeCode first second) (.cons (.proj 1) (.cons (.proj 0) (.cons (.proj 2) (.nil 3))))
def atomResult (first second : Code 1) : Code 4 :=
  let arity := left first second
  let rs := right first second
  let sym := apply4 first rs
  let vec := apply4 second rs
  let mapped : Code 4 := .comp (mapVector first second (termClose first second) 2)
    (.cons (.proj 2) (.cons vec (.cons (depth second) (.nil 4))))
  quad (tag first) arity sym mapped

def next (first second : Code 1) : Code 4 :=
  let t := tag first
  let is (n : Nat) := bin equalityCode t (numeralCode 4 n)
  selectAmong (is 0) (atomResult first second)
    (selectAmong (is 1) (atomResult first second)
      (selectAmong (is 2) (src first)
        (selectAmong (is 3) (src first)
          (selectAmong (is 4) (binaryResult first second)
            (selectAmong (is 5) (binaryResult first second)
              (unaryResult first second))))))

def budgetClose (first second : Code 1) : Code 4 := PA194FormulaBudget.packedResult (next first second)

/-- Root budget is the formula code; ceiling is budget plus initial depth. -/
def closeAtDepth (first second : Code 1) : Code 3 :=
  .comp (budgetClose first second)
    (.cons (.proj 0) (.cons (.proj 0) (.cons (.proj 1)
      (.cons (bin addCode (.proj 0) (.proj 2)) (.nil 3)))))
/-- Interface expected by the compiler: label, then formula, at depth zero. -/
def closeFormula (first second : Code 1) : Code 2 :=
  .comp (closeAtDepth first second) (.cons (.proj 1) (.cons (.proj 0) (.cons (.zero 2) (.nil 2))))

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

theorem modelApply4 (f : Code 1) (x : Code 4) (e : Fin 4 → M) :
    F (apply4 f x) e = F f (fun _ => F x e) := by
  rw [apply4,modelComposition]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem modelSrc (first : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (p budget hist label ceiling : M) :
    F (src first) ![pair p budget,hist,label,ceiling] = p := by
  rw [src,modelApply4,modelProjection,modelPi1Code first hf]
  exact pi₁_pair _ _

theorem modelBudget (second : Code 1)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (p b hist label ceiling : M) :
    F (budget second) ![pair p b,hist,label,ceiling] = b := by
  rw [budget,modelApply4,modelProjection,modelPi2Code second hs]
  exact pi₂_pair _ _

theorem modelTag (first : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (t p budget hist label ceiling : M) :
    F (tag first) ![pair (pair t p+1) budget,hist,label,ceiling] = t := by
  rw [tag,modelApply4,modelSrc first hf,modelStackHead first hf]

theorem modelPayload (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p budget hist label ceiling : M) :
    F (payload first second) ![pair (pair t p+1) budget,hist,label,ceiling] = p := by
  rw [payload,modelApply4,modelSrc first hf,modelStackTail second hs]

theorem modelLeft (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p q b hist label ceiling : M) :
    F (left first second) ![pair (pair t (pair p q)+1) b,hist,label,ceiling] = p := by
  rw [left,modelApply4,modelPayload first second hf hs,modelPi1Code first hf,pi₁_pair]
theorem modelRight (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p q b hist label ceiling : M) :
    F (right first second) ![pair (pair t (pair p q)+1) b,hist,label,ceiling] = q := by
  rw [right,modelApply4,modelPayload first second hf hs,modelPi2Code second hs,pi₂_pair]

theorem modelTermClose (first second : Code 1) (label x d : M) :
    F (termClose first second) ![label,x,d] = F (closeCode first second) ![x,label,d] := by
  rw [termClose,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 1 _
  · refine Fin.cases ?_ (fun j => ?_) j
    · exact modelProjection 0 _
    · exact Fin.cases (modelProjection 2 _) (fun j => Fin.elim0 j) j

theorem modelDepth (second : Code 1)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (p b hist label d : M) :
    F (depth second) ![pair p b,hist,label,b+d] = d := by
  rw [depth,modelBin,modelProjection,modelBudget second hs]
  exact modelSubAdd b d

theorem modelChildAt (first second : Code 1) (c b : Code 4) (e : Fin 4 → M) :
    F (childAt first second c b) e =
      F (lookupCode (stackComponent first) (stackComponent second))
        ![F distanceCode ![e 0,pair (F c e) (F b e)],e 1] := by
  rw [childAt,modelBin,modelBin,modelBin,modelPairCode,modelProjection,modelProjection]

theorem modelMapped (first second : Code 1) (v : Code 4) (e : Fin 4 → M) :
    F (.comp (mapVector first second (termClose first second) 2)
      (.cons (.proj 2) (.cons v (.cons (depth second) (.nil 4))))) e =
    F (mapVector first second (termClose first second) 2) ![e 2,F v e,F (depth second) e] := by
  rw [modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 2 _
  · refine Fin.cases rfl (fun j => ?_) j
    exact Fin.cases rfl (fun j => Fin.elim0 j) j

theorem modelAtomResult (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t k sym v b hist label d : M) :
    F (atomResult first second) ![pair (pair t (pair k (pair sym v))+1) b,hist,label,b+d] =
      pair t (pair k (pair sym (F (mapVector first second (termClose first second) 2) ![label,v,d]))) + 1 := by
  rw [atomResult,modelQuad,modelTag first hf,modelLeft first second hf hs,
    modelApply4,modelRight first second hf hs,modelPi1Code first hf,pi₁_pair,modelMapped,
    modelApply4,modelRight first second hf hs,modelPi2Code second hs,pi₂_pair,
    modelDepth second hs]
  rfl

theorem modelBinaryResult (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p q b hist label ceiling : M) :
    F (binaryResult first second) ![pair (pair t (pair p q)+1) b,hist,label,ceiling] =
      pair t (pair
        (F (lookupCode (stackComponent first) (stackComponent second))
          ![F distanceCode ![pair (pair t (pair p q)+1) b,pair p b],hist])
        (F (lookupCode (stackComponent first) (stackComponent second))
          ![F distanceCode ![pair (pair t (pair p q)+1) b,pair q b],hist])) + 1 := by
  rw [binaryResult,tag2,modelBin,modelTagValue,modelTag first hf,modelBin,modelPairCode,
    modelChildAt,modelChildAt,modelLeft first second hf hs,modelRight first second hf hs,
    modelBudget second hs]
  rfl

theorem modelUnaryResult (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p b hist label ceiling : M) :
    F (unaryResult first second) ![pair (pair t p+1) (b+1),hist,label,ceiling] =
      pair t (F (lookupCode (stackComponent first) (stackComponent second))
        ![F distanceCode ![pair (pair t p+1) (b+1),pair p b],hist]) + 1 := by
  rw [unaryResult,tag2,modelBin,modelTagValue,modelTag first hf,modelChildAt,
    modelPayload first second hf hs,modelBin,modelBudget second hs,modelNumeralCode]
  norm_num
  have hsub : F subCode ![b+1,1] = b := by
    have h := modelSubAdd (M := M) 1 b
    change F subCode ![1+b,1] = b at h
    simpa [add_comm] using h
  rw [hsub]

theorem modelCloseAtDepth (first second : Code 1) (p label d : M) :
    F (closeAtDepth first second) ![p,label,d] = F (budgetClose first second) ![p,p,label,p+d] := by
  rw [closeAtDepth,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 _
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection 0 _
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact modelProjection 1 _
      · refine Fin.cases ?_ (fun m => Fin.elim0 m) l
        change F (bin addCode (.proj 0) (.proj 2)) ![p,label,d] = p+d
        rw [modelBin,modelProjection,modelProjection]
        rfl

theorem modelCloseFormula (first second : Code 1) (label p : M) :
    F (closeFormula first second) ![label,p] = F (budgetClose first second) ![p,p,label,p] := by
  rw [closeFormula,modelComposition]
  have hv : (fun i : Fin 3 => F (getCode (.cons (.proj 1) (.cons (.proj 0) (.cons (.zero 2) (.nil 2)))) i) ![label,p]) = ![p,label,0] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection 1 _
    · refine Fin.cases ?_ (fun j => ?_) j
      · exact modelProjection 0 _
      · exact Fin.cases (PRAMultiplication.modelZero _) (fun j => Fin.elim0 j) j
  rw [hv,modelCloseAtDepth]
  simp

theorem modelNext (first second : Code 1) (e : Fin 4 → M) :
    F (next first second) e =
      if F (tag first) e = 0 then F (atomResult first second) e
      else if F (tag first) e = 1 then F (atomResult first second) e
      else if F (tag first) e = 2 then F (src first) e
      else if F (tag first) e = 3 then F (src first) e
      else if F (tag first) e = 4 then F (binaryResult first second) e
      else if F (tag first) e = 5 then F (binaryResult first second) e
      else F (unaryResult first second) e := by
  simp only [next, modelChooseEqual, modelNumeralCode]
  norm_num

theorem modelAtom (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t sym x y b label d : M) (ht : t = 0 ∨ t = 1) :
    F (budgetClose first second)
      ![pair t (pair 2 (pair sym (pair x (pair y 0+1)+1)))+1,b,label,b+d] =
      pair t (pair 2 (pair sym
        (pair (F (closeCode first second) ![x,label,d])
          (pair (F (closeCode first second) ![y,label,d]) 0+1)+1)))+1 := by
  rw [budgetClose,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,modelNext,
    modelTag first hf]
  have hbranch (yes no : M) : (if t = 0 then yes else if t = 1 then yes else no) = yes := by
    rcases ht with rfl | rfl <;> norm_num
  rw [hbranch,modelAtomResult first second hf hs]
  rw [modelMapSucc first second (termClose first second) hf hs,
    modelMapSucc first second (termClose first second) hf hs,
    modelMapZero, modelTermClose, modelTermClose]

theorem modelTruth (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (t payload b label ceiling : M) (ht : t = 2 ∨ t = 3) :
    F (budgetClose first second) ![pair t payload+1,b,label,ceiling] = pair t payload+1 := by
  rw [budgetClose,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,modelNext,
    modelTag first hf,modelSrc first hf]
  rcases ht with rfl | rfl <;> norm_num

/-- Both Boolean constructors recurse at the same budget. -/
theorem modelBoolean (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p q b label ceiling : M) (ht : t = 4 ∨ t = 5) :
    F (budgetClose first second) ![pair t (pair p q)+1,b,label,ceiling] =
      pair t (pair (F (budgetClose first second) ![p,b,label,ceiling])
        (F (budgetClose first second) ![q,b,label,ceiling])) + 1 := by
  rw [budgetClose,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,modelNext,
    modelTag first hf]
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  have ht1 : t ≠ 1 := by rcases ht with rfl | rfl <;> norm_num
  have ht2 : t ≠ 2 := by rcases ht with rfl | rfl <;> norm_num
  have ht3 : t ≠ 3 := by rcases ht with rfl | rfl <;> norm_num
  simp only [ht0,ht1,ht2,ht3,if_false]
  have hbranch (y z : M) : (if t = 4 then y else if t = 5 then y else z) = y := by
    rcases ht with rfl | rfl <;> norm_num
  rw [hbranch,modelBinaryResult first second hf hs]
  have hp : p < pair t (pair p q)+1 :=
    lt_of_le_of_lt (le_trans (le_pair_left p q) (le_pair_right t (pair p q))) (lt_add_one _)
  have hq : q < pair t (pair p q)+1 :=
    lt_of_le_of_lt (le_trans (le_pair_right p q) (le_pair_right t (pair p q))) (lt_add_one _)
  rw [PA194FormulaBudget.lookup_same (next first second) first second hf hs p (pair t (pair p q)+1) b label ceiling hp,
    PA194FormulaBudget.lookup_same (next first second) first second hf hs q (pair t (pair p q)+1) b label ceiling hq]

/-- Packed budget decreases by one under either quantifier. -/
theorem modelQuantifier (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (t p b label ceiling : M) (ht : t = 6 ∨ t = 7) :
    F (budgetClose first second) ![pair t p+1,b+1,label,ceiling] =
      pair t (F (budgetClose first second) ![p,b,label,ceiling]) + 1 := by
  rw [budgetClose,PA194FormulaBudget.modelPackedResult,PA194ParamHistory.modelTranslation,modelNext,
    modelTag first hf]
  have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> norm_num
  have ht1 : t ≠ 1 := by rcases ht with rfl | rfl <;> norm_num
  have ht2 : t ≠ 2 := by rcases ht with rfl | rfl <;> norm_num
  have ht3 : t ≠ 3 := by rcases ht with rfl | rfl <;> norm_num
  have ht4 : t ≠ 4 := by rcases ht with rfl | rfl <;> norm_num
  have ht5 : t ≠ 5 := by rcases ht with rfl | rfl <;> norm_num
  simp only [ht0,ht1,ht2,ht3,ht4,ht5,if_false]
  rw [modelUnaryResult first second hf hs]
  rw [PA194FormulaBudget.lookup_binder (next first second) first second hf hs p (pair t p+1) b label ceiling]
  exact lt_of_le_of_lt (le_pair_right t p) (lt_add_one _)

#print axioms modelCloseFormula
#print axioms modelCloseAtDepth
#print axioms modelAtom
#print axioms modelAtomResult
#print axioms modelDepth
#print axioms modelTermClose
#print axioms modelTruth
#print axioms modelBoolean
#print axioms modelBinaryResult
#print axioms modelQuantifier
#print axioms modelUnaryResult
#print axioms modelChildAt
#print axioms modelNext
#print axioms modelApply4
#print axioms modelPayload
end models
end PA194FormulaUpdate
