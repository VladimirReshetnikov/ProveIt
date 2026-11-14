import PA194TermHistory
import PA194CloseFunction

/-! A course-of-values term-closing update; numeric model equations only. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194TermRecursion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194StackCode PA194StackHistory PA194ParamHistory PA194TermHistory PA194BranchSeed
  PA194VariableDispatch PA194CloseVariable PA194NumeralCode PA194QuadCode PA194TagCode

def onNode (f : Code 1) : Code 4 := .comp f (.cons (.proj 0) (.nil 4))
def tagDecoder (first : Code 1) : Code 1 := stackComponent first
def arityDecoder (first second : Code 1) : Code 1 := apply1 first (stackComponent second)
def symbolDecoder (first second : Code 1) : Code 1 :=
  apply1 first (apply1 second (stackComponent second))
def childValue (first second decoder : Code 1) : Code 4 :=
  .comp (childAt first second decoder)
    (.cons (.proj 0) (.cons (.proj 2) (.cons (.proj 3) (.cons (.proj 1) (.nil 4)))))
def tag2 (x y : Code 4) : Code 4 := bin tagCode x y
def quad (a b c d : Code 4) : Code 4 :=
  .comp quadCode (.cons a (.cons b (.cons c (.cons d (.nil 4)))))
def varResult (first second : Code 1) : Code 4 :=
  .comp (closeVariable first second)
    (.cons (.proj 2) (.cons (.proj 0) (.cons (.proj 3) (.nil 4))))
def funcResult (k : Nat) (first second : Code 1) : Code 4 :=
  let a := onNode (arityDecoder first second)
  let sym := onNode (symbolDecoder first second)
  let c₁ := childValue first second (firstChild first second)
  let c₂ := childValue first second (secondChild first second)
  let vec := match k with
    | 0 => .zero 4
    | 1 => tag2 c₁ (.zero 4)
    | _ => tag2 c₁ (tag2 c₂ (.zero 4))
  quad (numeralCode 4 2) a sym vec
/-- Stage-update arguments are `[termCode, priorHistory, label, depth]`. -/
def next (first second : Code 1) : Code 4 :=
  let arity := onNode (arityDecoder first second)
  let functions := selectAmong (bin equalityCode arity (.zero 4))
    (funcResult 0 first second)
    (selectAmong (bin equalityCode arity (numeralCode 4 1))
      (funcResult 1 first second) (funcResult 2 first second))
  selectAmong (bin equalityCode (onNode (tagDecoder first)) (numeralCode 4 2))
    functions (varResult first second)
def closeCode (first second : Code 1) : Code 3 := translationCode (next first second)

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

theorem modelOnNode (f : Code 1) (e : Fin 4 → M) :
    F (onNode f) e = F f (fun _ => e 0) := by
  rw [onNode,modelComposition]
  congr 1
  funext i
  exact Fin.cases (modelProjection 0 e) (fun j => Fin.elim0 j) i

theorem modelChildValue (first second decoder : Code 1) (e : Fin 4 → M) :
    F (childValue first second decoder) e = F (childAt first second decoder) ![e 0,e 2,e 3,e 1] := by
  rw [childValue,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 e
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection 2 e
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact modelProjection 3 e
      · exact Fin.cases (modelProjection 1 e) (fun m => Fin.elim0 m) l

theorem modelVarResult (first second : Code 1) (e : Fin 4 → M) :
    F (varResult first second) e = F (closeVariable first second) ![e 2,e 0,e 3] := by
  rw [varResult,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 2 e
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact modelProjection 0 e
    · exact Fin.cases (modelProjection 3 e) (fun l => Fin.elim0 l) k

theorem modelQuad (a b c d : Code 4) (e : Fin 4 → M) :
    F (quad a b c d) e = pair (F a e) (pair (F b e) (pair (F c e) (F d e)))+1 := by
  rw [quad,modelComposition]
  have hv : (fun i : Fin 4 => F (getCode (.cons a (.cons b (.cons c (.cons d (.nil 4))))) i) e) =
      ![F a e,F b e,F c e,F d e] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases rfl (fun l => ?_) k
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  rw [hv,modelQuadValue]

theorem modelArity (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (arity sym vec : M) :
    F (arityDecoder first second) (fun _ => pair 2 (pair arity (pair sym vec))+1) = arity := by
  rw [arityDecoder,modelApply1,modelStackTail second hs,modelPi1Code first hf,pi₁_pair]

theorem modelSymbol (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (arity sym vec : M) :
    F (symbolDecoder first second) (fun _ => pair 2 (pair arity (pair sym vec))+1) = sym := by
  rw [symbolDecoder,modelApply1,modelApply1,modelStackTail second hs]
  simp only [modelPi1Code first hf,modelPi2Code second hs,pi₁_pair,pi₂_pair]

theorem modelNext (first second : Code 1) (e : Fin 4 → M) :
    F (next first second) e =
      if F (onNode (tagDecoder first)) e = 2 then
        (if F (onNode (arityDecoder first second)) e = 0 then F (funcResult 0 first second) e
         else if F (onNode (arityDecoder first second)) e = 1 then F (funcResult 1 first second) e
         else F (funcResult 2 first second) e)
      else F (varResult first second) e := by
  rw [next,modelChooseEqual,modelNumeralCode]
  norm_num
  split
  · rw [modelChooseEqual]
    have hz : F (.zero 4) e = (0 : M) := PRAMultiplication.modelZero e
    rw [hz]
    split
    · rfl
    · rw [modelChooseEqual,modelNumeralCode]
      norm_num
  · rfl

theorem modelNextVar (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (tag index hist label depth : M) (hneq : tag ≠ 2) :
    F (next first second) ![pair tag index+1,hist,label,depth] =
      F (closeVariable first second) ![label,pair tag index+1,depth] := by
  have ht : F (onNode (tagDecoder first)) ![pair tag index+1,hist,label,depth] = tag := by
    rw [modelOnNode]
    simp only [Matrix.cons_val_zero]
    exact modelStackHead first hf tag index
  rw [modelNext,ht,if_neg hneq,modelVarResult]
  rfl

theorem modelCloseBound (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (index label depth : M) :
    F (closeCode first second) ![pair 0 index+1,label,depth] =
      if index < depth then pair 0 index+1 else pair 0 (index+1)+1 := by
  rw [closeCode,PA194ParamHistory.modelTranslation]
  have hn : (0 : M) ≠ 2 := ne_of_lt (by norm_num)
  rw [modelNextVar first second hf 0 index _ label depth hn,
    PA194VariableDispatch.modelBound first second hf hs]

theorem modelCloseFree (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (index label depth : M) :
    F (closeCode first second) ![pair 1 index+1,label,depth] =
      if label = index then pair 0 depth+1 else pair 1 index+1 := by
  rw [closeCode,PA194ParamHistory.modelTranslation]
  have hn : (1 : M) ≠ 2 := ne_of_lt (by norm_num)
  rw [modelNextVar first second hf 1 index _ label depth hn,
    PA194VariableDispatch.modelFree first second hf hs]

theorem modelNextFunction (k : Nat) (hk : k ≤ 2) (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (sym v hist label depth : M) :
    F (next first second) ![pair 2 (pair (k : M) (pair sym v))+1,hist,label,depth] =
      F (funcResult k first second) ![pair 2 (pair (k : M) (pair sym v))+1,hist,label,depth] := by
  let e : Fin 4 → M := ![pair 2 (pair (k : M) (pair sym v))+1,hist,label,depth]
  have ht : F (onNode (tagDecoder first)) e = (2 : M) := by
    rw [modelOnNode]
    change F (stackComponent first) (fun _ => pair 2 (pair (k : M) (pair sym v))+1) = 2
    exact modelStackHead first hf 2 _
  have ha : F (onNode (arityDecoder first second)) e = (k : M) := by
    rw [modelOnNode]
    change F (arityDecoder first second) (fun _ => pair 2 (pair (k : M) (pair sym v))+1) = _
    exact modelArity first second hf hs _ _ _
  change F (next first second) e = _
  rw [modelNext,ht,if_pos rfl,ha]
  rcases k with _ | k
  · simp [e]
  rcases k with _ | k
  · norm_num [e]
  rcases k with _ | k
  · norm_num [e]
  · omega

/-- Nullary functions contain no arguments to close. -/
theorem modelCloseNullary (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (sym label depth : M) :
    F (closeCode first second) ![pair 2 (pair 0 (pair sym 0))+1,label,depth] =
      pair 2 (pair 0 (pair sym 0))+1 := by
  rw [closeCode,PA194ParamHistory.modelTranslation]
  have h := modelNextFunction 0 (by decide) first second hf hs sym (0 : M)
    (F (historyCode (next first second)) ![pair 2 (pair 0 (pair sym 0))+1,label,depth]) label depth
  norm_num at h
  rw [h]
  rw [funcResult,modelQuad,modelNumeralCode,modelOnNode,modelOnNode]
  simp only [Matrix.cons_val_zero]
  rw [modelArity first second hf hs,modelSymbol first second hf hs,PRAMultiplication.modelZero]
  norm_num
  rfl

/-- A unary function closes its single encoded argument using the earlier
history, at arbitrary (including nonstandard) model values. -/
theorem modelCloseUnary (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (sym child label depth : M) :
    F (closeCode first second) ![pair 2 (pair 1 (pair sym (pair child 0+1)))+1,label,depth] =
      pair 2 (pair 1 (pair sym (pair (F (closeCode first second) ![child,label,depth]) 0+1)))+1 := by
  let n : M := pair 2 (pair 1 (pair sym (pair child 0+1)))+1
  change F (closeCode first second) ![n,label,depth] = _
  rw [closeCode,PA194ParamHistory.modelTranslation]
  have h := modelNextFunction 1 (by decide) first second hf hs sym (pair child 0+1)
    (F (historyCode (next first second)) ![n,label,depth]) label depth
  norm_num at h
  change F (next first second) ![n,F (historyCode (next first second)) ![n,label,depth],label,depth] =
    F (funcResult 1 first second) ![n,F (historyCode (next first second)) ![n,label,depth],label,depth] at h
  rw [h,funcResult,modelQuad,modelNumeralCode,modelOnNode,modelOnNode]
  simp only [Matrix.cons_val_zero]
  change pair (2 : M) (pair (F (arityDecoder first second) (fun _ => n))
    (pair (F (symbolDecoder first second) (fun _ => n))
      (F (tag2 (childValue first second (firstChild first second)) (.zero 4))
        ![n,F (historyCode (next first second)) ![n,label,depth],label,depth])))+1 = _
  dsimp only [n]
  rw [modelArity first second hf hs,modelSymbol first second hf hs,
    tag2,modelBin,modelTagValue,modelChildValue]
  rw [PRAMultiplication.modelZero]
  change pair (2 : M) (pair (1 : M) (pair sym
    (pair (F (childAt first second (firstChild first second))
      ![pair 2 (pair 1 (pair sym (pair child 0+1)))+1,label,depth,
        F (historyCode (next first second))
          ![pair 2 (pair 1 (pair sym (pair child 0+1)))+1,label,depth]]) 0+1)))+1 = _
  rw [modelFirstLookup (next first second) first second hf hs]

/-- A binary function reads both smaller argument values from its prior
history and preserves arbitrary model-valued closing parameters. -/
theorem modelCloseBinary (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (sym left right label depth : M) :
    F (closeCode first second)
      ![pair 2 (pair 2 (pair sym (pair left (pair right 0+1)+1)))+1,label,depth] =
      pair 2 (pair 2 (pair sym
        (pair (F (closeCode first second) ![left,label,depth])
          (pair (F (closeCode first second) ![right,label,depth]) 0+1)+1)))+1 := by
  let n : M := pair 2 (pair 2 (pair sym (pair left (pair right 0+1)+1)))+1
  change F (closeCode first second) ![n,label,depth] = _
  rw [closeCode,PA194ParamHistory.modelTranslation]
  have h := modelNextFunction 2 (by decide) first second hf hs sym (pair left (pair right 0+1)+1)
    (F (historyCode (next first second)) ![n,label,depth]) label depth
  norm_num at h
  change F (next first second) ![n,F (historyCode (next first second)) ![n,label,depth],label,depth] =
    F (funcResult 2 first second) ![n,F (historyCode (next first second)) ![n,label,depth],label,depth] at h
  rw [h,funcResult,modelQuad,modelNumeralCode,modelOnNode,modelOnNode]
  simp only [Matrix.cons_val_zero]
  change pair (2 : M) (pair (F (arityDecoder first second) (fun _ => n))
    (pair (F (symbolDecoder first second) (fun _ => n))
      (F (tag2 (childValue first second (firstChild first second))
        (tag2 (childValue first second (secondChild first second)) (.zero 4)))
        ![n,F (historyCode (next first second)) ![n,label,depth],label,depth])))+1 = _
  dsimp only [n]
  rw [modelArity first second hf hs,modelSymbol first second hf hs,
    tag2,modelBin,modelTagValue,modelChildValue,
    tag2,modelBin,modelTagValue,modelChildValue,PRAMultiplication.modelZero]
  change pair (2 : M) (pair (2 : M) (pair sym
    (pair (F (childAt first second (firstChild first second))
      ![pair 2 (pair 2 (pair sym (pair left (pair right 0+1)+1)))+1,label,depth,
        F (historyCode (next first second))
          ![pair 2 (pair 2 (pair sym (pair left (pair right 0+1)+1)))+1,label,depth]])
      (pair (F (childAt first second (secondChild first second))
        ![pair 2 (pair 2 (pair sym (pair left (pair right 0+1)+1)))+1,label,depth,
          F (historyCode (next first second))
            ![pair 2 (pair 2 (pair sym (pair left (pair right 0+1)+1)))+1,label,depth]]) 0+1)+1)))+1 = _
  rw [modelFirstLookup (next first second) first second hf hs,
    modelSecondLookup (next first second) first second hf hs]
  all_goals norm_num

#print axioms modelCloseBinary

#print axioms modelCloseUnary

#print axioms modelCloseNullary

#print axioms modelNextFunction

#print axioms modelCloseBound
#print axioms modelCloseFree

#print axioms modelOnNode
#print axioms modelChildValue
#print axioms modelVarResult
#print axioms modelQuad
#print axioms modelArity
#print axioms modelSymbol
end models
end PA194TermRecursion
