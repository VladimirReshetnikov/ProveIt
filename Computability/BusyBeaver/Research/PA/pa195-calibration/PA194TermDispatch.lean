import PA194CloseFunction

/-! Dispatch closing of encoded variables and one externally fixed-arity function case. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194TermDispatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194VariableDispatch PA194StackCode PA194NumeralCode PA194CloseFunction PA194CloseVariable

/-- The function branch expects externally fixed arity `k` and receives an
explicit child operation. Inputs are closing label, encoded term, and depth. -/
def termDispatch (k : Nat) (first second : Code 1) (child : Code 3) : Code 3 :=
  selectAmong (bin equalityCode (component first) (numeralCode 3 2))
    (functionDispatch k first second child) (closeVariable first second)

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

theorem modelFunction (k : Nat) (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym v depth : M) :
    F (termDispatch k first second child)
      ![label,pair 2 (pair (k : M) (pair sym v))+1,depth] =
      pair 2 (pair (k : M) (pair sym (F (mapVector first second child k) ![label,v,depth])))+1 := by
  have ht : F (component first) ![label,pair 2 (pair (k : M) (pair sym v))+1,depth] = (2 : M) := by
    rw [modelComponent]
    change F (stackComponent first) (fun _ => pair 2 (pair (k : M) (pair sym v))+1) = 2
    exact modelStackHead first hf 2 _
  have hc : F (component first) ![label,pair 2 (pair (k : M) (pair sym v))+1,depth] =
      F (numeralCode 3 2) ![label,pair 2 (pair (k : M) (pair sym v))+1,depth] := by
    rw [ht,modelNumeralCode]
    norm_num
  rw [termDispatch,modelChooseEqual,if_pos hc,modelFunctionDispatch k first second child hf hs]

theorem modelBound (k : Nat) (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (termDispatch k first second child) ![label,pair 0 index+1,depth] =
      if index < depth then pair 0 index+1 else pair 0 (index+1)+1 := by
  have ht : F (component first) ![label,pair 0 index+1,depth] = (0 : M) := by
    rw [modelComponent]
    change F (stackComponent first) (fun _ => pair 0 index+1) = 0
    exact modelStackHead first hf 0 _
  have hc : F (component first) ![label,pair 0 index+1,depth] ≠
      F (numeralCode 3 2) ![label,pair 0 index+1,depth] := by
    rw [ht,modelNumeralCode]
    have hh : (0 : M) < 2 := by norm_num
    exact ne_of_lt hh
  rw [termDispatch,modelChooseEqual,if_neg hc,PA194VariableDispatch.modelBound first second hf hs label index depth]

theorem modelFree (k : Nat) (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (termDispatch k first second child) ![label,pair 1 index+1,depth] =
      if label = index then pair 0 depth+1 else pair 1 index+1 := by
  have ht : F (component first) ![label,pair 1 index+1,depth] = (1 : M) := by
    rw [modelComponent]
    change F (stackComponent first) (fun _ => pair 1 index+1) = 1
    exact modelStackHead first hf 1 _
  have hc : F (component first) ![label,pair 1 index+1,depth] ≠
      F (numeralCode 3 2) ![label,pair 1 index+1,depth] := by
    rw [ht,modelNumeralCode]
    have hh : (1 : M) < 2 := by norm_num
    exact ne_of_lt hh
  rw [termDispatch,modelChooseEqual,if_neg hc,PA194VariableDispatch.modelFree first second hf hs label index depth]

/-- The dispatcher closes an encoded function term with any externally finite
list of variable children, including nonstandard model-valued indices. -/
theorem modelShallowFunction (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym depth : M) (vs : List (Bool × M)) :
    F (termDispatch vs.length first second (closeVariable first second))
      ![label,pair 2 (pair (vs.length : M) (pair sym (vec (vs.map variableInput))))+1,depth] =
      pair 2 (pair (vs.length : M) (pair sym (vec (vs.map (variableClosed label depth)))))+1 := by
  rw [modelFunction vs.length first second (closeVariable first second) hf hs]
  have h := modelMapList first second (closeVariable first second) hf hs label depth
    (vs.map variableInput)
  simp only [List.length_map] at h
  rw [h]
  congr 3
  congr 1
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro v hv
  exact modelVariableInput first second hf hs label depth v

#print axioms modelShallowFunction

/-- Identification with named internal constructors is deliberately isolated
behind the IΣ₁ model hypothesis. -/
theorem modelFunctionInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : Nat)
    (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym v depth : M) :
    F (termDispatch k first second child) ![label,qqFunc (k : M) sym v,depth] =
      qqFunc (k : M) sym (F (mapVector first second child k) ![label,v,depth]) := by
  simp only [qqFunc]
  exact modelFunction k first second child hf hs label sym v depth

theorem modelBoundInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : Nat)
    (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (termDispatch k first second child) ![label,qqBvar index,depth] =
      if index < depth then qqBvar index else qqBvar (index+1) := by
  simp only [qqBvar]
  exact modelBound k first second child hf hs label index depth

theorem modelFreeInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : Nat)
    (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (termDispatch k first second child) ![label,qqFvar index,depth] =
      if label = index then qqBvar depth else qqFvar index := by
  simp only [qqBvar,qqFvar]
  exact modelFree k first second child hf hs label index depth

#print axioms modelFunctionInternal
#print axioms modelBoundInternal
#print axioms modelFreeInternal

#print axioms modelFunction
#print axioms modelBound
#print axioms modelFree
end models
end PA194TermDispatch
