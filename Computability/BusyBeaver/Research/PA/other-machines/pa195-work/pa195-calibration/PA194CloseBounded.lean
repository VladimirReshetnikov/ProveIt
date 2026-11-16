import PA194TermDispatch

/-! Externally bounded-depth closing for arithmetic terms. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194CloseBounded
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194VariableDispatch PA194StackCode PA194NumeralCode PA194CloseFunction
  PA194CloseVariable PA194BranchSeed

def funcArity (first second : Code 1) : Code 3 := post first (component second)
def functionByArity (first second : Code 1) (child : Code 3) : Code 3 :=
  selectAmong (bin equalityCode (funcArity first second) (.zero 3))
    (functionDispatch 0 first second child)
    (selectAmong (bin equalityCode (funcArity first second) (numeralCode 3 1))
      (functionDispatch 1 first second child) (functionDispatch 2 first second child))
def termStep (first second : Code 1) (child : Code 3) : Code 3 :=
  selectAmong (bin equalityCode (component first) (numeralCode 3 2))
    (functionByArity first second child) (closeVariable first second)
/-- This family has one fixed Code per externally supplied depth bound. -/
def closeDepth (first second : Code 1) : Nat → Code 3
  | 0 => closeVariable first second
  | n+1 => termStep first second (closeDepth first second n)

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

theorem modelArity (k : Nat) (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym v depth : M) :
    F (funcArity first second) ![label,pair 2 (pair (k : M) (pair sym v))+1,depth] = (k : M) := by
  rw [funcArity,modelPost,modelComponent]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [modelStackTail second hs,modelPi1Code first hf,pi₁_pair]

theorem modelByArity (first second : Code 1) (child : Code 3) (e : Fin 3 → M) :
    F (functionByArity first second child) e =
      if F (funcArity first second) e = 0 then F (functionDispatch 0 first second child) e
      else if F (funcArity first second) e = 1 then F (functionDispatch 1 first second child) e
      else F (functionDispatch 2 first second child) e := by
  rw [functionByArity,modelChooseEqual]
  have hz : F (.zero 3) e = (0 : M) := PRAMultiplication.modelZero e
  rw [hz]
  split
  · rfl
  · rw [modelChooseEqual,modelNumeralCode]
    norm_num

theorem modelStep (first second : Code 1) (child : Code 3) (e : Fin 3 → M) :
    F (termStep first second child) e =
      if F (component first) e = 2 then F (functionByArity first second child) e
      else F (closeVariable first second) e := by
  rw [termStep,modelChooseEqual,modelNumeralCode]
  norm_num

theorem modelFunction (k : Nat) (hk : k ≤ 2) (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym v depth : M) :
    F (termStep first second child) ![label,pair 2 (pair (k : M) (pair sym v))+1,depth] =
      pair 2 (pair (k : M) (pair sym (F (mapVector first second child k) ![label,v,depth]))) + 1 := by
  have ht : F (component first) ![label,pair 2 (pair (k : M) (pair sym v))+1,depth] = (2 : M) := by
    rw [modelComponent]
    change F (stackComponent first) (fun _ => pair 2 (pair (k : M) (pair sym v))+1) = 2
    exact modelStackHead first hf 2 _
  rw [modelStep,ht,if_pos rfl,modelByArity,modelArity k first second hf hs]
  rcases k with _ | k
  · simpa using modelFunctionDispatch 0 first second child hf hs label sym v depth
  rcases k with _ | k
  · simpa using modelFunctionDispatch 1 first second child hf hs label sym v depth
  rcases k with _ | k
  · simpa using modelFunctionDispatch 2 first second child hf hs label sym v depth
  · omega

theorem modelBound (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (termStep first second child) ![label,pair 0 index+1,depth] =
      if index < depth then pair 0 index+1 else pair 0 (index+1)+1 := by
  have ht : F (component first) ![label,pair 0 index+1,depth] = (0 : M) := by
    rw [modelComponent]
    change F (stackComponent first) (fun _ => pair 0 index+1) = 0
    exact modelStackHead first hf 0 _
  have hn : (0 : M) ≠ 2 := ne_of_lt (by norm_num)
  rw [modelStep,ht,if_neg hn,PA194VariableDispatch.modelBound first second hf hs]

theorem modelFree (first second : Code 1) (child : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label index depth : M) :
    F (termStep first second child) ![label,pair 1 index+1,depth] =
      if label = index then pair 0 depth+1 else pair 1 index+1 := by
  have ht : F (component first) ![label,pair 1 index+1,depth] = (1 : M) := by
    rw [modelComponent]
    change F (stackComponent first) (fun _ => pair 1 index+1) = 1
    exact modelStackHead first hf 1 _
  have hn : (1 : M) ≠ 2 := ne_of_lt (by norm_num)
  rw [modelStep,ht,if_neg hn,PA194VariableDispatch.modelFree first second hf hs]

/-- Externally finite arithmetic-term shapes. Fields are model values. -/
inductive Shape (V : Type) where
  | bound (index : V)
  | free (index : V)
  | nullary (symbol : V)
  | unary (symbol : V) (arg : Shape V)
  | binary (symbol : V) (left right : Shape V)

def Shape.height : Shape M → Nat
  | .bound _ => 0
  | .free _ => 0
  | .nullary _ => 1
  | .unary _ x => x.height+1
  | .binary _ x y => max x.height y.height+1

noncomputable def Shape.encoded : Shape M → M
  | .bound i => pair 0 i + 1
  | .free i => pair 1 i + 1
  | .nullary f => pair 2 (pair 0 (pair f 0)) + 1
  | .unary f x => pair 2 (pair 1 (pair f (vec [x.encoded]))) + 1
  | .binary f x y => pair 2 (pair 2 (pair f (vec [x.encoded,y.encoded]))) + 1

noncomputable def Shape.closed (label depth : M) : Shape M → M
  | .bound i => if i < depth then pair 0 i + 1 else pair 0 (i+1) + 1
  | .free i => if label = i then pair 0 depth + 1 else pair 1 i + 1
  | .nullary f => pair 2 (pair 0 (pair f 0)) + 1
  | .unary f x => pair 2 (pair 1 (pair f (vec [x.closed label depth]))) + 1
  | .binary f x y => pair 2 (pair 2 (pair f (vec [x.closed label depth,y.closed label depth]))) + 1

/-- For any external finite shape of bounded depth, its field values and
closing parameters may be arbitrary, including nonstandard model elements. -/
theorem modelCloseDepth (h : Nat) (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth : M) (t : Shape M) (ht : t.height ≤ h) :
    F (closeDepth first second h) ![label,t.encoded,depth] = t.closed label depth := by
  induction h generalizing t with
  | zero =>
    cases t with
    | bound i => exact PA194VariableDispatch.modelBound first second hf hs label i depth
    | free i => exact PA194VariableDispatch.modelFree first second hf hs label i depth
    | nullary f => simp [Shape.height] at ht
    | unary f x => simp [Shape.height] at ht
    | binary f x y => simp [Shape.height] at ht
  | succ h ih =>
    cases t with
    | bound i => exact modelBound first second (closeDepth first second h) hf hs label i depth
    | free i => exact modelFree first second (closeDepth first second h) hf hs label i depth
    | nullary f =>
      simpa [closeDepth,Shape.encoded,Shape.closed,vec,modelMapZero] using
        modelFunction 0 (by decide) first second (closeDepth first second h) hf hs label f (0 : M) depth
    | unary f x =>
      have hx : x.height ≤ h := by simp [Shape.height] at ht; omega
      have hi := ih x hx
      have hm := modelMapList first second (closeDepth first second h) hf hs label depth [x.encoded]
      simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil] at hm
      simp only [hi] at hm
      change F (termStep first second (closeDepth first second h)) ![label,
        pair 2 (pair 1 (pair f (vec [x.encoded])))+1,depth] = _
      have hstep := modelFunction 1 (by decide) first second (closeDepth first second h) hf hs label f (vec [x.encoded]) depth
      norm_num at hstep hm
      rw [hstep,hm]
      rfl
    | binary f x y =>
      have hx : x.height ≤ h := by simp [Shape.height] at ht; omega
      have hy : y.height ≤ h := by simp [Shape.height] at ht; omega
      have hix := ih x hx
      have hiy := ih y hy
      have hm := modelMapList first second (closeDepth first second h) hf hs label depth [x.encoded,y.encoded]
      simp only [List.length_cons, List.length_nil, List.map_cons, List.map_nil] at hm
      simp only [hix,hiy] at hm
      change F (termStep first second (closeDepth first second h)) ![label,
        pair 2 (pair 2 (pair f (vec [x.encoded,y.encoded])))+1,depth] = _
      have hstep := modelFunction 2 (by decide) first second (closeDepth first second h) hf hs label f (vec [x.encoded,y.encoded]) depth
      norm_num at hstep hm
      rw [hstep,hm]
      rfl

#print axioms modelCloseDepth

#print axioms modelFunction
#print axioms modelBound
#print axioms modelFree
end models
end PA194CloseBounded
