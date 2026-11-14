import PA194VariableDispatch
import PA194QuadCode
import PA194TagCode
import PA194NumeralCode

/-! Fixed-arity function-node closing with a supplied child operation. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194CloseFunction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection
open PA194VariableDispatch PA194StackCode PA194TagCode PA194QuadCode PA194NumeralCode PA194BranchSeed

/-- `[label, vector, depth]` mapped over a fixed externally specified arity.
The child operation itself remains an explicit input. -/
def childResult (first : Code 1) (close : Code 3) : Code 3 :=
  .comp close (.cons (.proj 0) (.cons (component first) (.cons (.proj 2) (.nil 3))))
def tailInput (second : Code 1) : Code 3 := component second
def mapVector (first second : Code 1) (close : Code 3) : Nat → Code 3
  | 0 => .zero 3
  | k+1 => bin tagCode (childResult first close)
      (.comp (mapVector first second close k)
        (.cons (.proj 0) (.cons (tailInput second) (.cons (.proj 2) (.nil 3)))))
/-- Inputs are label, symbol, argument vector, and binder depth. -/
def functionNode (k : Nat) (first second : Code 1) (close : Code 3) : Code 4 :=
  let mapped : Code 4 := .comp (mapVector first second close k)
    (.cons (.proj 0) (.cons (.proj 2) (.cons (.proj 3) (.nil 4))))
  .comp quadCode (.cons (numeralCode 4 2) (.cons (numeralCode 4 k)
    (.cons (.proj 1) (.cons mapped (.nil 4)))))

/-- Apply a unary certified pairing projection to a three-argument code. -/
def post (proj : Code 1) (x : Code 3) : Code 3 := .comp proj (.cons x (.nil 3))
def funcTail (second : Code 1) : Code 3 := post second (component second)
def funcSymbol (first second : Code 1) : Code 3 := post first (funcTail second)
def funcArguments (second : Code 1) : Code 3 := post second (funcTail second)
/-- Decode an actual encoded function node, then traverse the fixed arity. -/
def functionDispatch (k : Nat) (first second : Code 1) (close : Code 3) : Code 3 :=
  .comp (functionNode k first second close)
    (.cons (.proj 0) (.cons (funcSymbol first second)
      (.cons (funcArguments second) (.cons (.proj 2) (.nil 3)))))

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

theorem modelChild (first : Code 1) (close : Code 3) (e : Fin 3 → M) :
    F (childResult first close) e = F close ![e 0,F (component first) e,e 2] := by
  rw [childResult,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelProjection 0 e
  · refine Fin.cases rfl (fun k => ?_) j
    exact Fin.cases (modelProjection 2 e) (fun l => Fin.elim0 l) k

theorem modelMapZero (first second : Code 1) (close : Code 3) (e : Fin 3 → M) :
    F (mapVector first second close 0) e = 0 := PRAMultiplication.modelZero e

theorem modelMapSucc (first second : Code 1) (close : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (k : Nat) (label x rest depth : M) :
    F (mapVector first second close (k+1)) ![label,pair x rest + 1,depth] =
      pair (F close ![label,x,depth]) (F (mapVector first second close k) ![label,rest,depth]) + 1 := by
  rw [mapVector,modelBin,modelTagValue,modelChild,modelComponent]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  rw [modelStackHead first hf]
  rw [modelComposition]
  have hv : (fun i : Fin 3 => F (getCode
      (.cons (.proj 0) (.cons (tailInput second) (.cons (.proj 2) (.nil 3)))) i)
      ![label,pair x rest + 1,depth]) = ![label,rest,depth] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection 0 _
    · refine Fin.cases ?_ (fun k => ?_) j
      · change F (tailInput second) ![label,pair x rest + 1,depth] = rest
        rw [tailInput,modelComponent]
        simp only [Matrix.cons_val_one]
        exact modelStackTail second hs x rest
      · exact Fin.cases (modelProjection 2 _) (fun l => Fin.elim0 l) k
  rw [hv]
  rfl

noncomputable def vec (xs : List M) : M := xs.foldr (fun x y => pair x y + 1) 0

theorem modelMapList (first second : Code 1) (close : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth : M) (xs : List M) :
    F (mapVector first second close xs.length) ![label,vec xs,depth] =
      vec (xs.map (fun x => F close ![label,x,depth])) := by
  induction xs with
  | nil => simp [vec,modelMapZero]
  | cons x xs ih =>
    change F (mapVector first second close (xs.length+1)) ![label,pair x (vec xs)+1,depth] =
      pair (F close ![label,x,depth]) (vec (xs.map (fun y => F close ![label,y,depth]))) + 1
    rw [modelMapSucc first second close hf hs,ih]

/-- Rebuild a function node after applying the supplied child operation to the
externally fixed number of arguments. -/
theorem modelFunctionNode (k : Nat) (first second : Code 1) (close : Code 3)
    (label sym v depth : M) :
    F (functionNode k first second close) ![label,sym,v,depth] =
      pair 2 (pair (k : M) (pair sym (F (mapVector first second close k) ![label,v,depth]))) + 1 := by
  rw [functionNode,modelComposition]
  have hm : F (.comp (mapVector first second close k)
      (.cons (.proj 0) (.cons (.proj 2) (.cons (.proj 3) (.nil 4)))) : Code 4)
      ![label,sym,v,depth] = F (mapVector first second close k) ![label,v,depth] := by
    rw [modelComposition]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection 0 _
    · refine Fin.cases ?_ (fun l => ?_) j
      · exact modelProjection 2 _
      · exact Fin.cases (modelProjection 3 _) (fun m => Fin.elim0 m) l
  have hv : (fun i : Fin 4 => F (getCode
      (.cons (numeralCode 4 2) (.cons (numeralCode 4 k)
      (.cons (.proj 1) (.cons (.comp (mapVector first second close k)
      (.cons (.proj 0) (.cons (.proj 2) (.cons (.proj 3) (.nil 4))))) (.nil 4))))) i)
      ![label,sym,v,depth]) = ![(2 : M),(k : M),sym,F (mapVector first second close k) ![label,v,depth]] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelNumeralCode 4 2 _
    · refine Fin.cases ?_ (fun l => ?_) j
      · exact modelNumeralCode 4 k _
      · refine Fin.cases ?_ (fun m => ?_) l
        · exact modelProjection 1 _
        · exact Fin.cases hm (fun n => Fin.elim0 n) m
  rw [hv,modelQuadValue]

theorem modelFunctionList (first second : Code 1) (close : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym depth : M) (xs : List M) :
    F (functionNode xs.length first second close) ![label,sym,vec xs,depth] =
      pair 2 (pair (xs.length : M) (pair sym (vec (xs.map (fun x => F close ![label,x,depth]))))) + 1 := by
  rw [modelFunctionNode, modelMapList first second close hf hs]

theorem modelFunctionInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (k : Nat)
    (first second : Code 1) (close : Code 3) (label sym v depth : M) :
    F (functionNode k first second close) ![label,sym,v,depth] =
      qqFunc (k : M) sym (F (mapVector first second close k) ![label,v,depth]) := by
  rw [modelFunctionNode]
  rfl

theorem modelPost (proj : Code 1) (x : Code 3) (e : Fin 3 → M) :
    F (post proj x) e = F proj (fun _ => F x e) := by
  rw [post,modelComposition]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem modelFunctionDispatch (k : Nat) (first second : Code 1) (close : Code 3)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym v depth : M) :
    F (functionDispatch k first second close)
      ![label,pair 2 (pair (k : M) (pair sym v))+1,depth] =
      pair 2 (pair (k : M) (pair sym (F (mapVector first second close k) ![label,v,depth]))) + 1 := by
  let e : Fin 3 → M := ![label,pair 2 (pair (k : M) (pair sym v))+1,depth]
  have hp : F (component second) e = pair (k : M) (pair sym v) := by
    rw [modelComponent]
    change F (stackComponent second) (fun _ => pair 2 (pair (k : M) (pair sym v))+1) = _
    exact modelStackTail second hs 2 _
  have ht : F (funcTail second) e = pair sym v := by
    rw [funcTail,modelPost,hp,modelPi2Code second hs,pi₂_pair]
  have hsym : F (funcSymbol first second) e = sym := by
    rw [funcSymbol,modelPost,ht,modelPi1Code first hf,pi₁_pair]
  have hv : F (funcArguments second) e = v := by
    rw [funcArguments,modelPost,ht,modelPi2Code second hs,pi₂_pair]
  change F (functionDispatch k first second close) e = _
  rw [functionDispatch,modelComposition]
  have he : (fun i : Fin 4 => F (getCode
    (.cons (.proj 0) (.cons (funcSymbol first second)
      (.cons (funcArguments second) (.cons (.proj 2) (.nil 3))))) i) e) =
    ![label,sym,v,depth] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact modelProjection 0 e
    · refine Fin.cases ?_ (fun l => ?_) j
      · exact hsym
      · refine Fin.cases ?_ (fun m => ?_) l
        · exact hv
        · exact Fin.cases (modelProjection 2 e) (fun n => Fin.elim0 n) m
  rw [he,modelFunctionNode]

#print axioms modelFunctionDispatch

/-- A `false` flag encodes a bound variable and `true` a free variable. -/
noncomputable def variableInput (v : Bool × M) : M :=
  pair (if v.1 then 1 else 0) v.2 + 1

noncomputable def variableClosed (label depth : M) (v : Bool × M) : M :=
  if v.1 then (if label = v.2 then pair 0 depth + 1 else pair 1 v.2 + 1)
  else (if v.2 < depth then pair 0 v.2 + 1 else pair 0 (v.2+1) + 1)

theorem modelVariableInput (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth : M) (v : Bool × M) :
    F (closeVariable first second) ![label,variableInput v,depth] = variableClosed label depth v := by
  rcases v with ⟨b,x⟩
  cases b
  · exact modelBound first second hf hs label x depth
  · exact modelFree first second hf hs label x depth

/-- A complete one-level function case: its argument nodes are arbitrary bound
or free variables with arbitrary model-valued indices. -/
theorem modelShallowFunction (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym depth : M) (vs : List (Bool × M)) :
    F (functionNode vs.length first second (closeVariable first second))
      ![label,sym,vec (vs.map variableInput),depth] =
      pair 2 (pair (vs.length : M) (pair sym (vec (vs.map (variableClosed label depth))))) + 1 := by
  have h := modelFunctionList first second (closeVariable first second) hf hs label sym depth
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

/-- Closing an encoded function term whose children are variable nodes. -/
theorem modelShallowDispatch (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label sym depth : M) (vs : List (Bool × M)) :
    F (functionDispatch vs.length first second (closeVariable first second))
      ![label,pair 2 (pair (vs.length : M) (pair sym (vec (vs.map variableInput)))) + 1,depth] =
      pair 2 (pair (vs.length : M) (pair sym (vec (vs.map (variableClosed label depth))))) + 1 := by
  rw [modelFunctionDispatch vs.length first second (closeVariable first second) hf hs]
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

#print axioms modelShallowDispatch

#print axioms modelVariableInput
#print axioms modelShallowFunction

#print axioms modelFunctionNode
#print axioms modelFunctionList
#print axioms modelFunctionInternal

#print axioms modelMapZero
#print axioms modelMapSucc
#print axioms modelMapList
end models
end PA194CloseFunction
