import PA194ParamHistory

/-! Candidate-PRA function-term child decoding and parameterized history. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace PA194TermHistory
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection
open PA194StackCode PA194ParamHistory PA194BranchSeed

def apply1 (outer inner : Code 1) : Code 1 := .comp outer (.cons inner (.nil 1))
/-- The function's argument-vector field, for an encoded function node. -/
def arguments (second : Code 1) : Code 1 :=
  apply1 second (apply1 second (stackComponent second))
def firstChild (first second : Code 1) : Code 1 :=
  apply1 (stackComponent first) (arguments second)
def secondChild (first second : Code 1) : Code 1 :=
  apply1 (stackComponent first) (apply1 (stackComponent second) (arguments second))

/-- Inputs: encoded enclosing term, closing label, binder depth, and history. -/
def childAt (head tail decoder : Code 1) : Code 4 :=
  bin (lookupCode (stackComponent head) (stackComponent tail))
    (bin PA194StackHistory.distanceCode (.proj 0)
      (PA194PathIterator.unary decoder (.proj 0))) (.proj 3)

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

theorem modelApply1 (f g : Code 1) (n : M) :
    F (apply1 f g) (fun _ => n) = F f (fun _ => F g (fun _ => n)) := by
  rw [apply1,modelComposition]
  congr 1
  funext i
  exact Fin.cases rfl (fun j => Fin.elim0 j) i

theorem modelArguments (second : Code 1)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (arity sym vec : M) :
    F (arguments second) (fun _ => pair 2 (pair arity (pair sym vec))+1) = vec := by
  rw [arguments,modelApply1,modelApply1,modelStackTail second hs]
  simp only [modelPi2Code second hs,pi₂_pair]

theorem modelFirst (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (arity sym child rest : M) :
    F (firstChild first second)
      (fun _ => pair 2 (pair arity (pair sym (pair child rest+1)))+1) = child := by
  rw [firstChild,modelApply1,modelArguments second hs,modelStackHead first hf]

theorem modelSecond (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (arity sym firstValue child rest : M) :
    F (secondChild first second)
      (fun _ => pair 2 (pair arity (pair sym (pair firstValue (pair child rest+1)+1)))+1) = child := by
  rw [secondChild,modelApply1,modelApply1,modelArguments second hs,
    modelStackTail second hs,modelStackHead first hf]

/-- A present first argument is strictly smaller than its enclosing function
node, without any standardness or well-formedness hypothesis on the fields. -/
theorem first_lt_function (arity sym child rest : M) :
    child < pair 2 (pair arity (pair sym (pair child rest+1)))+1 := by
  have h1 : child ≤ pair child rest := le_pair_left child rest
  have h2 : pair child rest ≤ pair child rest+1 := le_of_lt (lt_succ_iff_le.mpr le_rfl)
  have h3 : pair child rest+1 ≤ pair sym (pair child rest+1) := le_pair_right _ _
  have h4 : pair sym (pair child rest+1) ≤ pair arity (pair sym (pair child rest+1)) := le_pair_right _ _
  have h5 : pair arity (pair sym (pair child rest+1)) ≤ pair 2 (pair arity (pair sym (pair child rest+1))) := le_pair_right _ _
  exact lt_succ_iff_le.mpr (le_trans h1 (le_trans h2 (le_trans h3 (le_trans h4 h5))))

theorem second_lt_function (arity sym firstValue child rest : M) :
    child < pair 2 (pair arity (pair sym (pair firstValue (pair child rest+1)+1)))+1 := by
  have h1 : child ≤ pair child rest := le_pair_left child rest
  have h2 : pair child rest ≤ pair child rest+1 := le_of_lt (lt_succ_iff_le.mpr le_rfl)
  have h3 : pair child rest+1 ≤ pair firstValue (pair child rest+1) := le_pair_right _ _
  have h4 : pair firstValue (pair child rest+1) ≤ pair firstValue (pair child rest+1)+1 := le_of_lt (lt_succ_iff_le.mpr le_rfl)
  have h5 : pair firstValue (pair child rest+1)+1 ≤ pair sym (pair firstValue (pair child rest+1)+1) := le_pair_right _ _
  have h6 : pair sym (pair firstValue (pair child rest+1)+1) ≤ pair arity (pair sym (pair firstValue (pair child rest+1)+1)) := le_pair_right _ _
  have h7 : pair arity (pair sym (pair firstValue (pair child rest+1)+1)) ≤ pair 2 (pair arity (pair sym (pair firstValue (pair child rest+1)+1))) := le_pair_right _ _
  exact lt_succ_iff_le.mpr (le_trans h1 (le_trans h2 (le_trans h3 (le_trans h4 (le_trans h5 (le_trans h6 h7))))))

/-- Lookup the first function child at nonstandard model stages, preserving
both arbitrary model-valued closing parameters. -/
theorem modelFirstLookup (next : Code 4) (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (arity sym child rest label depth : M) :
    let n := pair 2 (pair arity (pair sym (pair child rest+1)))+1
    F (childAt first second (firstChild first second))
      ![n,label,depth,F (historyCode next) ![n,label,depth]] =
      F (translationCode next) ![child,label,depth] := by
  dsimp only
  rw [childAt,modelBin,modelBin,modelProjection,
    PA194PathIterator.modelUnary,modelProjection,modelProjection]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_three]
  rw [modelFirst first second hf hs]
  exact modelLookupEarlier next first second hf hs child _ label depth
    (first_lt_function arity sym child rest)

/-- Lookup the second present function child under the same assumptions. -/
theorem modelSecondLookup (next : Code 4) (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (arity sym firstValue child rest label depth : M) :
    let n := pair 2 (pair arity (pair sym (pair firstValue (pair child rest+1)+1)))+1
    F (childAt first second (secondChild first second))
      ![n,label,depth,F (historyCode next) ![n,label,depth]] =
      F (translationCode next) ![child,label,depth] := by
  dsimp only
  rw [childAt,modelBin,modelBin,modelProjection,
    PA194PathIterator.modelUnary,modelProjection,modelProjection]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_three]
  rw [modelSecond first second hf hs]
  exact modelLookupEarlier next first second hf hs child _ label depth
    (second_lt_function arity sym firstValue child rest)

#print axioms modelFirstLookup
#print axioms modelSecondLookup

#print axioms modelFirst
#print axioms modelSecond
#print axioms first_lt_function
#print axioms second_lt_function
end models
end PA194TermHistory
