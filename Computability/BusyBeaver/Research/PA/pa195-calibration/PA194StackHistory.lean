import PA194StackCode
import DiophantineConsistency.PRAOpenInduction
import DiophantineConsistency.PRAAddition
import DiophantineConsistency.PRASubAddition

/-! Candidate-PRA operations for reverse-indexed recursive histories. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194StackHistory
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion PRAOpenInduction PRAAddition PRASubAddition PA194StackCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor PA195DecodedFields PA194ChildCodes

def shiftBody (tail : Code 1) : Semiformula language Nat 1 :=
  .rel Language.ORing.Rel.eq
    ![.func (dropCode tail) ![.func Code.succ ![.bvar 0], .fvar 0],
      .func (dropCode tail) ![.bvar 0, .func tail ![.fvar 0]]]

theorem shiftBody_open (tail : Code 1) : (shiftBody tail).Open := by
  simp [shiftBody, Semiformula.Open]

/-- Append the next computed value to the reversed history. `next` takes
the current index and the previous history. -/
def historyStep (next : Code 2) : Code 2 :=
  bin addCode (bin pairCode next (.proj 1)) (.comp oneCode (.nil 2))

def historyCode (next : Code 2) : Code 1 := .prec (.zero 0) (historyStep next)

/-- The value at a source code is computed from that code and its complete
history of earlier values. The update remains a supplied parameter. -/
def translationCode (next : Code 2) : Code 1 :=
  bin next (.proj 0) (historyCode next)

/-- Reverse index of child `j` in a history of length `n`: `n - (j+1)`. -/
def distanceCode : Code 2 :=
  bin subCode (.proj 0) (bin addCode (.proj 1) (.comp oneCode (.nil 2)))

/-- Given `[sourceCode, history]`, decode a child and read its previously
computed translation at the reverse index. -/
def childLookupCode (head tail child : Code 1) : Code 2 :=
  bin (lookupCode (stackComponent head) (stackComponent tail))
    (bin distanceCode (.proj 0) (PA194PathIterator.unary child (.proj 0))) (.proj 1)

/-- The history lookup at distance `k` from stage `j+k+1` retrieves the
value computed at stage `j`. -/
def reverseBody (next : Code 2) (head tail : Code 1) : Semiformula language Nat 1 :=
  .rel Language.ORing.Rel.eq
    ![.func (lookupCode (stackComponent head) (stackComponent tail))
        ![.bvar 0, .func (historyCode next)
          ![.func Code.succ ![.func addCode ![.fvar 0,.bvar 0]]]],
      .func next ![.fvar 0,.func (historyCode next) ![.fvar 0]]]

theorem reverseBody_open (next : Code 2) (head tail : Code 1) :
    (reverseBody next head tail).Open := by simp [reverseBody, Semiformula.Open]

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

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem shiftBody_eval (tail : Code 1) (i : M) (e : Nat → M) :
    (shiftBody tail).Eval ![i] e ↔
      F (dropCode tail) ![F Code.succ (fun _ => i),e 0] =
        F (dropCode tail) ![i,F tail (fun _ => e 0)] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![i] (shiftBody tail) ↔ _
  simp only [shiftBody, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : (fun j => Semiterm.val ![i] e
      (![(.func Code.succ ![.bvar 0] : Semiterm language Nat 1),.fvar 0] j)) =
      ![F Code.succ (fun _ => i),e 0] := by
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · change F Code.succ _ = _
      congr 1
      funext k
      exact Fin.cases rfl (fun l => Fin.elim0 l) k
    · exact Fin.cases rfl (fun l => Fin.elim0 l) k
  have h1 : (fun j => Semiterm.val ![i] e
      (![(.bvar 0 : Semiterm language Nat 1),.func tail ![.fvar 0]] j)) =
      ![i,F tail (fun _ => e 0)] := by
    funext j
    refine Fin.cases rfl (fun k => ?_) j
    refine Fin.cases ?_ (fun l => Fin.elim0 l) k
    change F tail _ = _
    congr 1
    funext l
    exact Fin.cases rfl (fun m => Fin.elim0 m) l
  simp only [Semiterm.val_func, Function.comp_def]
  rw [h0,h1]

/-- Iterated drop commutes with one additional leading tail, even for
nonstandard indices and arbitrary (possibly malformed) stack values. -/
theorem modelDropShift (tail : Code 1) (i v : M) :
    F (dropCode tail) ![i+1,v] = F (dropCode tail) ![i,F tail (fun _ => v)] := by
  let e : Nat → M := fun _ => v
  have main : (shiftBody tail).Eval ![i] e := by
    apply modelOpenInduction (M := M) (shiftBody tail) (shiftBody_open tail) e
    · apply (shiftBody_eval tail (F (Code.zero 0) Fin.elim0) e).mpr
      change F (dropCode tail) ![F Code.succ (fun _ => (0 : M)),v] =
        F (dropCode tail) ![(0 : M),F tail (fun _ => v)]
      rw [← modelAddOne]
      change F (dropCode tail) ![(0 : M)+1,v] =
        F (dropCode tail) ![(0 : M),F tail (fun _ => v)]
      rw [modelDropStep, modelDropBase, modelDropBase]
    · intro k hk
      apply (shiftBody_eval tail (F Code.succ (fun _ => k)) e).mpr
      have ih := (shiftBody_eval tail k e).mp hk
      change F (dropCode tail) ![F Code.succ (fun _ => k),v] =
        F (dropCode tail) ![k,F tail (fun _ => v)] at ih
      change F (dropCode tail) ![F Code.succ (fun _ => F Code.succ (fun _ => k)),v] =
        F (dropCode tail) ![F Code.succ (fun _ => k),F tail (fun _ => v)]
      rw [← modelAddOne, ← modelAddOne]
      rw [← modelAddOne] at ih
      change F (dropCode tail) ![(k+1)+1,v] =
        F (dropCode tail) ![k+1,F tail (fun _ => v)]
      change F (dropCode tail) ![k+1,v] =
        F (dropCode tail) ![k,F tail (fun _ => v)] at ih
      rw [modelDropStep tail (k+1) v,
          modelDropStep tail k (F tail (fun _ => v)), ← ih]
  have h := (shiftBody_eval tail i e).mp main
  change F (dropCode tail) ![F Code.succ (fun _ => i),v] =
    F (dropCode tail) ![i,F tail (fun _ => v)] at h
  rw [← modelAddOne] at h
  change F (dropCode tail) ![i+1,v] = F (dropCode tail) ![i,F tail (fun _ => v)] at h
  exact h

/-- Looking one cell farther into a pushed history recovers the previous
history's lookup, for every model index, not only standard numerals. -/
theorem modelLookupConsSucc (projHead projTail : Code 1)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) projTail)
    (i x rest : M) :
    F (lookupCode (stackComponent projHead) (stackComponent projTail))
      ![i+1,pair x rest+1] =
    F (lookupCode (stackComponent projHead) (stackComponent projTail)) ![i,rest] := by
  rw [modelLookupValue, modelDropShift, modelStackTail projTail htail, ← modelLookupValue]

/-- One primitive recursion stage pushes the next value and retains all
earlier stages as its tail. -/
theorem modelHistoryStep (next : Code 2) (n : M) :
    F (historyCode next) (fun _ => n+1) =
      pair (F next ![n,F (historyCode next) (fun _ => n)])
        (F (historyCode next) (fun _ => n)) + 1 := by
  change F (.prec (.zero 0) (historyStep next))
      (fun _ => F addCode ![n,F oneCode Fin.elim0]) = _
  rw [modelAddOne]
  have h := modelStep (M := M) (.zero 0) (historyStep next) (fun _ : Fin 1 => n)
  have hy : (fun _ : Fin 0 => n) = (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hy] at h
  have hs : Fin.cases (F Code.succ (fun _ => n)) (Fin.elim0 : Fin 0 → M) =
      (fun _ : Fin 1 => F Code.succ (fun _ => n)) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  change F (.prec (.zero 0) (historyStep next)) (fun _ => F Code.succ (fun _ => n)) =
    F (historyStep next) ![n,F (historyCode next) (fun _ => n)] at h
  rw [h,historyStep,modelBin,modelBin,modelPairCode,modelProjection]
  have hc : F (.comp oneCode (.nil 2)) ![n,F (historyCode next) (fun _ => n)] = (1 : M) := by
    rw [modelComposition]
    congr 1
    exact Subsingleton.elim _ _
  rw [hc]
  rfl

/-- The newest value of a recursive history is readable from its head. -/
theorem modelHistoryNewest (next : Code 2) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head) (n : M) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![0,F (historyCode next) (fun _ => n+1)] =
      F next ![n,F (historyCode next) (fun _ => n)] := by
  rw [modelHistoryStep, modelLookupZero head tail hhead]

/-- Earlier lookups persist under a new stage, with their reverse index raised
by one; the stage and index may both be nonstandard. -/
theorem modelHistoryEarlier (next : Code 2) (head tail : Code 1)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail) (n i : M) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![i+1,F (historyCode next) (fun _ => n+1)] =
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![i,F (historyCode next) (fun _ => n)] := by
  rw [modelHistoryStep,modelLookupConsSucc head tail htail]

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem reverseBody_eval (next : Code 2) (head tail : Code 1) (k : M) (e : Nat → M) :
    (reverseBody next head tail).Eval ![k] e ↔
      F (lookupCode (stackComponent head) (stackComponent tail))
        ![k,F (historyCode next) (fun _ => F Code.succ (fun _ => F addCode ![e 0,k]))] =
      F next ![e 0,F (historyCode next) (fun _ => e 0)] := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![k]
    (reverseBody next head tail) ↔ _
  simp only [reverseBody, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : (fun j => Semiterm.val ![k] e
      (![(.bvar 0 : Semiterm language Nat 1),.func (historyCode next)
        ![.func Code.succ ![.func addCode ![.fvar 0,.bvar 0]]]] j)) =
      ![k,F (historyCode next) (fun _ => F Code.succ (fun _ => F addCode ![e 0,k]))] := by
    funext j
    refine Fin.cases rfl (fun l => ?_) j
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change F (historyCode next) _ = _
    congr 1
    funext m
    refine Fin.cases ?_ (fun n => Fin.elim0 n) m
    change F Code.succ _ = _
    congr 1
    funext n
    refine Fin.cases ?_ (fun o => Fin.elim0 o) n
    change F addCode _ = _
    congr 1
    funext o
    refine Fin.cases rfl (fun p => ?_) o
    exact Fin.cases rfl (fun q => Fin.elim0 q) p
  have h1 : (fun j => Semiterm.val ![k] e
      (![(.fvar 0 : Semiterm language Nat 1),.func (historyCode next) ![.fvar 0]] j)) =
      ![e 0,F (historyCode next) (fun _ => e 0)] := by
    funext j
    refine Fin.cases rfl (fun l => ?_) j
    refine Fin.cases ?_ (fun m => Fin.elim0 m) l
    change F (historyCode next) _ = _
    congr 1
    funext m
    exact Fin.cases rfl (fun n => Fin.elim0 n) m
  simp only [Semiterm.val_func, Function.comp_def]
  rw [h0,h1]

/-- A value produced at any model stage remains available at every later
stage at the exact reverse index. Both `j` and `k` may be nonstandard. -/
theorem modelHistoryReverse (next : Code 2) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail) (j k : M) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![k,F (historyCode next) (fun _ => j+k+1)] =
      F next ![j,F (historyCode next) (fun _ => j)] := by
  let e : Nat → M := fun _ => j
  have main : (reverseBody next head tail).Eval ![k] e := by
    apply modelOpenInduction (M := M) (reverseBody next head tail)
      (reverseBody_open next head tail) e
    · apply (reverseBody_eval next head tail (0 : M) e).mpr
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![F (Code.zero 0) Fin.elim0,F (historyCode next) (fun _ => F Code.succ
          (fun _ => F addCode ![j,F (Code.zero 0) Fin.elim0]))] = F next ![j,F (historyCode next) (fun _ => j)]
      rw [modelAddZero, ← modelAddOne]
      exact modelHistoryNewest next head tail hhead j
    · intro i hi
      apply (reverseBody_eval next head tail (F Code.succ (fun _ => i)) e).mpr
      have ih := (reverseBody_eval next head tail i e).mp hi
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![i,F (historyCode next) (fun _ => F Code.succ (fun _ => F addCode ![j,i]))] =
          F next ![j,F (historyCode next) (fun _ => j)] at ih
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![F Code.succ (fun _ => i),F (historyCode next) (fun _ => F Code.succ
          (fun _ => F addCode ![j,F Code.succ (fun _ => i)]))] =
          F next ![j,F (historyCode next) (fun _ => j)]
      rw [modelAddSucc, ← modelAddOne, ← modelAddOne, ← modelAddOne] 
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![i+1,F (historyCode next) (fun _ => (j+i+1)+1)] =
          F next ![j,F (historyCode next) (fun _ => j)]
      rw [modelHistoryEarlier next head tail htail]
      rw [← modelAddOne] at ih
      change F (lookupCode (stackComponent head) (stackComponent tail))
        ![i,F (historyCode next) (fun _ => j+i+1)] =
          F next ![j,F (historyCode next) (fun _ => j)] at ih
      exact ih
  have h := (reverseBody_eval next head tail k e).mp main
  rw [← modelAddOne] at h
  change F (lookupCode (stackComponent head) (stackComponent tail))
    ![k,F (historyCode next) (fun _ => j+k+1)] =
      F next ![j,F (historyCode next) (fun _ => j)] at h
  exact h

/-- Every earlier model stage has a reverse index, including when either
stage is nonstandard. -/
theorem modelHistoryEarlierLt (next : Code 2) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail) (j n : M) (h : j < n) :
    ∃ k : M, n = j+k+1 ∧
      F (lookupCode (stackComponent head) (stackComponent tail))
        ![k,F (historyCode next) (fun _ => n)] =
        F next ![j,F (historyCode next) (fun _ => j)] := by
  obtain ⟨k,hk⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp h)
  have hn : n = j+k+1 := by rw [hk]; ac_rfl
  refine ⟨k,hn,?_⟩
  rw [hn]
  exact modelHistoryReverse next head tail hhead htail j k

/-- For each `j<n`, the explicit primitive-recursive distance code reads
the value produced at stage `j` from the model-length history at stage `n`. -/
theorem modelHistoryLookupEarlier (next : Code 2) (head tail : Code 1)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail) (j n : M) (h : j < n) :
    F (lookupCode (stackComponent head) (stackComponent tail))
      ![F distanceCode ![n,j],F (historyCode next) (fun _ => n)] =
      F next ![j,F (historyCode next) (fun _ => j)] := by
  obtain ⟨k,hk⟩ := le_iff_exists_add.mp (lt_iff_succ_le.mp h)
  have hn : n = j+k+1 := by rw [hk]; ac_rfl
  have hconst : F (.comp oneCode (.nil 2)) ![n,j] = (1 : M) := by
    rw [modelComposition]
    congr 1
    exact Subsingleton.elim _ _
  have hdist : F distanceCode ![n,j] = k := by
    rw [distanceCode, modelBin, modelBin, modelProjection, modelProjection, hconst]
    change F subCode ![n,j+1] = k
    rw [hk]
    exact modelSubAdd (j+1) k
  rw [hdist,hn]
  exact modelHistoryReverse next head tail hhead htail j k

/-- The first exact source decoder child reads its computed history value. -/
theorem modelHistoryFirstChild (next : Code 2) (head tail child : Code 1)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hchild : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) child) (n : M) (hn : 0 < n) :
    F (childLookupCode head tail child) ![n,F (historyCode next) (fun _ => n)] =
      F next ![first (n / 4),F (historyCode next) (fun _ => first (n / 4))] := by
  rw [childLookupCode, modelBin, modelBin, modelProjection,
      PA194PathIterator.modelUnary, modelProjection, modelProjection,
      modelFirstCode child hchild]
  exact modelHistoryLookupEarlier next head tail hhead htail _ n
    (decoded_fields_lt n hn).1

/-- The second exact source decoder child reads its computed history value. -/
theorem modelHistorySecondChild (next : Code 2) (head tail child : Code 1)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hchild : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) child) (n : M) (hn : 0 < n) :
    F (childLookupCode head tail child) ![n,F (historyCode next) (fun _ => n)] =
      F next ![second (n / 4),F (historyCode next) (fun _ => second (n / 4))] := by
  rw [childLookupCode, modelBin, modelBin, modelProjection,
      PA194PathIterator.modelUnary, modelProjection, modelProjection,
      modelSecondCode child hchild]
  exact modelHistoryLookupEarlier next head tail hhead htail _ n
    (decoded_fields_lt n hn).2

/-- The staged translation code evaluates the supplied update on the source
code and its previously computed history. -/
theorem modelTranslation (next : Code 2) (n : M) :
    F (translationCode next) (fun _ => n) =
      F next ![n,F (historyCode next) (fun _ => n)] := by
  rw [translationCode,modelBin,modelProjection]

/-- The stored first child is exactly the corresponding translation-code
value, for every positive, possibly nonstandard, source code. -/
theorem modelTranslationFirstChild (next : Code 2) (head tail child : Code 1)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hchild : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) child) (n : M) (hn : 0 < n) :
    F (childLookupCode head tail child) ![n,F (historyCode next) (fun _ => n)] =
      F (translationCode next) (fun _ => first (n / 4)) := by
  rw [modelHistoryFirstChild next head tail child hhead htail hchild n hn,
      modelTranslation]

/-- The analogous lookup theorem for the second decoded child. -/
theorem modelTranslationSecondChild (next : Code 2) (head tail child : Code 1)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hchild : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) child) (n : M) (hn : 0 < n) :
    F (childLookupCode head tail child) ![n,F (historyCode next) (fun _ => n)] =
      F (translationCode next) (fun _ => second (n / 4)) := by
  rw [modelHistorySecondChild next head tail child hhead htail hchild n hn,
      modelTranslation]

#print axioms modelDropShift
#print axioms modelLookupConsSucc
#print axioms modelHistoryStep
#print axioms modelHistoryNewest
#print axioms modelHistoryEarlier
#print axioms modelHistoryReverse
#print axioms modelHistoryEarlierLt
#print axioms modelHistoryLookupEarlier
#print axioms modelHistoryFirstChild
#print axioms modelHistorySecondChild
#print axioms modelTranslation
#print axioms modelTranslationFirstChild
#print axioms modelTranslationSecondChild
end models

/-- Candidate PRA supplies all four components required by the exact
first- and second-child history lookup theorems. -/
theorem PRA_has_historyComponents : ∃ head tail firstChild secondChild : Code 1,
    (PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head) ∧
    (PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail) ∧
    (PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) firstChild) ∧
    (PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) secondChild) := by
  obtain ⟨head,tail,hhead,htail⟩ := PRA_has_stackProjections
  obtain ⟨firstChild,_,hfirst⟩ := PRA_has_firstChildCode
  obtain ⟨secondChild,_,hsecond⟩ := PRA_has_secondChildCode
  exact ⟨head,tail,firstChild,secondChild,hhead,htail,hfirst,hsecond⟩

#print axioms PRA_has_historyComponents
end PA194StackHistory
