import PA194StackHistory
import PA194DispatchCode

/-! History-aware PA194 source dispatch, parameterized by the remaining
formula constructors. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194HistoryDispatch
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAEqualityCode PRASelectCode PRABooleanOps
  PA194NumeralCode PA194TagDecoder PA194StackHistory PA194StackCode PA194ChildCodes
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

/-- Equality test for two two-variable PR codes. -/
def equal2 (x y : Code 2) : Code 2 := bin equalityCode x y

def tag2 (tag : Code 1) : Code 2 := PA194PathIterator.unary tag (.proj 0)

def tagIs2 (tag : Code 1) (k : Nat) : Code 2 := equal2 (tag2 tag) (numeralCode 2 k)

/-- `[source, history]` dispatch. Branches may depend on both arguments. -/
def historyDispatch (tag : Code 1) (truth implication membership universal equality : Code 2) : Code 2 :=
  selectAmong (equal2 (.proj 0) (.zero 2)) truth
    (selectAmong (tagIs2 tag 1) membership
      (selectAmong (tagIs2 tag 2) universal
        (selectAmong (tagIs2 tag 3) equality implication)))

/-- The implication branch consumes the two previously translated children. -/
def implicationBranch (head tail firstChild secondChild : Code 1) (imp : Code 2) : Code 2 :=
  bin imp (childLookupCode head tail firstChild) (childLookupCode head tail secondChild)

/-- The universal constructor transposes the source pair: its binder is the
second field, and its body is the first field. -/
def universalBranch (head tail firstChild secondChild : Code 1) (forallOp : Code 2) : Code 2 :=
  bin forallOp (PA194PathIterator.unary secondChild (.proj 0)) (childLookupCode head tail firstChild)

/-- The missing implication and binder-closing implementations are explicit
binary code parameters; the three other branches are unary source-code
functions lifted over the ignored history. -/
def sourceUpdate (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2) : Code 2 :=
  historyDispatch tag (PA194PathIterator.unary truth (.proj 0))
    (implicationBranch head tail firstChild secondChild imp)
    (PA194PathIterator.unary membership (.proj 0))
    (universalBranch head tail firstChild secondChild forallOp)
    (PA194PathIterator.unary equality (.proj 0))

/-- A complete course-of-values recursion parameterized by its remaining
formula constructors. -/
def sourceTranslation (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2) : Code 1 :=
  translationCode (sourceUpdate tag head tail firstChild secondChild truth membership equality imp forallOp)

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

theorem modelChooseEq2 (x y yes no : Code 2) (e : Fin 2 → M) :
    F (selectAmong (equal2 x y) yes no) e =
      if F x e = F y e then F yes e else F no e := by
  rw [modelSelectAmong,equal2,modelBin]
  have hb := modelEqualityCode (F x e) (F y e)
  by_cases he : F x e = F y e
  · have hone := hb.2.mpr he
    simp only [he] at hone
    simp only [he, if_pos]
    rw [hone]
    exact modelSelectOne _ _
  · simp only [he, if_false]
    have hz : F equalityCode ![F x e,F y e] = F (Code.zero 0) Fin.elim0 := by
      rcases hb.1 with hz | ho
      · exact hz
      · exact False.elim (he (hb.2.mp ho))
    rw [hz]
    exact modelSelectZero _ _

theorem modelHistoryDispatch (tag : Code 1)
    (truth implication membership universal equality : Code 2) (n hist : M) :
    F (historyDispatch tag truth implication membership universal equality) ![n,hist] =
      if n = 0 then F truth ![n,hist]
      else if F tag (fun _ => n) = ((1 : Nat) : M) then F membership ![n,hist]
      else if F tag (fun _ => n) = ((2 : Nat) : M) then F universal ![n,hist]
      else if F tag (fun _ => n) = ((3 : Nat) : M) then F equality ![n,hist]
      else F implication ![n,hist] := by
  rw [historyDispatch,modelChooseEq2,modelProjection,PRAMultiplication.modelZero]
  change (if n = 0 then _ else _) = _
  split
  · rfl
  · simp only [tagIs2,tag2]
    rw [modelChooseEq2,modelNumeralCode,PA194PathIterator.modelUnary,modelProjection]
    simp only [Matrix.cons_val_zero]
    split
    · rfl
    · rw [modelChooseEq2,modelNumeralCode,PA194PathIterator.modelUnary,modelProjection]
      simp only [Matrix.cons_val_zero]
      split
      · rfl
      · rw [modelChooseEq2,modelNumeralCode,PA194PathIterator.modelUnary,modelProjection]
        simp only [Matrix.cons_val_zero]
        rfl

theorem modelHistoryDispatchTagged (tag : Code 1)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (truth implication membership universal equality : Code 2) (n hist : M) :
    F (historyDispatch tag truth implication membership universal equality) ![n,hist] =
      if n = 0 then F truth ![n,hist]
      else if n % 4 = ((1 : Nat) : M) then F membership ![n,hist]
      else if n % 4 = ((2 : Nat) : M) then F universal ![n,hist]
      else if n % 4 = ((3 : Nat) : M) then F equality ![n,hist]
      else F implication ![n,hist] := by
  rw [modelHistoryDispatch,modelTagCode tag htag]

/-- The implication update applies the supplied constructor to the two
recursive translation values, including at nonstandard model codes. -/
theorem modelImplicationBranch (next : Code 2) (head tail firstChild secondChild : Code 1)
    (imp : Code 2)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) (hn : 0 < n) :
    F (implicationBranch head tail firstChild secondChild imp)
      ![n,F (historyCode next) (fun _ => n)] =
      F imp ![F (translationCode next) (fun _ => first (n / 4)),
              F (translationCode next) (fun _ => second (n / 4))] := by
  rw [implicationBranch,modelBin,
    modelTranslationFirstChild next head tail firstChild hhead htail hfirst n hn,
    modelTranslationSecondChild next head tail secondChild hhead htail hsecond n hn]

/-- The universal update passes the second field as binder and the first
field's recursive translation as body. -/
theorem modelUniversalBranch (next : Code 2) (head tail firstChild secondChild : Code 1)
    (forallOp : Code 2)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) (hn : 0 < n) :
    F (universalBranch head tail firstChild secondChild forallOp)
      ![n,F (historyCode next) (fun _ => n)] =
      F forallOp ![second (n / 4),F (translationCode next) (fun _ => first (n / 4))] := by
  rw [universalBranch,modelBin,PA194PathIterator.modelUnary,modelProjection,
    modelSecondCode secondChild hsecond,
    modelTranslationFirstChild next head tail firstChild hhead htail hfirst n hn]
  rfl

/-- A nonzero tag-zero source formula selects the implication update. -/
theorem modelUpdateImplication
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (n hist : M) (hn : 0 < n) (hmod : n % 4 = 0) :
    F (sourceUpdate tag head tail firstChild secondChild truth membership equality imp forallOp) ![n,hist] =
      F (implicationBranch head tail firstChild secondChild imp) ![n,hist] := by
  rw [sourceUpdate,modelHistoryDispatchTagged tag htag]
  have h0 : n ≠ 0 := ne_of_gt hn
  have h01 : (0 : M) ≠ ((1 : Nat) : M) := by norm_num
  have h02 : (0 : M) ≠ ((2 : Nat) : M) := by norm_num
  have h03 : (0 : M) ≠ ((3 : Nat) : M) := by norm_num
  simp only [h0,if_false,hmod,h01,h02,h03]

/-- A tag-two source formula selects the universal update. -/
theorem modelUpdateUniversal
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (n hist : M) (hn : 0 < n) (hmod : n % 4 = ((2 : Nat) : M)) :
    F (sourceUpdate tag head tail firstChild secondChild truth membership equality imp forallOp) ![n,hist] =
      F (universalBranch head tail firstChild secondChild forallOp) ![n,hist] := by
  rw [sourceUpdate,modelHistoryDispatchTagged tag htag]
  have h0 : n ≠ 0 := ne_of_gt hn
  have h21 : ((2 : Nat) : M) ≠ ((1 : Nat) : M) := by norm_num
  simp only [h0,if_false,hmod,h21,if_true]

/-- The parameterized course-of-values translator satisfies its implication
recursion equation for every nonzero tag-zero model code. -/
theorem modelTranslationImplication
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) (hn : 0 < n) (hmod : n % 4 = 0) :
    let tr := sourceTranslation tag head tail firstChild secondChild truth membership equality imp forallOp
    F tr (fun _ => n) =
      F imp ![F tr (fun _ => first (n / 4)),F tr (fun _ => second (n / 4))] := by
  dsimp only
  rw [sourceTranslation,modelTranslation,
    modelUpdateImplication tag head tail firstChild secondChild truth membership equality imp forallOp
      htag n _ hn hmod,
    modelImplicationBranch _ head tail firstChild secondChild imp hhead htail hfirst hsecond n hn]

/-- The tag-two recursion applies the supplied universal constructor to the
second source field and the first field's recursively translated body. -/
theorem modelTranslationUniversal
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) (hn : 0 < n) (hmod : n % 4 = ((2 : Nat) : M)) :
    let tr := sourceTranslation tag head tail firstChild secondChild truth membership equality imp forallOp
    F tr (fun _ => n) =
      F forallOp ![second (n / 4),F tr (fun _ => first (n / 4))] := by
  dsimp only
  rw [sourceTranslation,modelTranslation,
    modelUpdateUniversal tag head tail firstChild secondChild truth membership equality imp forallOp
      htag n _ hn hmod,
    modelUniversalBranch _ head tail firstChild secondChild forallOp hhead htail hfirst hsecond n hn]

/-- Code zero selects the supplied truth translation, independently of its
also having implication tag zero. -/
theorem modelTranslationZero
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2) :
    F (sourceTranslation tag head tail firstChild secondChild truth membership equality imp forallOp)
      (fun _ => (0 : M)) = F truth (fun _ => (0 : M)) := by
  rw [sourceTranslation,modelTranslation,sourceUpdate,modelHistoryDispatch]
  simp only [if_true]
  rw [PA194PathIterator.modelUnary,modelProjection]
  rfl

/-- A tag-one code selects the supplied membership translation. -/
theorem modelTranslationMembership
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (n : M) (hn : 0 < n) (hmod : n % 4 = ((1 : Nat) : M)) :
    F (sourceTranslation tag head tail firstChild secondChild truth membership equality imp forallOp)
      (fun _ => n) = F membership (fun _ => n) := by
  rw [sourceTranslation,modelTranslation,sourceUpdate,modelHistoryDispatchTagged tag htag]
  have h0 : n ≠ 0 := ne_of_gt hn
  simp only [h0,if_false,hmod,if_true]
  rw [PA194PathIterator.modelUnary,modelProjection]
  rfl

/-- A tag-three code selects the supplied equality translation. -/
theorem modelTranslationEquality
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (n : M) (hn : 0 < n) (hmod : n % 4 = ((3 : Nat) : M)) :
    F (sourceTranslation tag head tail firstChild secondChild truth membership equality imp forallOp)
      (fun _ => n) = F equality (fun _ => n) := by
  rw [sourceTranslation,modelTranslation,sourceUpdate,modelHistoryDispatchTagged tag htag]
  have h0 : n ≠ 0 := ne_of_gt hn
  have h31 : ((3 : Nat) : M) ≠ ((1 : Nat) : M) := by norm_num
  have h32 : ((3 : Nat) : M) ≠ ((2 : Nat) : M) := by norm_num
  simp only [h0,if_false,hmod,h31,h32,if_true]
  rw [PA194PathIterator.modelUnary,modelProjection]
  rfl

/-- Exact universal constructor `U(a,b)=4*cantor(b,a)+2`: its label is `a`
and its recursively translated body is `b`. -/
theorem modelTranslationUniversalConstructor
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    let tr := sourceTranslation tag head tail firstChild secondChild truth membership equality imp forallOp
    F tr (fun _ => 4 * cantor b a + 2) = F forallOp ![a,F tr (fun _ => b)] := by
  have hn : 0 < 4 * cantor b a + 2 := by simp
  have hm : (4 * cantor b a + 2) % 4 = ((2 : Nat) : M) := by
    simpa only [mul_comm, Nat.cast_ofNat] using
      (mod_mul_add_of_lt (cantor b a) 4 (show (2 : M) < 4 by norm_num))
  have hdiv : (4 * cantor b a + 2) / 4 = cantor b a := by
    exact div_mul_add' (cantor b a) 4 (by norm_num)
  have h := modelTranslationUniversal tag head tail firstChild secondChild truth membership equality
    imp forallOp htag hhead htail hfirst hsecond (4 * cantor b a + 2) hn hm
  rw [hdiv,first_cantor,second_cantor] at h
  exact h

/-- Exact nonzero implication constructor `I(a,b)=4*cantor(a,b)`. The
exceptional `I(0,0)=0` is covered by `modelTranslationZero`. -/
theorem modelTranslationImplicationConstructor
    (tag head tail firstChild secondChild truth membership equality : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding tagMatrix.val) tag)
    (hhead : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* PRAHerbrandSelection.openMatrixAt
      (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) (hnz : 4 * cantor a b ≠ 0) :
    let tr := sourceTranslation tag head tail firstChild secondChild truth membership equality imp forallOp
    F tr (fun _ => 4 * cantor a b) = F imp ![F tr (fun _ => a),F tr (fun _ => b)] := by
  have hn : 0 < 4 * cantor a b := by
    rcases Arithmetic.zero_le (4 * cantor a b) with hz | hp
    · exact False.elim (hnz hz.symm)
    · exact hp
  have hm : (4 * cantor a b) % 4 = (0 : M) := by simp
  have hdiv : (4 * cantor a b) / 4 = cantor a b := by simp
  have h := modelTranslationImplication tag head tail firstChild secondChild truth membership equality
    imp forallOp htag hhead htail hfirst hsecond (4 * cantor a b) hn hm
  rw [hdiv,first_cantor,second_cantor] at h
  exact h


#print axioms modelChooseEq2
#print axioms modelHistoryDispatch
#print axioms modelHistoryDispatchTagged
#print axioms modelImplicationBranch
#print axioms modelUniversalBranch
#print axioms modelUpdateImplication
#print axioms modelUpdateUniversal
#print axioms modelTranslationImplication
#print axioms modelTranslationUniversal
#print axioms modelTranslationZero
#print axioms modelTranslationMembership
#print axioms modelTranslationEquality
#print axioms modelTranslationUniversalConstructor
#print axioms modelTranslationImplicationConstructor
end models
end PA194HistoryDispatch
