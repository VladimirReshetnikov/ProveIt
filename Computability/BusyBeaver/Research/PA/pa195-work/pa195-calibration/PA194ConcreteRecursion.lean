import PA194HistoryDispatch
import PA194MembershipCode
import PA194EqualityCode

/-! Bind the recursive source translator's atomic branches to the actual
candidate-PRA membership and equality code constructors. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194ConcreteRecursion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAHerbrandSelection PA194StackHistory PA194HistoryDispatch
  PA194MembershipCode PA194EqualityCode PA194ChildCodes PA194TagDecoder
  PA194BitTemplate PA194TemplateInternal PA194EqAtomCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def concreteTranslation (tag head tail firstChild secondChild truth : Code 1)
    (imp forallOp : Code 2) : Code 1 :=
  sourceTranslation tag head tail firstChild secondChild truth
    (membershipCode firstChild secondChild) (equalityCode firstChild secondChild) imp forallOp

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

theorem modelConcreteZero (tag head tail firstChild secondChild truth : Code 1)
    (imp forallOp : Code 2) :
    F (concreteTranslation tag head tail firstChild secondChild truth imp forallOp)
      (fun _ => (0 : M)) = F truth (fun _ => (0 : M)) := by
  exact modelTranslationZero tag head tail firstChild secondChild truth
    (membershipCode firstChild secondChild) (equalityCode firstChild secondChild) imp forallOp

theorem modelConcreteMembership (tag head tail firstChild secondChild truth : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    F (concreteTranslation tag head tail firstChild secondChild truth imp forallOp)
      (fun _ => 4 * cantor a b + 1) = F bitTemplateCode ![b,a] := by
  have hn : 0 < 4 * cantor a b + 1 := by simp
  have hm : (4 * cantor a b + 1) % 4 = ((1 : Nat) : M) := by
    simpa only [mul_comm, Nat.cast_one] using
      (mod_mul_add_of_lt (cantor a b) 4 (show (1 : M) < 4 by norm_num))
  rw [concreteTranslation,
    modelTranslationMembership tag head tail firstChild secondChild truth
      (membershipCode firstChild secondChild) (equalityCode firstChild secondChild)
      imp forallOp htag _ hn hm,
    modelMembershipConstructor firstChild secondChild hfirst hsecond]

theorem modelConcreteEquality (tag head tail firstChild secondChild truth : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    F (concreteTranslation tag head tail firstChild secondChild truth imp forallOp)
      (fun _ => 4 * cantor a b + 3) = F eqAtomCode ![a,b] := by
  have hn : 0 < 4 * cantor a b + 3 := by simp
  have hm : (4 * cantor a b + 3) % 4 = ((3 : Nat) : M) := by
    simpa only [mul_comm, Nat.cast_ofNat] using
      (mod_mul_add_of_lt (cantor a b) 4 (show (3 : M) < 4 by norm_num))
  rw [concreteTranslation,
    modelTranslationEquality tag head tail firstChild secondChild truth
      (membershipCode firstChild secondChild) (equalityCode firstChild secondChild)
      imp forallOp htag _ hn hm,
    modelEqualityConstructor firstChild secondChild hfirst hsecond]

/-- The concrete-atomic recursion invokes the supplied implication code on
the recursive translations of the two children, except at the zero alias. -/
theorem modelConcreteImplication (tag head tail firstChild secondChild truth : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) (hnz : 4 * cantor a b ≠ 0) :
    let tr := concreteTranslation tag head tail firstChild secondChild truth imp forallOp
    F tr (fun _ => 4 * cantor a b) = F imp ![F tr (fun _ => a),F tr (fun _ => b)] := by
  exact modelTranslationImplicationConstructor tag head tail firstChild secondChild truth
    (membershipCode firstChild secondChild) (equalityCode firstChild secondChild)
    imp forallOp htag hhead htail hfirst hsecond a b hnz

/-- The transposed universal constructor supplies the correct binder and
recursively translated body to the still-parameterized closing operation. -/
theorem modelConcreteUniversal (tag head tail firstChild secondChild truth : Code 1)
    (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hhead : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head)
    (htail : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    let tr := concreteTranslation tag head tail firstChild secondChild truth imp forallOp
    F tr (fun _ => 4 * cantor b a + 2) = F forallOp ![a,F tr (fun _ => b)] := by
  exact modelTranslationUniversalConstructor tag head tail firstChild secondChild truth
    (membershipCode firstChild secondChild) (equalityCode firstChild secondChild)
    imp forallOp htag hhead htail hfirst hsecond a b

/-- Identification with Foundation's typed substitution is available for
all model-valued labels under the explicit IΣ₁ assumption. -/
theorem modelConcreteMembershipInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag head tail firstChild secondChild truth : Code 1) (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    F (concreteTranslation tag head tail firstChild secondChild truth imp forallOp)
      (fun _ => 4 * cantor a b + 1) =
      (Bootstrapping.Semiformula.subst (substEnv b a 0)
        (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).val := by
  rw [modelConcreteMembership tag head tail firstChild secondChild truth imp forallOp htag hfirst hsecond]
  exact modelBitTemplate_internal b a

/-- Equality with Foundation's named equality-atom code also explicitly
requires IΣ₁; the preceding numeric branch theorem does not. -/
theorem modelConcreteEqualityInternal [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    (tag head tail firstChild secondChild truth : Code 1) (imp forallOp : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    F (concreteTranslation tag head tail firstChild secondChild truth imp forallOp)
      (fun _ => 4 * cantor a b + 3) = qqRel 2 0 (matrixToVec ![qqFvar a,qqFvar b]) := by
  rw [modelConcreteEquality tag head tail firstChild secondChild truth imp forallOp htag hfirst hsecond]
  exact modelEqAtomMatchesFoundation a b

#print axioms modelConcreteMembership
#print axioms modelConcreteEquality
#print axioms modelConcreteZero
#print axioms modelConcreteImplication
#print axioms modelConcreteUniversal
#print axioms modelConcreteMembershipInternal
#print axioms modelConcreteEqualityInternal
end models

/-- Candidate PRA supplies all decoder and auxiliary projection certificates
used by the concrete atomic and recursive branch equations. -/
theorem PRA_has_concreteComponents : ∃ tag head tail firstChild secondChild : Code 1,
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) head) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) tail) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild) ∧
    (PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild) := by
  obtain ⟨tag,_,htag⟩ := PRA_has_tagCode
  obtain ⟨head,tail,firstChild,secondChild,hhead,htail,hfirst,hsecond⟩ := PRA_has_historyComponents
  exact ⟨tag,head,tail,firstChild,secondChild,htag,hhead,htail,hfirst,hsecond⟩

#print axioms PRA_has_concreteComponents
end PA194ConcreteRecursion
