import PA194HistoryDispatch
import PA194DualImpCode
import PA194DualAtomCode

/-! A PA194 source recursion carrying positive/negative NNF syntax pairs.
Only the paired binder-closing operation remains a supplied code parameter. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace PA194DualRecursion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAHerbrandSelection PA194ChildCodes PA194TagDecoder
  PA194HistoryDispatch PA194DualImpCode PA194DualAtomCode PA194BranchSeed
  PA194BitTemplate PA194CanonicalVectorCode PA194EqAtomCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def dualMembershipCode (firstChild secondChild : Code 1) : Code 1 :=
  .comp dualBitCode (.cons secondChild (.cons firstChild (.nil 1)))

def dualEqualityCode (firstChild secondChild : Code 1) : Code 1 :=
  .comp dualEqCode (.cons firstChild (.cons secondChild (.nil 1)))

/-- The sole remaining syntax constructor parameter is paired universal
closing. Pair-projection and child/tag codes carry separate certificates. -/
def dualTranslation (tag firstProjection secondProjection firstChild secondChild : Code 1)
    (forallDual : Code 2) : Code 1 :=
  sourceTranslation tag firstProjection secondProjection firstChild secondChild
    dualTruthCode (dualMembershipCode firstChild secondChild)
    (dualEqualityCode firstChild secondChild)
    (dualImpCode firstProjection secondProjection) forallDual

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

theorem modelDualMembershipValue (firstChild secondChild : Code 1)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) : F (dualMembershipCode firstChild secondChild) (fun _ => n) =
      F dualBitCode ![second (n/4),first (n/4)] := by
  rw [dualMembershipCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelSecondCode secondChild hsecond n
  · exact Fin.cases (modelFirstCode firstChild hfirst n) (fun k => Fin.elim0 k) j

theorem modelDualEqualityValue (firstChild secondChild : Code 1)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (n : M) : F (dualEqualityCode firstChild secondChild) (fun _ => n) =
      F dualEqCode ![first (n/4),second (n/4)] := by
  rw [dualEqualityCode,modelComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact modelFirstCode firstChild hfirst n
  · exact Fin.cases (modelSecondCode secondChild hsecond n) (fun k => Fin.elim0 k) j

theorem modelDualZero (tag firstProjection secondProjection firstChild secondChild : Code 1)
    (forallDual : Code 2) :
    F (dualTranslation tag firstProjection secondProjection firstChild secondChild forallDual)
      (fun _ => (0 : M)) = pair (pair 2 0 + 1) (pair 3 0 + 1) := by
  rw [dualTranslation,modelTranslationZero,modelDualTruth]

theorem modelDualMembership (tag firstProjection secondProjection firstChild secondChild : Code 1)
    (forallDual : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    F (dualTranslation tag firstProjection secondProjection firstChild secondChild forallDual)
      (fun _ => 4 * cantor a b + 1) = F dualBitCode ![b,a] := by
  have hn : 0 < 4 * cantor a b + 1 := by simp
  have hm : (4 * cantor a b + 1) % 4 = ((1 : Nat) : M) := by
    simpa only [mul_comm, Nat.cast_one] using
      (mod_mul_add_of_lt (cantor a b) 4 (show (1 : M) < 4 by norm_num))
  rw [dualTranslation,modelTranslationMembership tag firstProjection secondProjection
    firstChild secondChild dualTruthCode (dualMembershipCode firstChild secondChild)
    (dualEqualityCode firstChild secondChild) (dualImpCode firstProjection secondProjection)
    forallDual htag _ hn hm, modelDualMembershipValue firstChild secondChild hfirst hsecond]
  have h : (4 * cantor a b + 1) / 4 = cantor a b := by
    exact div_mul_add' (cantor a b) 4 (by norm_num)
  rw [h,first_cantor,second_cantor]

theorem modelDualEquality (tag firstProjection secondProjection firstChild secondChild : Code 1)
    (forallDual : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    F (dualTranslation tag firstProjection secondProjection firstChild secondChild forallDual)
      (fun _ => 4 * cantor a b + 3) = F dualEqCode ![a,b] := by
  have hn : 0 < 4 * cantor a b + 3 := by simp
  have hm : (4 * cantor a b + 3) % 4 = ((3 : Nat) : M) := by
    simpa only [mul_comm, Nat.cast_ofNat] using
      (mod_mul_add_of_lt (cantor a b) 4 (show (3 : M) < 4 by norm_num))
  rw [dualTranslation,modelTranslationEquality tag firstProjection secondProjection
    firstChild secondChild dualTruthCode (dualMembershipCode firstChild secondChild)
    (dualEqualityCode firstChild secondChild) (dualImpCode firstProjection secondProjection)
    forallDual htag _ hn hm, modelDualEqualityValue firstChild secondChild hfirst hsecond]
  have h : (4 * cantor a b + 3) / 4 = cantor a b := by
    exact div_mul_add' (cantor a b) 4 (by norm_num)
  rw [h,first_cantor,second_cantor]

/-- The dual implication constructor works for arbitrary model values, not
only externally supplied pairs. -/
theorem modelDualImpAny (firstProjection secondProjection : Code 1)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) firstProjection)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) secondProjection)
    (x y : M) : F (dualImpCode firstProjection secondProjection) ![x,y] =
      pair (pair 5 (pair (π₂ x) (π₁ y)) + 1)
           (pair 4 (pair (π₁ x) (π₂ y)) + 1) := by
  rw [dualImpCode,modelBin,modelOrCode,modelAndCode]
  simp only [PA194PathIterator.modelUnary,modelProjection,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [modelPi1Code firstProjection hfirst,modelPi1Code firstProjection hfirst,
      modelPi2Code secondProjection hsecond,modelPi2Code secondProjection hsecond]
  exact modelPairCode _ _

/-- The nonzero source implication branch is fully constructed using paired
NNF constructors; no generic syntax-negation code is assumed. -/
theorem modelDualImplication (tag firstProjection secondProjection firstChild secondChild : Code 1)
    (forallDual : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfp : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) firstProjection)
    (hsp : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) secondProjection)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) (hnz : 4 * cantor a b ≠ 0) :
    let tr := dualTranslation tag firstProjection secondProjection firstChild secondChild forallDual
    F tr (fun _ => 4 * cantor a b) =
      pair (pair 5 (pair (π₂ (F tr (fun _ => a))) (π₁ (F tr (fun _ => b)))) + 1)
           (pair 4 (pair (π₁ (F tr (fun _ => a))) (π₂ (F tr (fun _ => b)))) + 1) := by
  dsimp only
  rw [dualTranslation,
    modelTranslationImplicationConstructor tag firstProjection secondProjection firstChild secondChild
      dualTruthCode (dualMembershipCode firstChild secondChild) (dualEqualityCode firstChild secondChild)
      (dualImpCode firstProjection secondProjection) forallDual htag hfp hsp hfirst hsecond a b hnz,
    modelDualImpAny firstProjection secondProjection hfp hsp]

/-- Universal closing remains an explicit binary parameter. -/
theorem modelDualUniversal (tag firstProjection secondProjection firstChild secondChild : Code 1)
    (forallDual : Code 2)
    (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
    (hfp : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) firstProjection)
    (hsp : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) secondProjection)
    (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
    (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
    (a b : M) :
    let tr := dualTranslation tag firstProjection secondProjection firstChild secondChild forallDual
    F tr (fun _ => 4 * cantor b a + 2) = F forallDual ![a,F tr (fun _ => b)] := by
  exact modelTranslationUniversalConstructor tag firstProjection secondProjection firstChild secondChild
    dualTruthCode (dualMembershipCode firstChild secondChild) (dualEqualityCode firstChild secondChild)
    (dualImpCode firstProjection secondProjection) forallDual htag hfp hsp hfirst hsecond a b

#print axioms modelDualMembershipValue
#print axioms modelDualEqualityValue
#print axioms modelDualZero
#print axioms modelDualMembership
#print axioms modelDualEquality
#print axioms modelDualImpAny
#print axioms modelDualImplication
#print axioms modelDualUniversal
end models
end PA194DualRecursion
