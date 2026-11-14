import PA194SourceOutputWF
import PA194CloseNegation
import PA194DualComplement
/-! Polarity of both outputs of the PA194 named numerical source traversal.
This identifies internal syntactic negation, not a truth predicate for
nonstandard formulas. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace PA194SourcePolarity
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194CanonicalDualForall PA194DualRecursion PA194DualQuantRecursion PA194DualAtomCode
  PA194DualComplement PA194TagDecoder PA194ChildCodes PA194TemplateInternal PA194SourceOutputWF
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
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
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def complementary (out : M) : Prop := π₂ out = Bootstrapping.neg ℒₒᵣ (π₁ out)
variable (tag firstChild secondChild : Code 1)
variable (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
variable (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
variable (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
include htag hfirst hsecond
local notation "T" => translation tag firstChild secondChild

theorem zero_pol : complementary (F T (fun _ => (0 : M))) := by
  rw [translation,dualQuantTranslation,modelDualZero]
  simp only [complementary,pi₁_pair,pi₂_pair]
  change (^⊥ : M) = neg ℒₒᵣ (^⊤ : M)
  simp

theorem membership_pol (a b : M) : complementary (F T (fun _ => 4*cantor a b+1)) := by
  rw [translation,dualQuantTranslation,modelDualMembership _ _ _ _ _ _ htag hfirst hsecond,
    modelDualBitComplement]
  simp only [complementary,pi₁_pair,pi₂_pair]
  rfl

theorem equality_pol (a b : M) : complementary (F T (fun _ => 4*cantor a b+3)) := by
  rw [translation,dualQuantTranslation,modelDualEquality _ _ _ _ _ _ htag hfirst hsecond,
    modelDualEqComplement]
  simp only [complementary,pi₁_pair,pi₂_pair]
  rfl

theorem implication_pol (a b : M) (hnz : 4*cantor a b ≠ 0)
    (ha : complementary (F T (fun _ => a))) (hb : complementary (F T (fun _ => b))) :
    complementary (F T (fun _ => 4*cantor a b)) := by
  have hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val)
      PA194TermWellFormedUnconditional.canonicalFirst := (Classical.choose_spec PA194BranchSeed.PRA_has_pi1Code).2
  have hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val)
      PA194TermWellFormedUnconditional.canonicalSecond := (Classical.choose_spec PA194BranchSeed.PRA_has_pi2Code).2
  have wa := all_wf tag firstChild secondChild htag hfirst hsecond a
  have wb := all_wf tag firstChild secondChild htag hfirst hsecond b
  rw [translation,dualQuantTranslation,modelDualImplication _ _ _ _ _ _ htag hf hs hfirst hsecond a b hnz]
  simp only [complementary,pi₁_pair,pi₂_pair] at *
  change (π₁ (F T (fun _ => a))) ^⋏ (π₂ (F T (fun _ => b))) =
    neg ℒₒᵣ ((π₂ (F T (fun _ => a))) ^⋎ (π₁ (F T (fun _ => b))))
  rw [ha,hb]
  rw [neg_or wa.1.isUFormula.neg wb.1.isUFormula, IsUFormula.neg_neg wa.1.isUFormula]

theorem universal_pol (label body : M) (hbody : complementary (F T (fun _ => body))) :
    complementary (F T (fun _ => 4*cantor body label+2)) := by
  have wb := all_wf tag firstChild secondChild htag hfirst hsecond body
  rw [translation_universal tag firstChild secondChild htag hfirst hsecond label body wb.1 wb.2]
  simp only [complementary,pi₁_pair,pi₂_pair] at *
  rw [hbody,PA194CloseNegation.close_neg label 0 _ wb.1]
  have hw := PA194InternalFormulaClose.close_wellformed label 0 _ wb.1
  rw [neg_all hw.isUFormula]

/-- The negative output is exactly Foundation's internal negation of the
positive output, including for nonstandard source codes. -/
theorem all_pol (n : M) : complementary (F T (fun _ => n)) := by
  have hT : 𝚺₁-Function₁ (fun n : M => F T (fun _ => n)) := by
    have hg : 𝚺₁.DefinableFunction (fun e : Fin 1 → M => F T e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) T)
    convert hg using 1
    funext e
    apply congrArg (fun v : Fin 1 → M => F T v)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  haveI := hT
  have hdef : 𝚺₁-Predicate (fun n : M => complementary (F T (fun _ => n))) := by
    unfold complementary
    definability
  refine ISigma1.sigma1_order_induction hdef ?_ n
  intro x ih
  obtain ⟨a,b,h | h | h | h⟩ := source_cases x
  · rw [h] at ih ⊢
    by_cases hnz : 4*cantor a b = 0
    · rw [hnz]
      exact zero_pol tag firstChild secondChild htag hfirst hsecond
    · have hs := components_lt_imp a b hnz
      exact implication_pol tag firstChild secondChild htag hfirst hsecond a b hnz (ih a hs.1) (ih b hs.2)
  · rw [h]
    exact membership_pol tag firstChild secondChild htag hfirst hsecond a b
  · rw [h] at ih ⊢
    exact universal_pol tag firstChild secondChild htag hfirst hsecond b a (ih a (first_lt_universal a b))
  · rw [h]
    exact equality_pol tag firstChild secondChild htag hfirst hsecond a b

omit htag hfirst hsecond in
theorem fixed_all_pol (n : M) : complementary (F fixedTranslation (fun _ => n)) := by
  exact all_pol fixedTag fixedFirst fixedSecond
    (Classical.choose_spec PRA_has_tagCode).2
    (Classical.choose_spec PRA_has_firstChildCode).2
    (Classical.choose_spec PRA_has_secondChildCode).2 n

#check @fixed_all_pol
#print axioms fixed_all_pol
#print axioms all_pol
#print axioms implication_pol
#print axioms universal_pol
#print axioms zero_pol
#print axioms membership_pol
#print axioms equality_pol
end models
end PA194SourcePolarity
