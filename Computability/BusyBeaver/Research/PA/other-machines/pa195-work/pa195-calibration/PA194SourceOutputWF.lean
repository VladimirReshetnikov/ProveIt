import PA194CanonicalDualForall
/-! Arbitrary-model output well-formedness for the PA194 named numerical
source traversal. This does not assert semantic duality or proof translation. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace PA194SourceOutputWF
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194CanonicalDualForall PA194DualRecursion PA194DualQuantRecursion PA194DualAtomCode
  PA194TagDecoder PA194ChildCodes PA194TemplateInternal
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

def outWF (out : M) : Prop := IsSemiformula ℒₒᵣ 0 (π₁ out) ∧ IsSemiformula ℒₒᵣ 0 (π₂ out)

variable (tag firstChild secondChild : Code 1)
variable (htag : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding tagMatrix.val) tag)
variable (hfirst : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding firstMatrix.val) firstChild)
variable (hsecond : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding secondMatrix.val) secondChild)
include htag hfirst hsecond
local notation "T" => translation tag firstChild secondChild

theorem zero_wf : outWF (F T (fun _ => (0 : M))) := by
  rw [translation,dualQuantTranslation,modelDualZero]
  simp only [outWF,pi₁_pair,pi₂_pair]
  change IsSemiformula ℒₒᵣ 0 (^⊤ : M) ∧ IsSemiformula ℒₒᵣ 0 (^⊥ : M)
  simp

theorem membership_wf (a b : M) : outWF (F T (fun _ => 4*cantor a b+1)) := by
  rw [translation,dualQuantTranslation,modelDualMembership _ _ _ _ _ _ htag hfirst hsecond,
    modelDualBitInternal]
  simp only [outWF,pi₁_pair,pi₂_pair]
  exact ⟨(Bootstrapping.Semiformula.subst (substEnv b a 0)
        (⌜(Rew.emb ▹ bitDef.val : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).isSemiformula,
    (Bootstrapping.Semiformula.subst (substEnv b a 0)
        (⌜(Rew.emb ▹ (∼bitDef.val) : Semiproposition ℒₒᵣ 2)⌝ : Bootstrapping.Semiformula M ℒₒᵣ 2)).isSemiformula⟩

theorem equality_wf (a b : M) : outWF (F T (fun _ => 4*cantor a b+3)) := by
  rw [translation,dualQuantTranslation,modelDualEquality _ _ _ _ _ _ htag hfirst hsecond,
    modelDualEqInternal]
  have hrel : (ℒₒᵣ : Language).IsRel (2 : M) 0 := by
    apply Arithmetic.isRel_iff_LOR.mpr
    left
    exact ⟨rfl,rfl⟩
  simp [outWF,hrel]

theorem implication_wf (a b : M) (hnz : 4*cantor a b ≠ 0)
    (ha : outWF (F T (fun _ => a))) (hb : outWF (F T (fun _ => b))) :
    outWF (F T (fun _ => 4*cantor a b)) := by
  have hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val)
      PA194TermWellFormedUnconditional.canonicalFirst := (Classical.choose_spec PA194BranchSeed.PRA_has_pi1Code).2
  have hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val)
      PA194TermWellFormedUnconditional.canonicalSecond := (Classical.choose_spec PA194BranchSeed.PRA_has_pi2Code).2
  rw [translation,dualQuantTranslation,modelDualImplication _ _ _ _ _ _ htag hf hs hfirst hsecond a b hnz]
  simp only [outWF,pi₁_pair,pi₂_pair] at *
  exact ⟨IsSemiformula.or.mpr ⟨ha.2,hb.1⟩,IsSemiformula.and.mpr ⟨ha.1,hb.2⟩⟩

theorem universal_wf (label body : M) (hbody : outWF (F T (fun _ => body))) :
    outWF (F T (fun _ => 4*cantor body label+2)) := by
  have hp := hbody.1
  have hn := hbody.2
  rw [translation_universal tag firstChild secondChild htag hfirst hsecond label body hp hn]
  simp only [outWF,pi₁_pair,pi₂_pair]
  constructor
  · apply IsSemiformula.all.mpr
    simpa using PA194InternalFormulaClose.close_wellformed label 0 _ hp
  · apply IsSemiformula.exs.mpr
    simpa using PA194InternalFormulaClose.close_wellformed label 0 _ hn

omit htag hfirst hsecond in
theorem remainder_cases (n : M) : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by
  have hlt : n % 4 < (4 : M) := mod_lt n (by norm_num)
  have hle : n % 4 ≤ (3 : M) := lt_succ_iff_le.mp (by simp [three_add_one_eq_four, hlt])
  exact le_three_iff_eq_zero_or_one_or_two_or_three.mp hle

omit htag hfirst hsecond in
theorem source_cases (n : M) : ∃ a b : M,
    n = 4*cantor a b ∨ n = 4*cantor a b+1 ∨
      n = 4*cantor a b+2 ∨ n = 4*cantor a b+3 := by
  refine ⟨first (n/4),second (n/4),?_⟩
  have hn : 4*cantor (first (n/4)) (second (n/4)) + n%4 = n := by
    rw [cantor_projections]
    exact div_add_mod n 4
  rcases remainder_cases n with h | h | h | h <;> rw [h] at hn
  · left; simpa using hn.symm
  · exact Or.inr (Or.inl hn.symm)
  · exact Or.inr (Or.inr (Or.inl hn.symm))
  · exact Or.inr (Or.inr (Or.inr hn.symm))

omit htag hfirst hsecond in
theorem components_lt_imp (a b : M) (hnz : 4*cantor a b ≠ 0) :
    a < 4*cantor a b ∧ b < 4*cantor a b := by
  have hp : 0 < cantor a b := by
    apply pos_iff_ne_zero.mpr
    intro he
    apply hnz
    rw [he]
    simp
  have ht : cantor a b < 4*cantor a b := by
    have h := mul_lt_mul_of_pos_right (show (1 : M) < 4 by norm_num) hp
    simpa using h
  exact ⟨lt_of_le_of_lt (components_le a b).1 ht,lt_of_le_of_lt (components_le a b).2 ht⟩

omit htag hfirst hsecond in
theorem first_lt_universal (a b : M) : a < 4*cantor a b+2 := by
  have ht : cantor a b ≤ 4*cantor a b := by
    have h := Arithmetic.mul_le_mul_right (a := cantor a b) (show (1 : M) ≤ 4 by norm_num)
    simpa [mul_comm] using h
  have ht' : 4*cantor a b < 4*cantor a b+2 := lt_add_of_pos_right _ (by norm_num)
  exact lt_of_le_of_lt (le_trans (components_le a b).1 ht) ht'

/-- Every internal source code yields two well-formed arithmetic formulas. -/
theorem all_wf (n : M) : outWF (F T (fun _ => n)) := by
  have hT : 𝚺₁-Function₁ (fun n : M => F T (fun _ => n)) := by
    have hg : 𝚺₁.DefinableFunction (fun e : Fin 1 → M => F T e) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) T)
    convert hg using 1
    funext e
    apply congrArg (fun v : Fin 1 → M => F T v)
    funext i
    exact Fin.cases rfl (fun j => Fin.elim0 j) i
  haveI := hT
  have hdef : 𝚺₁-Predicate (fun n : M => outWF (F T (fun _ => n))) := by
    unfold outWF
    definability
  refine ISigma1.sigma1_order_induction hdef ?_ n
  intro x ih
  obtain ⟨a,b,h | h | h | h⟩ := source_cases x
  · rw [h] at ih ⊢
    by_cases hnz : 4*cantor a b = 0
    · rw [hnz]
      exact zero_wf tag firstChild secondChild htag hfirst hsecond
    · have hs := components_lt_imp a b hnz
      exact implication_wf tag firstChild secondChild htag hfirst hsecond a b hnz (ih a hs.1) (ih b hs.2)
  · rw [h]
    exact membership_wf tag firstChild secondChild htag hfirst hsecond a b
  · rw [h] at ih ⊢
    exact universal_wf tag firstChild secondChild htag hfirst hsecond b a (ih a (first_lt_universal a b))
  · rw [h]
    exact equality_wf tag firstChild secondChild htag hfirst hsecond a b

/-- Fix certified source decoders once; the certificates exist in PRA. -/
noncomputable def fixedTag : Code 1 := Classical.choose PRA_has_tagCode
noncomputable def fixedFirst : Code 1 := Classical.choose PRA_has_firstChildCode
noncomputable def fixedSecond : Code 1 := Classical.choose PRA_has_secondChildCode
noncomputable def fixedTranslation : Code 1 := translation fixedTag fixedFirst fixedSecond

omit htag hfirst hsecond in
theorem fixed_all_wf (n : M) : outWF (F fixedTranslation (fun _ => n)) := by
  exact all_wf fixedTag fixedFirst fixedSecond
    (Classical.choose_spec PRA_has_tagCode).2
    (Classical.choose_spec PRA_has_firstChildCode).2
    (Classical.choose_spec PRA_has_secondChildCode).2 n

#check @fixed_all_wf
#check @all_wf
#print axioms fixed_all_wf
#print axioms all_wf
#print axioms components_lt_imp
#print axioms first_lt_universal
#print axioms source_cases
#print axioms remainder_cases
#print axioms universal_wf
#print axioms implication_wf
#print axioms zero_wf
#print axioms membership_wf
#print axioms equality_wf
end models
end PA194SourceOutputWF
