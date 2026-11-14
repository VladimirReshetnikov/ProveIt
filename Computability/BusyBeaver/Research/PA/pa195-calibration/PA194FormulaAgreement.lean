import PA194FormulaUpdate
import PA194InternalFormulaClose
/-! Agreement of the explicit candidate-PRA formula-closing code with
Foundation's internal formula traversal, including nonstandard internal inputs.

The fixed-ceiling proof uses a bounded universal over budgets in its Σ₁
induction predicate. It does not establish compiler correctness or either
machine/consistency implication. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
namespace PA194FormulaAgreement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194FormulaUpdate PA194InternalFormulaClose
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

theorem predicate_def (G : M → M → M → M → M) (H : M → M → M)
    (hg : 𝚺₁-Function₄ G) (hh : 𝚺₁-Function₂ H) (label ceiling : M) :
    𝚺₁-Relation (fun n p : M => ∀ b ≤ ceiling, p ≤ b → b+n = ceiling → G p b label ceiling = H n p) := by
  haveI := hg
  haveI := hh
  definability
theorem close_vec_two (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth x y : M) (hx : IsSemiterm ℒₒᵣ depth x) (hy : IsSemiterm ℒₒᵣ depth y) :
    PA194InternalClose.construction.resultVec ℒₒᵣ ![label,depth] 2 ?[x,y] =
      ?[F (PA194TermRecursion.closeCode first second) ![x,label,depth],
        F (PA194TermRecursion.closeCode first second) ![y,label,depth]] := by
  rw [show (2 : M) = 1+1 by norm_num,
    Language.TermRec.Construction.resultVec_cons _ _ _ (by simpa using hy.isUTerm) hx.isUTerm,
    show (1 : M) = 0+1 by simp,
    Language.TermRec.Construction.resultVec_cons _ _ _ (by simp) hy.isUTerm]
  simp only [Language.TermRec.Construction.resultVec_nil]
  change ?[PA194InternalClose.close label depth x, PA194InternalClose.close label depth y] = _
  rw [← PA194InternalClose.agree first second hf hs label depth x hx,
    ← PA194InternalClose.agree first second hf hs label depth y hy]

theorem budget_agree (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label ceiling depth p : M) (hp : IsSemiformula ℒₒᵣ depth p) :
    ∀ b ≤ ceiling, p ≤ b → b+depth = ceiling →
      F (budgetClose first second) ![p,b,label,ceiling] = PA194InternalFormulaClose.close label depth p := by
  have hg : 𝚺₁-Function₄ (fun p b a c : M => F (budgetClose first second) ![p,b,a,c]) := by
    have h : 𝚺₁.DefinableFunction (fun v : Fin 4 → M => F (budgetClose first second) v) :=
      HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) (budgetClose first second))
    convert h using 1
    funext v
    exact congrArg (fun e : Fin 4 → M => F (budgetClose first second) e) (Matrix.fun_eq_vec_four v).symm
  haveI : 𝚺₁-Function₂ ((PA194InternalFormulaClose.construction (M := M)).result ℒₒᵣ) :=
    (PA194InternalFormulaClose.graph (M := M)).to_definable
  have hc : 𝚺₁-Function₂ (PA194InternalFormulaClose.close label) := by
    unfold PA194InternalFormulaClose.close
    definability
  have hdef := predicate_def (fun p b a c : M => F (budgetClose first second) ![p,b,a,c])
    (PA194InternalFormulaClose.close label) hg hc label ceiling
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k r v hr hv b hb hpb hbn
    have hk : k = 2 := by
      rcases (Arithmetic.isRel_iff_LOR (V := M)).mp hr with (⟨h,_⟩ | ⟨h,_⟩) <;> exact h
    subst k
    obtain ⟨x,y,hx,hy,rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
    have hxy := IsSemitermVec.doubleton.mp hv
    rw [PA194InternalFormulaClose.close_rel label n 2 r _ hr hv.isUTerm,
      close_vec_two first second hf hs label n x y hxy.1 hxy.2]
    change F (budgetClose first second) ![pair 0 (pair 2 (pair r (pair x (pair y 0+1)+1)))+1,b,label,ceiling] = _
    rw [←hbn,modelAtom first second hf hs 0 r x y b label n (Or.inl rfl)]
    rfl
  · intro n k r v hr hv b hb hpb hbn
    have hk : k = 2 := by
      rcases (Arithmetic.isRel_iff_LOR (V := M)).mp hr with (⟨h,_⟩ | ⟨h,_⟩) <;> exact h
    subst k
    obtain ⟨x,y,hx,hy,rfl⟩ := IsUTermVec.two_iff.mp hv.isUTerm
    have hxy := IsSemitermVec.doubleton.mp hv
    rw [PA194InternalFormulaClose.close_nrel label n 2 r _ hr hv.isUTerm,
      close_vec_two first second hf hs label n x y hxy.1 hxy.2]
    change F (budgetClose first second) ![pair 1 (pair 2 (pair r (pair x (pair y 0+1)+1)))+1,b,label,ceiling] = _
    rw [←hbn,modelAtom first second hf hs 1 r x y b label n (Or.inr rfl)]
    rfl
  · intro n b hb hpb hbn
    rw [PA194InternalFormulaClose.close_verum]
    change F (budgetClose first second) ![pair 2 0+1,b,label,ceiling] = _
    rw [modelTruth first second hf 2 0 b label ceiling (Or.inl rfl)]
    rfl
  · intro n b hb hpb hbn
    rw [PA194InternalFormulaClose.close_falsum]
    change F (budgetClose first second) ![pair 3 0+1,b,label,ceiling] = _
    rw [modelTruth first second hf 3 0 b label ceiling (Or.inr rfl)]
    rfl
  · intro n p q hp hq ihp ihq b hb hpb hbn
    rw [PA194InternalFormulaClose.close_and label n p q hp.isUFormula hq.isUFormula]
    change F (budgetClose first second) ![pair 4 (pair p q)+1,b,label,ceiling] = _
    rw [modelBoolean first second hf hs 4 p q b label ceiling (Or.inl rfl)]
    have hp' : p ≤ b := le_trans (le_of_lt (by simp : p < p ^⋏ q)) hpb
    have hq' : q ≤ b := le_trans (le_of_lt (by simp : q < p ^⋏ q)) hpb
    rw [ihp b hb hp' hbn, ihq b hb hq' hbn]
    rfl
  · intro n p q hp hq ihp ihq b hb hpb hbn
    rw [PA194InternalFormulaClose.close_or label n p q hp.isUFormula hq.isUFormula]
    change F (budgetClose first second) ![pair 5 (pair p q)+1,b,label,ceiling] = _
    rw [modelBoolean first second hf hs 5 p q b label ceiling (Or.inr rfl)]
    have hp' : p ≤ b := le_trans (le_of_lt (by simp : p < p ^⋎ q)) hpb
    have hq' : q ≤ b := le_trans (le_of_lt (by simp : q < p ^⋎ q)) hpb
    rw [ihp b hb hp' hbn, ihq b hb hq' hbn]
    rfl
  · intro n p hp ih b hb hpb hbn
    rcases zero_or_succ b with (rfl | ⟨b,rfl⟩)
    · have hpos : (0 : M) < ^∀ p := by
        change (0 : M) < pair 6 p + 1
        exact lt_of_le_of_lt (zero_le) (lt_add_one _)
      exact (not_le_of_gt hpos hpb).elim
    · rw [PA194InternalFormulaClose.close_all label n p hp.isUFormula]
      change F (budgetClose first second) ![pair 6 p+1,b+1,label,ceiling] = _
      rw [modelQuantifier first second hf hs 6 p b label ceiling (Or.inl rfl)]
      have hb' : b ≤ ceiling := le_trans (le_of_lt (lt_add_one b)) hb
      have hp' : p ≤ b := lt_succ_iff_le.mp (lt_of_lt_of_le (by simp : p < ^∀ p) hpb)
      have hbn' : b+(n+1) = ceiling := by simpa [add_assoc,add_comm,add_left_comm] using hbn
      rw [ih b hb' hp' hbn']
      rfl
  · intro n p hp ih b hb hpb hbn
    rcases zero_or_succ b with (rfl | ⟨b,rfl⟩)
    · have hpos : (0 : M) < ^∃ p := by
        change (0 : M) < pair 7 p + 1
        exact lt_of_le_of_lt (zero_le) (lt_add_one _)
      exact (not_le_of_gt hpos hpb).elim
    · rw [PA194InternalFormulaClose.close_exs label n p hp.isUFormula]
      change F (budgetClose first second) ![pair 7 p+1,b+1,label,ceiling] = _
      rw [modelQuantifier first second hf hs 7 p b label ceiling (Or.inr rfl)]
      have hb' : b ≤ ceiling := le_trans (le_of_lt (lt_add_one b)) hb
      have hp' : p ≤ b := lt_succ_iff_le.mp (lt_of_lt_of_le (by simp : p < ^∃ p) hpb)
      have hbn' : b+(n+1) = ceiling := by simpa [add_assoc,add_comm,add_left_comm] using hbn
      rw [ih b hb' hp' hbn']
      rfl
/-- The root budget is the formula code, which is sufficient at any depth. -/
theorem root_agree (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label depth p : M) (hp : IsSemiformula ℒₒᵣ depth p) :
    F (closeAtDepth first second) ![p,label,depth] = PA194InternalFormulaClose.close label depth p := by
  rw [modelCloseAtDepth]
  apply budget_agree first second hf hs label (p+depth) depth p hp p
  · exact le_add_right (le_refl p)
  · exact le_refl p
  · rfl

/-- The compiler-shaped code agrees on arbitrary internal closed-depth formulas. -/
theorem compiler_close_agree (first second : Code 1)
    (hf : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₁Def.val) first)
    (hs : PRA ⊢ ∀⁰* openMatrixAt (Semiformula.lMap embedding pi₂Def.val) second)
    (label p : M) (hp : IsSemiformula ℒₒᵣ 0 p) :
    F (closeFormula first second) ![label,p] = PA194InternalFormulaClose.close label 0 p := by
  rw [modelCloseFormula]
  apply budget_agree first second hf hs label p 0 p hp p
  · exact le_refl p
  · exact le_refl p
  · simp

/-- A single fixed compiler-interface code with certified projections. -/
noncomputable def canonicalCloseFormula : Code 2 :=
  closeFormula PA194TermWellFormedUnconditional.canonicalFirst PA194TermWellFormedUnconditional.canonicalSecond

/-- Agreement for arbitrary internal formulas and labels without projection premises. -/
theorem canonical_close_agree (label p : M) (hp : IsSemiformula ℒₒᵣ 0 p) :
    F canonicalCloseFormula ![label,p] = PA194InternalFormulaClose.close label 0 p := by
  exact compiler_close_agree _ _
    (Classical.choose_spec PA194BranchSeed.PRA_has_pi1Code).2
    (Classical.choose_spec PA194BranchSeed.PRA_has_pi2Code).2 label p hp

/-- The canonical code outputs an internally well-formed formula at depth 1. -/
theorem canonical_close_wellformed (label p : M) (hp : IsSemiformula ℒₒᵣ 0 p) :
    IsSemiformula ℒₒᵣ 1 (F canonicalCloseFormula ![label,p]) := by
  rw [canonical_close_agree label p hp]
  simpa using PA194InternalFormulaClose.close_wellformed label 0 p hp

#print axioms canonical_close_agree
#print axioms canonical_close_wellformed
#print axioms root_agree
#print axioms compiler_close_agree
#print axioms close_vec_two
#print axioms predicate_def
#print axioms budget_agree
end models
end PA194FormulaAgreement
