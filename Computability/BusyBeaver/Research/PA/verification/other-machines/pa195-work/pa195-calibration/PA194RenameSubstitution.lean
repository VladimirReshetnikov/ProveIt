import PA194RenameShiftCompatibility
import PA194ExpandedRename
import PA194PAAxiomReopen
import PA194LiftRename
/-! Renaming commutes with internal bound-variable substitution and with
Foundation's eigenvariable opening, including nonstandard internal syntax. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
namespace PA194RenameSubstitution
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode

open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility
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
variable (mapGraph : 𝚺₁.Semisentence 3) (f : M → M → M)
variable (hf : ∀ v : Fin 3 → M, (M ⊧/v mapGraph.val) ↔ v 0 = f (v 2) (v 1))

lemma term_rename_bshift (p depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    renameTerm mapGraph f hf p (termBShift ℒₒᵣ t) = termBShift ℒₒᵣ (renameTerm mapGraph f hf p t) := by
  haveI := term_definable mapGraph f hf p
  have hdef : 𝚺₁-Predicate (fun t : M =>
      renameTerm mapGraph f hf p (termBShift ℒₒᵣ t) = termBShift ℒₒᵣ (renameTerm mapGraph f hf p t)) := by
    definability
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz; simp [rename_bvar]
  · intro x; simp [rename_fvar]
  · intro k g v hg hv ih
    rw [termBShift_func hg hv.isUTerm,
      rename_func mapGraph f hf p k g _ hg hv.isUTerm.termBShiftVec,
      rename_func mapGraph f hf p k g v hg hv.isUTerm]
    have hvec := (vector_wf mapGraph f hf p depth k v hv).isUTerm
    rw [termBShift_func hg hvec]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm.termBShiftVec)
      (by rw [len_termBShiftVec hvec])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm.termBShiftVec hi,
      nth_termBShiftVec hvec hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termBShiftVec hv.isUTerm hi]
    exact ih i hi


lemma term_rename_subst (p n m w t : M) (ht : IsSemiterm ℒₒᵣ n t) (hw : IsSemitermVec ℒₒᵣ n m w) :
    renameTerm mapGraph f hf p (termSubst ℒₒᵣ w t) =
      termSubst ℒₒᵣ ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![p] n w) (renameTerm mapGraph f hf p t) := by
  haveI := term_definable mapGraph f hf p
  haveI : 𝚺₁-Function₁ (fun t : M => termSubst ℒₒᵣ w t) := by definability
  have hw' := vector_wf mapGraph f hf p m n w hw
  have hdef : 𝚺₁-Predicate (fun t : M =>
      renameTerm mapGraph f hf p (termSubst ℒₒᵣ w t) =
      termSubst ℒₒᵣ ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![p] n w) (renameTerm mapGraph f hf p t)) := by
    definability
  apply IsSemiterm.sigma1_induction hdef (n := n) ?_ ?_ ?_ t ht
  · intro z hz
    rw [termSubst_bvar, rename_bvar mapGraph f hf p z, termSubst_bvar,
      Language.TermRec.Construction.nth_resultVec _ _ _ hw.isUTerm hz]
    rfl
  · intro x; simp [rename_fvar]
  · intro k g v hg hv ih
    rw [termSubst_func hg hv.isUTerm,
      rename_func mapGraph f hf p k g _ hg (hw.termSubstVec hv).isUTerm,
      rename_func mapGraph f hf p k g v hg hv.isUTerm]
    have hv' := vector_wf mapGraph f hf p n k v hv
    rw [termSubst_func hg hv'.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ (hw.termSubstVec hv).isUTerm)
      (by rw [len_termSubstVec hv'.isUTerm])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv'.isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termSubstVec hv.isUTerm hi]
    exact ih i hi

noncomputable def renameVec (p k v : M) : M :=
  (termConstruction mapGraph f hf).resultVec ℒₒᵣ ![p] k v

theorem renameVec_definable (p : M) : 𝚺₁-Function₂ (renameVec mapGraph f hf p) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 3 → M =>
      (termConstruction mapGraph f hf).resultVec ℒₒᵣ (v ·.succ.succ) (v 0) (v 1)) :=
    HierarchySymbol.Defined.to_definable _ ((termConstruction mapGraph f hf).resultVec_defined (L := ℒₒᵣ))
  have hi : ∀ j : Fin 3, 𝚺₁.DefinableFunction (fun v : Fin 2 → M => ![v 0,v 1,p] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.var 0
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact HierarchySymbol.DefinableFunction.var 1
      · exact Fin.cases (HierarchySymbol.DefinableFunction.const p) (fun x => Fin.elim0 x) l
  have h := HierarchySymbol.DefinableFunction.substitution hg hi
  change 𝚺₁.DefinableFunction (fun v : Fin 2 → M => renameVec mapGraph f hf p (v 0) (v 1))
  convert h using 1
  funext v
  unfold renameVec
  congr 1

lemma renameVec_qVec (p n m w : M) (hw : IsSemitermVec ℒₒᵣ n m w) :
    (termConstruction mapGraph f hf).resultVec ℒₒᵣ ![p] (n+1) (qVec ℒₒᵣ w) =
      qVec ℒₒᵣ ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![p] n w) := by
  have hw' := vector_wf mapGraph f hf p m n w hw
  apply nth_ext' (n + 1)
    (Language.TermRec.Construction.resultVec_lh _ _ _ hw.qVec.isUTerm)
    (by rw [len_qVec hw'.isUTerm])
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hw.qVec.isUTerm hi]
  unfold qVec
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simpa [renameTerm] using rename_bvar mapGraph f hf p 0
  · have hi' : i < n := by simpa using hi
    rw [nth_adjoin_succ, nth_adjoin_succ, hw.lh, hw'.lh,
      nth_termBShiftVec hw.isUTerm (by simpa [hw.lh] using hi'),
      nth_termBShiftVec hw'.isUTerm (by simpa [hw'.lh] using hi'),
      Language.TermRec.Construction.nth_resultVec _ _ _ hw.isUTerm hi']
    exact term_rename_bshift mapGraph f hf p m w.[i] (hw.nth hi')

lemma formula_rename_subst (p n φ : M) (hφ : IsSemiformula ℒₒᵣ n φ) : ∀ m w,
    IsSemitermVec ℒₒᵣ n m w →
    renameFormula mapGraph f hf p (subst ℒₒᵣ w φ) =
      subst ℒₒᵣ (renameVec mapGraph f hf p n w) (renameFormula mapGraph f hf p φ) := by
  haveI := formula_definable mapGraph f hf p
  haveI := renameVec_definable mapGraph f hf p
  apply IsSemiformula.pi1_structural_induction ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · definability
  · intro n k R v hR hv m w hw
    rw [substs_rel hR hv.isUTerm,
      rename_rel mapGraph f hf p k R _ hR (hw.termSubstVec hv).isUTerm,
      rename_rel mapGraph f hf p k R v hR hv.isUTerm,
      substs_rel hR (vector_wf mapGraph f hf p n k v hv).isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ (hw.termSubstVec hv).isUTerm)
      (by rw [len_termSubstVec (vector_wf mapGraph f hf p n k v hv).isUTerm])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec (vector_wf mapGraph f hf p n k v hv).isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact term_rename_subst mapGraph f hf p n m w v.[i] (hv.nth hi) hw
  · intro n k R v hR hv m w hw
    rw [substs_nrel hR hv.isUTerm,
      rename_nrel mapGraph f hf p k R _ hR (hw.termSubstVec hv).isUTerm,
      rename_nrel mapGraph f hf p k R v hR hv.isUTerm,
      substs_nrel hR (vector_wf mapGraph f hf p n k v hv).isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ (hw.termSubstVec hv).isUTerm)
      (by rw [len_termSubstVec (vector_wf mapGraph f hf p n k v hv).isUTerm])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ (hw.termSubstVec hv).isUTerm hi,
      nth_termSubstVec hv.isUTerm hi,
      nth_termSubstVec (vector_wf mapGraph f hf p n k v hv).isUTerm hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact term_rename_subst mapGraph f hf p n m w v.[i] (hv.nth hi) hw
  · intro n m w hw; simp [rename_verum]
  · intro n m w hw; simp [rename_falsum]
  · intro n φ ψ hφ hψ ihφ ihψ m w hw
    rw [substs_and hφ.isUFormula hψ.isUFormula,
      rename_and mapGraph f hf p _ _ (hφ.subst hw).isUFormula (hψ.subst hw).isUFormula,
      rename_and mapGraph f hf p _ _ hφ.isUFormula hψ.isUFormula,
      substs_and (formula_wf mapGraph f hf p n φ hφ).isUFormula (formula_wf mapGraph f hf p n ψ hψ).isUFormula,
      ihφ m w hw, ihψ m w hw]
  · intro n φ ψ hφ hψ ihφ ihψ m w hw
    rw [substs_or hφ.isUFormula hψ.isUFormula,
      rename_or mapGraph f hf p _ _ (hφ.subst hw).isUFormula (hψ.subst hw).isUFormula,
      rename_or mapGraph f hf p _ _ hφ.isUFormula hψ.isUFormula,
      substs_or (formula_wf mapGraph f hf p n φ hφ).isUFormula (formula_wf mapGraph f hf p n ψ hψ).isUFormula,
      ihφ m w hw, ihψ m w hw]
  · intro n φ hφ ih m w hw
    rw [substs_all hφ.isUFormula,
      rename_all mapGraph f hf p _ (hφ.subst hw.qVec).isUFormula,
      rename_all mapGraph f hf p _ hφ.isUFormula,
      substs_all (formula_wf mapGraph f hf p (n+1) φ hφ).isUFormula,
      ih (m+1) (qVec ℒₒᵣ w) hw.qVec]
    congr 2
    exact renameVec_qVec mapGraph f hf p n m w hw
  · intro n φ hφ ih m w hw
    rw [substs_ex hφ.isUFormula,
      rename_exs mapGraph f hf p _ (hφ.subst hw.qVec).isUFormula,
      rename_exs mapGraph f hf p _ hφ.isUFormula,
      substs_ex (formula_wf mapGraph f hf p (n+1) φ hφ).isUFormula,
      ih (m+1) (qVec ℒₒᵣ w) hw.qVec]
    congr 2
    exact renameVec_qVec mapGraph f hf p n m w hw

lemma renameVec_single_fvar (p x : M) : renameVec mapGraph f hf p 1 (?[ ^&x ] : M) = ?[^&(f p x)] := by
  unfold renameVec
  rw [show (1 : M) = 0+1 by simp,
    Language.TermRec.Construction.resultVec_cons _ _ _ (by simp) (by simp)]
  simp [renameTerm,termConstruction]

lemma formula_rename_free (p q φ : M) (hφ : IsSemiformula ℒₒᵣ 1 φ)
    (hzero : f p 0 = 0) (hmap : ∀ x, f p (x+1) = f q x+1) :
    renameFormula mapGraph f hf p (free ℒₒᵣ φ) =
      free ℒₒᵣ (renameFormula mapGraph f hf q φ) := by
  unfold free substs1
  rw [formula_rename_subst mapGraph f hf p 1 (shift ℒₒᵣ φ) hφ.shift 0 ?[^&0] (by simp),
    renameVec_single_fvar mapGraph f hf p 0, hzero,
    formula_rename_shift mapGraph f hf p q 1 φ hφ hmap]

lemma expanded_rename_free (k a d e φ : M) (hφ : IsSemiformula ℒₒᵣ 1 φ) :
    renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair (k+1) (pair a (pair d e))) (free ℒₒᵣ φ) =
    free ℒₒᵣ (renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair k (pair a (pair d e))) φ) := by
  apply formula_rename_free _ _ _ _ _ φ hφ
  · simpa [PA194ExpandedRename.packedRen] using PA194ExpandedRename.lift_zero k a d e
  · intro x
    simpa [PA194ExpandedRename.packedRen] using PA194ExpandedRename.lift_succ k a d e x

#print axioms expanded_rename_free
#print axioms formula_rename_free
#print axioms formula_rename_subst
#print axioms renameVec_qVec
#print axioms term_rename_subst
#print axioms term_rename_bshift
end models
end PA194RenameSubstitution
