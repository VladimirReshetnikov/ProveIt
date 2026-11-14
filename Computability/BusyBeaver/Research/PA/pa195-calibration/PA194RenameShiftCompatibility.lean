import PA194GenericRenameRules
import PA194ExpandedRename
import PA194PAAxiomReopen
import PA194LiftRename
/-! Internal formula renaming is compatible with free-variable shift.
The explicit cases cover the expanded parameterized renaming family. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
namespace PA194RenameShiftCompatibility
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode

open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules
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

lemma rename_bvar (param z : M) : renameTerm mapGraph f hf param (^#z) = ^#z := by
  simp [renameTerm,termConstruction]
lemma rename_fvar (param x : M) : renameTerm mapGraph f hf param (^&x) = ^&(f param x) := by
  simp [renameTerm,termConstruction]
lemma rename_func (param k g v : M) (hg : (ℒₒᵣ : Language).IsFunc k g) (hv : IsUTermVec ℒₒᵣ k v) :
    renameTerm mapGraph f hf param (^func k g v) = ^func k g ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![param] k v) := by
  simp [renameTerm,termConstruction,hg,hv]

lemma term_rename_shift (p q depth t : M) (ht : IsSemiterm ℒₒᵣ depth t)
    (hmap : ∀ x, f p (x+1) = f q x + 1) :
    renameTerm mapGraph f hf p (termShift ℒₒᵣ t) = termShift ℒₒᵣ (renameTerm mapGraph f hf q t) := by
  haveI := term_definable mapGraph f hf p
  haveI := term_definable mapGraph f hf q
  have hdef : 𝚺₁-Predicate (fun t : M =>
      renameTerm mapGraph f hf p (termShift ℒₒᵣ t) = termShift ℒₒᵣ (renameTerm mapGraph f hf q t)) := by
    definability
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz; simp [rename_bvar]
  · intro x; simp [rename_fvar,hmap]
  · intro k g v hg hv ih
    rw [termShift_func hg hv.isUTerm,
      rename_func mapGraph f hf p k g _ hg hv.isUTerm.termShiftVec,
      rename_func mapGraph f hf q k g v hg hv.isUTerm]
    have hvec := (vector_wf mapGraph f hf q depth k v hv).isUTerm
    rw [termShift_func hg hvec]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm.termShiftVec)
      (by rw [len_termShiftVec hvec])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm.termShiftVec hi,
      nth_termShiftVec hvec hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi]
    exact ih i hi

lemma formula_rename_shift (p q depth φ : M) (hφ : IsSemiformula ℒₒᵣ depth φ)
    (hmap : ∀ x, f p (x+1) = f q x + 1) :
    renameFormula mapGraph f hf p (shift ℒₒᵣ φ) = shift ℒₒᵣ (renameFormula mapGraph f hf q φ) := by
  haveI := formula_definable mapGraph f hf p
  haveI := formula_definable mapGraph f hf q
  have hdef : 𝚺₁-Relation (fun n φ : M =>
      renameFormula mapGraph f hf p (shift ℒₒᵣ φ) = shift ℒₒᵣ (renameFormula mapGraph f hf q φ)) := by
    definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · intro n k r v hr hv
    rw [shift_rel hr hv.isUTerm,
      rename_rel mapGraph f hf p k r _ hr hv.isUTerm.termShiftVec,
      rename_rel mapGraph f hf q k r v hr hv.isUTerm]
    have hvec := (vector_wf mapGraph f hf q n k v hv).isUTerm
    rw [shift_rel hr hvec]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm.termShiftVec)
      (by rw [len_termShiftVec hvec])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm.termShiftVec hi,
      nth_termShiftVec hvec hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi]
    exact term_rename_shift mapGraph f hf p q n v.[i] (hv.nth hi) hmap
  · intro n k r v hr hv
    rw [shift_nrel hr hv.isUTerm,
      rename_nrel mapGraph f hf p k r _ hr hv.isUTerm.termShiftVec,
      rename_nrel mapGraph f hf q k r v hr hv.isUTerm]
    have hvec := (vector_wf mapGraph f hf q n k v hv).isUTerm
    rw [shift_nrel hr hvec]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm.termShiftVec)
      (by rw [len_termShiftVec hvec])
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm.termShiftVec hi,
      nth_termShiftVec hvec hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi]
    exact term_rename_shift mapGraph f hf p q n v.[i] (hv.nth hi) hmap
  · intro n; simp [rename_verum]
  · intro n; simp [rename_falsum]
  · intro n φ ψ hφ hψ ihφ ihψ
    have hfφ := (formula_wf mapGraph f hf q n φ hφ).isUFormula
    have hfψ := (formula_wf mapGraph f hf q n ψ hψ).isUFormula
    simp [shift_and hφ.isUFormula hψ.isUFormula,
      rename_and mapGraph f hf p _ _ hφ.isUFormula.shift hψ.isUFormula.shift,
      rename_and mapGraph f hf q _ _ hφ.isUFormula hψ.isUFormula,
      shift_and hfφ hfψ,ihφ,ihψ]
  · intro n φ ψ hφ hψ ihφ ihψ
    have hfφ := (formula_wf mapGraph f hf q n φ hφ).isUFormula
    have hfψ := (formula_wf mapGraph f hf q n ψ hψ).isUFormula
    simp [shift_or hφ.isUFormula hψ.isUFormula,
      rename_or mapGraph f hf p _ _ hφ.isUFormula.shift hψ.isUFormula.shift,
      rename_or mapGraph f hf q _ _ hφ.isUFormula hψ.isUFormula,
      shift_or hfφ hfψ,ihφ,ihψ]
  · intro n φ hφ ih
    have hfφ := (formula_wf mapGraph f hf q (n+1) φ hφ).isUFormula
    simp [shift_all hφ.isUFormula,
      rename_all mapGraph f hf p _ hφ.isUFormula.shift,
      rename_all mapGraph f hf q _ hφ.isUFormula,shift_all hfφ,ih]
  · intro n φ hφ ih
    have hfφ := (formula_wf mapGraph f hf q (n+1) φ hφ).isUFormula
    simp [shift_exs hφ.isUFormula,
      rename_exs mapGraph f hf p _ hφ.isUFormula.shift,
      rename_exs mapGraph f hf q _ hφ.isUFormula,shift_exs hfφ,ih]

lemma term_rename_shift_noshift (p q depth t : M) (ht : IsSemiterm ℒₒᵣ depth t)
    (hmap : ∀ x, f p (x+1) = f q x) :
    renameTerm mapGraph f hf p (termShift ℒₒᵣ t) = renameTerm mapGraph f hf q t := by
  haveI := term_definable mapGraph f hf p
  haveI := term_definable mapGraph f hf q
  have hdef : 𝚺₁-Predicate (fun t : M =>
      renameTerm mapGraph f hf p (termShift ℒₒᵣ t) = renameTerm mapGraph f hf q t) := by
    definability
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz; simp [rename_bvar]
  · intro x; simp [rename_fvar,hmap]
  · intro k g v hg hv ih
    rw [termShift_func hg hv.isUTerm,
      rename_func mapGraph f hf p k g _ hg hv.isUTerm.termShiftVec,
      rename_func mapGraph f hf q k g v hg hv.isUTerm]
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm.termShiftVec)
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm.termShiftVec hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi]
    exact ih i hi

lemma formula_rename_shift_noshift (p q depth φ : M) (hφ : IsSemiformula ℒₒᵣ depth φ)
    (hmap : ∀ x, f p (x+1) = f q x) :
    renameFormula mapGraph f hf p (shift ℒₒᵣ φ) = renameFormula mapGraph f hf q φ := by
  haveI := formula_definable mapGraph f hf p
  haveI := formula_definable mapGraph f hf q
  have hdef : 𝚺₁-Relation (fun n φ : M =>
      renameFormula mapGraph f hf p (shift ℒₒᵣ φ) = renameFormula mapGraph f hf q φ) := by
    definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hφ
  · intro n k r v hr hv
    rw [shift_rel hr hv.isUTerm,
      rename_rel mapGraph f hf p k r _ hr hv.isUTerm.termShiftVec,
      rename_rel mapGraph f hf q k r v hr hv.isUTerm]
    simp only [qqRel_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm.termShiftVec)
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm.termShiftVec hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi]
    exact term_rename_shift_noshift mapGraph f hf p q n v.[i] (hv.nth hi) hmap
  · intro n k r v hr hv
    rw [shift_nrel hr hv.isUTerm,
      rename_nrel mapGraph f hf p k r _ hr hv.isUTerm.termShiftVec,
      rename_nrel mapGraph f hf q k r v hr hv.isUTerm]
    simp only [qqNRel_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm.termShiftVec)
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm.termShiftVec hi,
      Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi,
      nth_termShiftVec hv.isUTerm hi]
    exact term_rename_shift_noshift mapGraph f hf p q n v.[i] (hv.nth hi) hmap
  · intro n; simp [rename_verum]
  · intro n; simp [rename_falsum]
  · intro n φ ψ hφ hψ ihφ ihψ
    simp [shift_and hφ.isUFormula hψ.isUFormula,
      rename_and mapGraph f hf p _ _ hφ.isUFormula.shift hψ.isUFormula.shift,
      rename_and mapGraph f hf q _ _ hφ.isUFormula hψ.isUFormula,
      ihφ,ihψ]
  · intro n φ ψ hφ hψ ihφ ihψ
    simp [shift_or hφ.isUFormula hψ.isUFormula,
      rename_or mapGraph f hf p _ _ hφ.isUFormula.shift hψ.isUFormula.shift,
      rename_or mapGraph f hf q _ _ hφ.isUFormula hψ.isUFormula,
      ihφ,ihψ]
  · intro n φ hφ ih
    simp [shift_all hφ.isUFormula,
      rename_all mapGraph f hf p _ hφ.isUFormula.shift,
      rename_all mapGraph f hf q _ hφ.isUFormula,ih]
  · intro n φ hφ ih
    simp [shift_exs hφ.isUFormula,
      rename_exs mapGraph f hf p _ hφ.isUFormula.shift,
      rename_exs mapGraph f hf q _ hφ.isUFormula,ih]

lemma expanded_shift_positive (k a d e depth φ : M) (hφ : IsSemiformula ℒₒᵣ depth φ) :
    renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair (k+1) (pair a (pair d e))) (shift ℒₒᵣ φ) =
    shift ℒₒᵣ (renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair k (pair a (pair d e))) φ) := by
  apply formula_rename_shift _ _ _ _ _ depth φ hφ
  intro x
  simpa [PA194ExpandedRename.packedRen] using PA194ExpandedRename.lift_succ k a d e x

lemma expanded_shift_zero_succ (a d e depth φ : M) (hφ : IsSemiformula ℒₒᵣ depth φ) :
    renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair 0 (pair (a+1) (pair d e))) (shift ℒₒᵣ φ) =
    renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair 0 (pair a (pair (d+1) e))) φ := by
  apply formula_rename_shift_noshift _ _ _ _ _ depth φ hφ
  intro x
  simpa [PA194ExpandedRename.packedRen] using PA194ExpandedRename.shift_zero_exception_succ a d e x

lemma expanded_shift_zero_zero (d e depth φ : M) (hφ : IsSemiformula ℒₒᵣ depth φ) :
    renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair 0 (pair 0 (pair d e))) (shift ℒₒᵣ φ) =
    renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair 0 (pair 0 (pair (d+1) 0))) φ := by
  apply formula_rename_shift_noshift _ _ _ _ _ depth φ hφ
  intro x
  simpa [PA194ExpandedRename.packedRen] using PA194ExpandedRename.shift_zero_exception_zero d e x

#print axioms expanded_shift_positive
#print axioms expanded_shift_zero_succ
#print axioms expanded_shift_zero_zero
#print axioms formula_rename_shift_noshift
#print axioms formula_rename_shift
#print axioms term_rename_shift
end models
end PA194RenameShiftCompatibility
