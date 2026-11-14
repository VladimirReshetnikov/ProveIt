import PA194GenericRenameAxiom
import PA194PAAxiomReopen
import PA194LiftRename
/-! Model-internal free-label traversal preserves well-formed syntax and
commutes with syntactic negation. It does not transform derivations. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
namespace PA194GenericRenameRules
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode

open PA194GenericRenameBase PA194GenericRenameAxiom
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

lemma term_wf (param depth t : M) (ht : IsSemiterm ℒₒᵣ depth t) :
    IsSemiterm ℒₒᵣ depth (renameTerm mapGraph f hf param t) := by
  haveI := term_definable mapGraph f hf param
  have hdef : 𝚺₁-Predicate (fun t : M => IsSemiterm ℒₒᵣ depth (renameTerm mapGraph f hf param t)) := by
    definability
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz; simp [renameTerm,termConstruction,hz]
  · intro x; simp [renameTerm,termConstruction]
  · intro k g v hg hv ih
    change IsSemiterm ℒₒᵣ depth ((termConstruction mapGraph f hf).result ℒₒᵣ ![param] (^func k g v))
    rw [Language.TermRec.Construction.result_func' _ hg hv.isUTerm]
    change IsSemiterm ℒₒᵣ depth (^func k g ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![param] k v))
    simp only [hg, IsSemiterm.func, true_and]
    refine IsSemitermVec.iff.mpr ⟨?_, ?_⟩
    · exact Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm
    · intro i hi
      rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
      exact ih i hi

lemma vector_wf (param depth k v : M) (hv : IsSemitermVec ℒₒᵣ k depth v) :
    IsSemitermVec ℒₒᵣ k depth ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![param] k v) := by
  apply IsSemitermVec.iff.mpr
  constructor
  · simp [hv.isUTerm]
  · intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    exact term_wf mapGraph f hf param depth v.[i] (hv.nth hi)

lemma formula_wf (param depth p : M) (hp : IsSemiformula ℒₒᵣ depth p) :
    IsSemiformula ℒₒᵣ depth (renameFormula mapGraph f hf param p) := by
  haveI := formula_definable mapGraph f hf param
  have hdef : 𝚺₁-Relation (fun n p : M => IsSemiformula ℒₒᵣ n (renameFormula mapGraph f hf param p)) := by
    definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k R v hR hv
    simp [renameFormula, formulaConstruction, hR, hv.isUTerm, vector_wf mapGraph f hf param n k v hv]
  · intro n k R v hR hv
    simp [renameFormula, formulaConstruction, hR, hv.isUTerm, vector_wf mapGraph f hf param n k v hv]
  · intro n; simp [renameFormula, formulaConstruction]
  · intro n; simp [renameFormula, formulaConstruction]
  · intro n p q hp hq ihp ihq
    simp [renameFormula, formulaConstruction, hp.isUFormula, hq.isUFormula] at *
    exact ⟨ihp,ihq⟩
  · intro n p q hp hq ihp ihq
    simp [renameFormula, formulaConstruction, hp.isUFormula, hq.isUFormula] at *
    exact ⟨ihp,ihq⟩
  · intro n p hp ih
    simp [renameFormula, formulaConstruction, hp.isUFormula] at *
    exact ih
  · intro n p hp ih
    simp [renameFormula, formulaConstruction, hp.isUFormula] at *
    exact ih

lemma rename_rel (param k r v : M) (hr : (ℒₒᵣ : Language).IsRel k r) (hv : IsUTermVec ℒₒᵣ k v) :
    renameFormula mapGraph f hf param (^rel k r v) = ^rel k r ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![param] k v) := by
  simp [renameFormula,formulaConstruction,hr,hv]
lemma rename_nrel (param k r v : M) (hr : (ℒₒᵣ : Language).IsRel k r) (hv : IsUTermVec ℒₒᵣ k v) :
    renameFormula mapGraph f hf param (^nrel k r v) = ^nrel k r ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![param] k v) := by
  simp [renameFormula,formulaConstruction,hr,hv]
lemma rename_verum (param : M) : renameFormula mapGraph f hf param ^⊤ = ^⊤ := by simp [renameFormula,formulaConstruction]
lemma rename_falsum (param : M) : renameFormula mapGraph f hf param ^⊥ = ^⊥ := by simp [renameFormula,formulaConstruction]
lemma rename_and (param p q : M) (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    renameFormula mapGraph f hf param (p ^⋏ q) = renameFormula mapGraph f hf param p ^⋏ renameFormula mapGraph f hf param q := by
  simp [renameFormula,formulaConstruction,hp,hq]
lemma rename_or (param p q : M) (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    renameFormula mapGraph f hf param (p ^⋎ q) = renameFormula mapGraph f hf param p ^⋎ renameFormula mapGraph f hf param q := by
  simp [renameFormula,formulaConstruction,hp,hq]
lemma rename_all (param p : M) (hp : IsUFormula ℒₒᵣ p) :
    renameFormula mapGraph f hf param (^∀ p) = ^∀ (renameFormula mapGraph f hf param p) := by
  simp [renameFormula,formulaConstruction,hp]
lemma rename_exs (param p : M) (hp : IsUFormula ℒₒᵣ p) :
    renameFormula mapGraph f hf param (^∃ p) = ^∃ (renameFormula mapGraph f hf param p) := by
  simp [renameFormula,formulaConstruction,hp]

lemma formula_neg (param depth p : M) (hp : IsSemiformula ℒₒᵣ depth p) :
    renameFormula mapGraph f hf param (Bootstrapping.neg ℒₒᵣ p) =
      Bootstrapping.neg ℒₒᵣ (renameFormula mapGraph f hf param p) := by
  haveI := formula_definable mapGraph f hf param
  have hdef : 𝚺₁-Relation (fun n p : M =>
      renameFormula mapGraph f hf param (Bootstrapping.neg ℒₒᵣ p) =
      Bootstrapping.neg ℒₒᵣ (renameFormula mapGraph f hf param p)) := by
    definability
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k r v hr hv
    have hvec := (vector_wf mapGraph f hf param n k v hv).isUTerm
    simp [neg_rel hr hv.isUTerm, rename_rel mapGraph f hf param k r v hr hv.isUTerm,
      rename_nrel mapGraph f hf param k r v hr hv.isUTerm, hr, hvec]
  · intro n k r v hr hv
    have hvec := (vector_wf mapGraph f hf param n k v hv).isUTerm
    simp [neg_nrel hr hv.isUTerm, rename_rel mapGraph f hf param k r v hr hv.isUTerm,
      rename_nrel mapGraph f hf param k r v hr hv.isUTerm, hr, hvec]
  · intro n; simp [rename_verum,rename_falsum]
  · intro n; simp [rename_verum,rename_falsum]
  · intro n p q hp hq ihp ihq
    have hp' := formula_wf mapGraph f hf param n p hp
    have hq' := formula_wf mapGraph f hf param n q hq
    simp [neg_and hp.isUFormula hq.isUFormula,rename_and mapGraph f hf param p q hp.isUFormula hq.isUFormula,
      rename_or mapGraph f hf param _ _ hp.isUFormula.neg hq.isUFormula.neg, hp'.isUFormula,hq'.isUFormula,ihp,ihq]
  · intro n p q hp hq ihp ihq
    have hp' := formula_wf mapGraph f hf param n p hp
    have hq' := formula_wf mapGraph f hf param n q hq
    simp [neg_or hp.isUFormula hq.isUFormula,rename_or mapGraph f hf param p q hp.isUFormula hq.isUFormula,
      rename_and mapGraph f hf param _ _ hp.isUFormula.neg hq.isUFormula.neg, hp'.isUFormula,hq'.isUFormula,ihp,ihq]
  · intro n p hp ih
    have hp' := formula_wf mapGraph f hf param (n+1) p hp
    simp [neg_all hp.isUFormula,rename_all mapGraph f hf param p hp.isUFormula,
      rename_exs mapGraph f hf param _ hp.isUFormula.neg,hp'.isUFormula,ih]
  · intro n p hp ih
    have hp' := formula_wf mapGraph f hf param (n+1) p hp
    simp [neg_ex hp.isUFormula,rename_exs mapGraph f hf param p hp.isUFormula,
      rename_all mapGraph f hf param _ hp.isUFormula.neg,hp'.isUFormula,ih]

#print axioms formula_neg
#print axioms formula_wf
#print axioms term_wf
end models
end PA194GenericRenameRules
