import PA194GenericRenameBase
import PA194PAAxiomReopen
import PA194LiftRename
/-! Any Σ₁-definable free-label renaming fixes Foundation's internal PA axioms.
The final corollary instantiates the protected-prefix candidate-PRA code. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 3000000
namespace PA194GenericRenameAxiom
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode

open PA194GenericRenameBase
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

noncomputable def renameTerm (param t : M) : M := (termConstruction mapGraph f hf).result ℒₒᵣ ![param] t

theorem term_definable (param : M) : 𝚺₁-Function₁ (renameTerm mapGraph f hf param) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 2 → M => (termConstruction mapGraph f hf).result ℒₒᵣ (v ·.succ) (v 0)) :=
    HierarchySymbol.Defined.to_definable _ ((termConstruction mapGraph f hf).result_defined (L := ℒₒᵣ))
  have hi : ∀ j : Fin 2, 𝚺₁.DefinableFunction (fun v : Fin 1 → M => ![v 0,param] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.var 0
    · exact Fin.cases (HierarchySymbol.DefinableFunction.const param) (fun x => Fin.elim0 x) k
  have h := HierarchySymbol.DefinableFunction.substitution hg hi
  change 𝚺₁.DefinableFunction (fun v : Fin 1 → M => renameTerm mapGraph f hf param (v 0))
  convert h using 1
  funext v
  unfold renameTerm
  congr 1

lemma term_fixed (param depth t : M) (ht : IsSemiterm ℒₒᵣ depth t)
    (hs : termShift ℒₒᵣ t = t) : renameTerm mapGraph f hf param t = t := by
  haveI := term_definable mapGraph f hf param
  have hdef : 𝚺₁-Predicate (fun t : M => termShift ℒₒᵣ t = t → renameTerm mapGraph f hf param t = t) := by
    definability
  revert hs
  apply IsSemiterm.sigma1_induction hdef (n := depth) ?_ ?_ ?_ t ht
  · intro z hz _
    simp [renameTerm, termConstruction]
  · intro x h
    simp only [termShift_fvar, qqFvar_inj] at h
    exact False.elim ((ne_of_lt (lt_add_one x)) h.symm)
  · intro k g v hfunc hv ih hs
    rw [termShift_func hfunc hv.isUTerm] at hs
    have hvfixed : termShiftVec ℒₒᵣ k v = v := by simpa using hs
    change (termConstruction mapGraph f hf).result ℒₒᵣ ![param] (^func k g v) = ^func k g v
    rw [Language.TermRec.Construction.result_func' _ hfunc hv.isUTerm]
    change ^func k g ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![param] k v) = ^func k g v
    simp only [qqFunc_inj, true_and]
    apply nth_ext' k
      (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
    intro i hi
    rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
    change renameTerm mapGraph f hf param v.[i] = v.[i]
    apply ih i hi
    have hh := congrArg (fun z : M => z.[i]) hvfixed
    simpa [nth_termShiftVec hv.isUTerm hi] using hh


lemma vector_fixed (param depth k v : M) (hv : IsSemitermVec ℒₒᵣ k depth v)
    (hs : termShiftVec ℒₒᵣ k v = v) :
    (termConstruction mapGraph f hf).resultVec ℒₒᵣ ![param] k v = v := by
  apply nth_ext' k
    (Language.TermRec.Construction.resultVec_lh _ _ _ hv.isUTerm) (by simpa using hv.lh)
  intro i hi
  rw [Language.TermRec.Construction.nth_resultVec _ _ _ hv.isUTerm hi]
  change renameTerm mapGraph f hf param v.[i] = v.[i]
  apply term_fixed mapGraph f hf param depth v.[i] (hv.nth hi)
  have hh := congrArg (fun z : M => z.[i]) hs
  simpa [nth_termShiftVec hv.isUTerm hi] using hh

noncomputable def renameFormula (param p : M) : M :=
  (formulaConstruction mapGraph f hf).result ℒₒᵣ param p

theorem formula_definable (param : M) : 𝚺₁-Function₁ (renameFormula mapGraph f hf param) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 2 → M => (formulaConstruction mapGraph f hf).result ℒₒᵣ (v 0) (v 1)) :=
    HierarchySymbol.Defined.to_definable _ ((formulaConstruction mapGraph f hf).result_defined (L := ℒₒᵣ))
  have hi : ∀ j : Fin 2, 𝚺₁.DefinableFunction (fun v : Fin 1 → M => ![param,v 0] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.const param
    · exact Fin.cases (HierarchySymbol.DefinableFunction.var 0) (fun x => Fin.elim0 x) k
  have h := HierarchySymbol.DefinableFunction.substitution hg hi
  change 𝚺₁.DefinableFunction (fun v : Fin 1 → M => renameFormula mapGraph f hf param (v 0))
  convert h using 1
  funext v
  unfold renameFormula
  simp

lemma formula_fixed (param depth p : M) (hp : IsSemiformula ℒₒᵣ depth p)
    (hs : shift ℒₒᵣ p = p) : renameFormula mapGraph f hf param p = p := by
  haveI := formula_definable mapGraph f hf param
  have hdef : 𝚺₁-Relation (fun depth p : M => shift ℒₒᵣ p = p → renameFormula mapGraph f hf param p = p) := by
    definability
  revert hs
  apply IsSemiformula.sigma1_structural_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hp
  · intro n k R v hR hv hs
    rw [shift_rel hR hv.isUTerm] at hs
    have hvec : termShiftVec ℒₒᵣ k v = v := by simpa using hs
    simp [renameFormula, formulaConstruction, hR, hv.isUTerm, vector_fixed mapGraph f hf param n k v hv hvec]
  · intro n k R v hR hv hs
    rw [shift_nrel hR hv.isUTerm] at hs
    have hvec : termShiftVec ℒₒᵣ k v = v := by simpa using hs
    simp [renameFormula, formulaConstruction, hR, hv.isUTerm, vector_fixed mapGraph f hf param n k v hv hvec]
  · intro n _; simp [renameFormula, formulaConstruction]
  · intro n _; simp [renameFormula, formulaConstruction]
  · intro n p q hp hq ihp ihq hs
    rw [shift_and hp.isUFormula hq.isUFormula] at hs
    have h : shift ℒₒᵣ p = p ∧ shift ℒₒᵣ q = q := by simpa using hs
    simp [renameFormula, formulaConstruction, hp.isUFormula, hq.isUFormula] at *
    exact ⟨ihp h.1, ihq h.2⟩
  · intro n p q hp hq ihp ihq hs
    rw [shift_or hp.isUFormula hq.isUFormula] at hs
    have h : shift ℒₒᵣ p = p ∧ shift ℒₒᵣ q = q := by simpa using hs
    simp [renameFormula, formulaConstruction, hp.isUFormula, hq.isUFormula] at *
    exact ⟨ihp h.1, ihq h.2⟩
  · intro n p hp ih hs
    rw [shift_all hp.isUFormula] at hs
    have h : shift ℒₒᵣ p = p := by simpa using hs
    simp [renameFormula, formulaConstruction, hp.isUFormula] at *
    exact ih h
  · intro n p hp ih hs
    rw [shift_exs hp.isUFormula] at hs
    have h : shift ℒₒᵣ p = p := by simpa using hs
    simp [renameFormula, formulaConstruction, hp.isUFormula] at *
    exact ih h

lemma pa_axiom_fixed (param p : M) (hp : p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class) :
    renameFormula mapGraph f hf param p = p := by
  rcases (PA194PAAxiomReopen.pa_class_split p).mp hp with (hfinite | hind)
  · have he := (PA194PAAxiomReopen.finite_class (V := M) 𝗣𝗔⁻ PeanoMinus.finite p).mp hfinite
    obtain ⟨σ, _, rfl⟩ := he
    apply formula_fixed mapGraph f hf param 0 (⌜σ⌝ : M) (by simp)
    exact PA194PAAxiomReopen.sentence_quote_fixed σ
  · obtain ⟨m, hm, b, hbp, rfl, hb, hshift, hbv, _⟩ := hind
    have hformula : IsSemiformula ℒₒᵣ 0 (qqAlls b m) := by
      rw [isSemiformula_iff]
      constructor
      · exact isUFormula_qqAlls.mpr hb
      · rw [bv_qqAlls hb, hbv]; simp
    exact formula_fixed mapGraph f hf param 0 (qqAlls b m) hformula
      (PA194ShiftFixedClose.shift_qqAlls_of_fixed hb hshift m)

def liftedMapGraph : 𝚺₁.Semisentence 3 :=
  .mkSigma “y x p. ∃ k, !pi₁Def k p ∧ ∃ a, !pi₂Def a p ∧ !(PA194CodeGraph.graph PA194LiftRename.renameCode) y k a x”

lemma liftedMapGraph_correct (v : Fin 3 → M) :
    (M ⊧/v liftedMapGraph.val) ↔ v 0 = PA194LiftRename.rename (π₁ (v 2)) (π₂ (v 2)) (v 1) := by
  simp [liftedMapGraph, (PA194CodeGraph.modelGraph PA194LiftRename.renameCode).iff,
    PA194LiftRename.modelCode, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

lemma lifted_pa_axiom_fixed (k a p : M) (hp : p ∈ (𝗣𝗔 : ArithmeticTheory).Δ₁Class) :
    renameFormula liftedMapGraph (fun param x => PA194LiftRename.rename (π₁ param) (π₂ param) x)
      liftedMapGraph_correct (pair k a) p = p :=
  pa_axiom_fixed liftedMapGraph _ liftedMapGraph_correct (pair k a) p hp

#print axioms lifted_pa_axiom_fixed
#print axioms pa_axiom_fixed
#print axioms formula_fixed
#print axioms term_fixed
end models
end PA194GenericRenameAxiom
