import PA194RenameSubstitution
import Foundation.FirstOrder.Bootstrapping.Syntax.Proof.Basic
/-! Internal finite formula-context images under free-label renaming,
including shift and universal-premise compatibility. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
namespace PA194RenameContexts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194RenameSubstitution
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

noncomputable def renameSetGraph : 𝚺₁.Semisentence 3 := .mkSigma
  “t param s. (∀ y ∈' t, ∃ x ∈' s, !((formulaBlueprint mapGraph).result ℒₒᵣ) y param x) ∧
    (∀ x ∈' s, ∃ y, !((formulaBlueprint mapGraph).result ℒₒᵣ) y param x ∧ y ∈ t)”

lemma renameSet_existsUnique (param s : M) :
    ∃! t : M, ∀ y, y ∈ t ↔ ∃ x ∈ s, y = renameFormula mapGraph f hf param x := by
  haveI := formula_definable mapGraph f hf param
  exact sigma₁_replacement (by definability) s

noncomputable def renameSet (param s : M) : M := Classical.choose! (renameSet_existsUnique mapGraph f hf param s)

lemma mem_renameSet_iff {param s y : M} : y ∈ renameSet mapGraph f hf param s ↔ ∃ x ∈ s, y = renameFormula mapGraph f hf param x :=
  Classical.choose!_spec (renameSet_existsUnique mapGraph f hf param s) y

lemma renameSet_graph (param s t : M) :
    t = renameSet mapGraph f hf param s ↔
      (∀ y ∈ t, ∃ x ∈ s, y = renameFormula mapGraph f hf param x) ∧
      (∀ x ∈ s, renameFormula mapGraph f hf param x ∈ t) := by
  constructor
  · rintro rfl
    constructor
    · intro y hy; exact (mem_renameSet_iff mapGraph f hf).mp hy
    · intro x hx; exact (mem_renameSet_iff mapGraph f hf).mpr ⟨x, hx, rfl⟩
  · rintro ⟨h₁,h₂⟩
    apply mem_ext; intro y; constructor
    · intro hy; exact (mem_renameSet_iff mapGraph f hf).mpr (h₁ y hy)
    · intro hy
      obtain ⟨x,hx,rfl⟩ := (mem_renameSet_iff mapGraph f hf).mp hy
      exact h₂ x hx

lemma renameSet_defined : 𝚺₁-Function₂ (renameSet mapGraph f hf) via renameSetGraph mapGraph := by
  apply HierarchySymbol.Defined.mk
  intro v
  simp [renameSetGraph, (formulaConstruction mapGraph f hf).result_defined.iff,
    renameFormula, renameSet_graph, Matrix.comp_vecCons', Matrix.constant_eq_singleton]

#print axioms renameSet_defined
lemma renameSet_insert (param p s : M) :
    renameSet mapGraph f hf param (insert p s) = insert (renameFormula mapGraph f hf param p) (renameSet mapGraph f hf param s) := by
  apply mem_ext; intro y
  simp [mem_renameSet_iff]

lemma renameSet_wf (param s : M) (hs : IsFormulaSet ℒₒᵣ s) : IsFormulaSet ℒₒᵣ (renameSet mapGraph f hf param s) := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := (mem_renameSet_iff mapGraph f hf).mp hy
  exact formula_wf mapGraph f hf param 0 x (hs x hx)

lemma renameSet_shift (p q s : M) (hs : IsFormulaSet ℒₒᵣ s)
    (hmap : ∀ x, f p (x+1) = f q x + 1) :
    renameSet mapGraph f hf p (setShift ℒₒᵣ s) = setShift ℒₒᵣ (renameSet mapGraph f hf q s) := by
  apply mem_ext; intro y
  simp only [mem_renameSet_iff, mem_setShift_iff]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, formula_rename_shift mapGraph f hf p q 0 x (hs x hx) hmap⟩
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (formula_rename_shift mapGraph f hf p q 0 x (hs x hx) hmap).symm⟩

lemma renameSet_shift_noshift (p q s : M) (hs : IsFormulaSet ℒₒᵣ s)
    (hmap : ∀ x, f p (x+1) = f q x) :
    renameSet mapGraph f hf p (setShift ℒₒᵣ s) = renameSet mapGraph f hf q s := by
  apply mem_ext; intro y
  simp only [mem_renameSet_iff, mem_setShift_iff]
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, formula_rename_shift_noshift mapGraph f hf p q 0 x (hs x hx) hmap⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, (formula_rename_shift_noshift mapGraph f hf p q 0 x (hs x hx) hmap).symm⟩

lemma renameSet_allPremise (p q φ s : M) (hφ : IsSemiformula ℒₒᵣ 1 φ) (hs : IsFormulaSet ℒₒᵣ s)
    (hzero : f p 0 = 0) (hmap : ∀ x, f p (x+1) = f q x+1) :
    renameSet mapGraph f hf p (insert (free ℒₒᵣ φ) (setShift ℒₒᵣ s)) =
      insert (free ℒₒᵣ (renameFormula mapGraph f hf q φ)) (setShift ℒₒᵣ (renameSet mapGraph f hf q s)) := by
  rw [renameSet_insert, formula_rename_free mapGraph f hf p q φ hφ hzero hmap,
    renameSet_shift mapGraph f hf p q s hs hmap]

lemma expanded_allPremise (k a d e φ s : M) (hφ : IsSemiformula ℒₒᵣ 1 φ) (hs : IsFormulaSet ℒₒᵣ s) :
    renameSet PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair (k+1) (pair a (pair d e))) (insert (free ℒₒᵣ φ) (setShift ℒₒᵣ s)) =
    insert (free ℒₒᵣ (renameFormula PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
      (pair k (pair a (pair d e))) φ))
      (setShift ℒₒᵣ (renameSet PA194ExpandedRename.expandedGraph PA194ExpandedRename.packedRen PA194ExpandedRename.expandedGraph_correct
        (pair k (pair a (pair d e))) s)) := by
  apply renameSet_allPremise _ _ _ _ _ φ s hφ hs
  · simpa [PA194ExpandedRename.packedRen] using PA194ExpandedRename.lift_zero k a d e
  · intro x
    simpa [PA194ExpandedRename.packedRen] using PA194ExpandedRename.lift_succ k a d e x

#print axioms expanded_allPremise
#print axioms renameSet_allPremise
#print axioms renameSet_shift_noshift
#print axioms renameSet_wf
#print axioms renameSet_insert
end models
end PA194RenameContexts
