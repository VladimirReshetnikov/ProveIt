import PA194InductionAxiomReopen
/-! Σ₁-graph-parametrized internal free-label renaming of terms and formulas.
The formula and map parameter may be nonstandard model elements. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3000000
namespace PA194GenericRenameBase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode

def termBlueprint (mapGraph : 𝚺₁.Semisentence 3) : Language.TermRec.Blueprint 1 where
  bvar := .mkSigma “y z p. !qqBvarDef y z”
  fvar := .mkSigma “y x p. ∃ w, !mapGraph w x p ∧ !qqFvarDef y w”
  func := .mkSigma “y k f v v' p. !qqFuncDef y k f v'”

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

noncomputable def termConstruction : Language.TermRec.Construction M (termBlueprint mapGraph) where
  bvar _ z := ^#z
  fvar p x := ^&(f (p 0) x)
  func _ k f _ v' := ^func k f v'
  bvar_defined := .mk fun v => by simp [termBlueprint]
  fvar_defined := .mk fun v => by simp [termBlueprint, hf, eq_comm]
  func_defined := .mk fun v => by simp [termBlueprint]

noncomputable def formulaBlueprint : UformulaRec1.Blueprint where
  rel := .mkSigma “y param k R v. ∃ w, !((termBlueprint mapGraph).resultVec ℒₒᵣ) w k v param ∧ !qqRelDef y k R w”
  nrel := .mkSigma “y param k R v. ∃ w, !((termBlueprint mapGraph).resultVec ℒₒᵣ) w k v param ∧ !qqNRelDef y k R w”
  verum := .mkSigma “y param. !qqVerumDef y”
  falsum := .mkSigma “y param. !qqFalsumDef y”
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂”
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂”
  all := .mkSigma “y param p₁ y₁. !qqAllDef y y₁”
  exs := .mkSigma “y param p₁ y₁. !qqExsDef y y₁”
  allChanges := .mkSigma “param' param. param' = param”
  exsChanges := .mkSigma “param' param. param' = param”

noncomputable def formulaConstruction : UformulaRec1.Construction M (formulaBlueprint mapGraph) where
  rel p k R v := ^rel k R ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![p] k v)
  nrel p k R v := ^nrel k R ((termConstruction mapGraph f hf).resultVec ℒₒᵣ ![p] k v)
  verum _ := ^⊤
  falsum _ := ^⊥
  and _ _ _ y₁ y₂ := y₁ ^⋏ y₂
  or _ _ _ y₁ y₂ := y₁ ^⋎ y₂
  all _ _ y := ^∀ y
  exs _ _ y := ^∃ y
  allChanges p := p
  exsChanges p := p
  rel_defined := .mk fun v => by
    simp [formulaBlueprint, (termConstruction mapGraph f hf).eval_resultVec, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  nrel_defined := .mk fun v => by
    simp [formulaBlueprint, (termConstruction mapGraph f hf).eval_resultVec, Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  verum_defined := .mk fun v => by simp [formulaBlueprint]
  falsum_defined := .mk fun v => by simp [formulaBlueprint]
  and_defined := .mk fun v => by simp [formulaBlueprint]
  or_defined := .mk fun v => by simp [formulaBlueprint]
  all_defined := .mk fun v => by simp [formulaBlueprint]
  exs_defined := .mk fun v => by simp [formulaBlueprint]
  allChanges_defined := .mk fun v => by simp [formulaBlueprint]
  exChanges_defined := .mk fun v => by simp [formulaBlueprint]


end models
end PA194GenericRenameBase
