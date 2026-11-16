import PA194ModelStandardEqSequent
import PA194ModelFormulaTranslation
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.HierarchySymbol.Semiformula
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance eqTheoryInstanceZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance eqTheoryInstanceOne : One M := ⟨F oneCode Fin.elim0⟩
local instance eqTheoryInstanceAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance eqTheoryInstanceMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance eqTheoryInstanceLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance eqTheoryInstanceIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageEqTheory : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

def finiteEqList : List (Sentence M6.PA.RelationalSource.language) :=
  [sourceEqRefl,sourceEqSymm,sourceEqTrans,sourceEqRelExt,PA194RelExtTypedTranslation.sourceRelExt]

theorem finiteEqListTheory : {σ | σ ∈ finiteEqList} =
    Theory.eqAxiom M6.PA.RelationalSource.language := by
  ext σ
  constructor
  · intro h
    simp only [finiteEqList,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h | h | h | h | h <;> subst σ
    · exact Theory.eqAxiom.refl
    · exact Theory.eqAxiom.symm
    · exact Theory.eqAxiom.trans
    · exact Theory.eqAxiom.relExt (L := M6.PA.RelationalSource.language) M6.PA.RelationalSource.Relation.eq
    · exact Theory.eqAxiom.relExt (L := M6.PA.RelationalSource.language) M6.PA.RelationalSource.Relation.mem
  · intro h
    simp only [finiteEqList,List.mem_cons,List.not_mem_nil,or_false]
    cases h with
    | refl => exact Or.inl rfl
    | symm => exact Or.inr (Or.inl rfl)
    | trans => exact Or.inr (Or.inr (Or.inl rfl))
    | funcExt f => nomatch f
    | relExt r =>
      cases r with
      | eq => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
      | mem => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

def finiteEqTheoryFormula : 𝚺₀.Semisentence 1 := .mkSigma
  “x. x = ↑(Encodable.encode sourceEqRefl) ∨
    x = ↑(Encodable.encode sourceEqSymm) ∨ x = ↑(Encodable.encode sourceEqTrans) ∨
    x = ↑(Encodable.encode sourceEqRelExt) ∨
    x = ↑(Encodable.encode PA194RelExtTypedTranslation.sourceRelExt)”

@[implicit_reducible] noncomputable def finiteEqTheoryDelta : (Theory.eqAxiom M6.PA.RelationalSource.language).Δ₁ where
  ch := .ofZero finiteEqTheoryFormula _
  mem_iff := by
    intro φ
    rw [←finiteEqListTheory]
    simp [finiteEqTheoryFormula, finiteEqList, Semiformula.quote_eq_encode]
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

theorem finiteEqTheory_class (p : M) :
    letI := finiteEqTheoryDelta
    p ∈ (Theory.eqAxiom M6.PA.RelationalSource.language).Δ₁Class ↔ finiteEqAxiomCode p := by
  letI := finiteEqTheoryDelta
  change M ⊧/![p] (finiteEqTheoryFormula.val) ↔ finiteEqAxiomCode p
  simp [finiteEqTheoryFormula, finiteEqAxiomCode, Sentence.quote_eq_encode, numeral_eq_natCast]

/-- The axiom-leaf sequent clause for Foundation's Δ₁ class under the
explicit five-element presentation of the source equality theory. -/
theorem finiteEqTheory_axiom_sseq (bound free base reserve p s : M)
    (hz : base+p ≤ reserve) (hp : p ∈ s) :
    letI := finiteEqTheoryDelta
    p ∈ (Theory.eqAxiom M6.PA.RelationalSource.language).Δ₁Class →
    TargetProvable (ConPA.Sequent.sseq numericalCalc numericalTranslation
      (pair bound (pair free (pair base reserve))) s 1) := by
  letI := finiteEqTheoryDelta
  intro hax
  exact finiteEqAxiom_sseq bound free base reserve p s
    ((finiteEqTheory_class p).mp hax) hz hp

#print axioms finiteEqTheory_axiom_sseq
#print axioms finiteEqTheory_class
#print axioms finiteEqListTheory
#print axioms finiteEqTheoryDelta
end models
end PA194ModelLogic
