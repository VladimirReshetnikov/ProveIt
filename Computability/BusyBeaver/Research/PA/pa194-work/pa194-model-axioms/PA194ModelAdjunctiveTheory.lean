import PA194ModelWeakAdjunctionAxiom
import PA194ModelSimAxiomRules

/-!
# A source theory with weak adjunction, and its axiom rule

`adjunctiveTheory` is the theory of the relational source language whose axioms are the five
equality axioms of `Theory.eqAxiom` and the weak-adjunction sentence. It has an explicit `Δ₁`
presentation (a disjunction of six equations), so Foundation's internal derivations of it are
available in every model of `𝗜𝚺₁`.

* `adjunctiveTheory_eq`: the theory is `Theory.eqAxiom ∪ {sourceWeakAdjunction}`.
* `adjunctiveTheory_class`: in a model, the internal axiom class is "one of the five quoted
  equality axioms, or the quoted weak-adjunction sentence".
* `simRuleAdjunctiveAxiom`: the axiom field of a simulation for this theory, for the numerical
  calculus and the fixed formula translation, under the reserve bound
  `base + p ≤ reserve` that `pa194-model-logic` uses for the equality axioms.

This discharges one field of a simulation for a theory larger than the equality theory. No
simulation is constructed, and nothing here yields a consistency implication.
-/
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
local instance adjTheoryZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance adjTheoryOne : One M := ⟨F oneCode Fin.elim0⟩
local instance adjTheoryAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance adjTheoryMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance adjTheoryLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance adjTheoryIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local instance sourceLanguageAdjTheory : Language.Eq M6.PA.RelationalSource.language :=
  ⟨M6.PA.RelationalSource.Relation.eq⟩

def adjunctiveList : List (Sentence M6.PA.RelationalSource.language) :=
  [sourceEqRefl,sourceEqSymm,sourceEqTrans,sourceEqRelExt,
    PA194RelExtTypedTranslation.sourceRelExt,sourceWeakAdjunction]

/-- The equality axioms of the relational source language together with weak adjunction. -/
def adjunctiveTheory : Theory M6.PA.RelationalSource.language := {σ | σ ∈ adjunctiveList}

theorem adjunctiveTheory_eq :
    adjunctiveTheory = Theory.eqAxiom M6.PA.RelationalSource.language ∪ {sourceWeakAdjunction} := by
  rw [←finiteEqListTheory]
  ext σ
  simp [adjunctiveTheory,adjunctiveList,finiteEqList]
  tauto

def adjunctiveTheoryFormula : 𝚺₀.Semisentence 1 := .mkSigma
  “x. x = ↑(Encodable.encode sourceEqRefl) ∨
    x = ↑(Encodable.encode sourceEqSymm) ∨ x = ↑(Encodable.encode sourceEqTrans) ∨
    x = ↑(Encodable.encode sourceEqRelExt) ∨
    x = ↑(Encodable.encode PA194RelExtTypedTranslation.sourceRelExt) ∨
    x = ↑(Encodable.encode sourceWeakAdjunction)”

@[implicit_reducible] noncomputable def adjunctiveTheoryDelta : adjunctiveTheory.Δ₁ where
  ch := .ofZero adjunctiveTheoryFormula _
  mem_iff := by
    intro φ
    simp [adjunctiveTheory, adjunctiveTheoryFormula, adjunctiveList, Semiformula.quote_eq_encode]
  isDelta1 := ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by simp

/-- The internal axiom class of the theory, in a model. -/
theorem adjunctiveTheory_class (p : M) :
    letI := adjunctiveTheoryDelta
    p ∈ adjunctiveTheory.Δ₁Class ↔
      finiteEqAxiomCode p ∨ p = (⌜sourceWeakAdjunction⌝ : M) := by
  letI := adjunctiveTheoryDelta
  change M ⊧/![p] (adjunctiveTheoryFormula.val) ↔ _
  simp [adjunctiveTheoryFormula, finiteEqAxiomCode, Sentence.quote_eq_encode, numeral_eq_natCast,
    or_assoc]

/-- The axiom rule for the theory, with the weak-adjunction reserve bound separate. -/
theorem adjunctiveTheory_axiom_rule (e p : M) (hz : simBase e + p ≤ simReserve e)
    (hw : ((simBase e+1)+1)+1 < simReserve e) :
    letI := adjunctiveTheoryDelta
    p ∈ adjunctiveTheory.Δ₁Class →
    TargetProvable (impValue (negatedTranslation e p) 1) := by
  letI := adjunctiveTheoryDelta
  intro hax
  rcases (adjunctiveTheory_class p).mp hax with h | h
  · have hrule := finiteEqTheory_axiom_rule e p hz
    exact hrule ((finiteEqTheory_class p).mpr h)
  · subst h
    exact simRuleWeakAdjunction e hw

theorem succ_le_succ_model {x y : M} (h : x ≤ y) : x+1 ≤ y+1 := by
  simpa only [add_comm] using add_le_add_right h 1

/-- The code of the weak-adjunction sentence is at least four, so the reserve bound of the
axiom rule covers its four binder labels. -/
theorem four_le_weakAdjRoot : ((((0 : M)+1)+1)+1)+1 ≤ weakAdjRoot := by
  have ha (p : M) : p+1 ≤ ^∀ p := by
    change p+1 ≤ pair (6 : M) p+1
    exact succ_le_succ_model (le_pair_right (6 : M) p)
  have he (p : M) : p+1 ≤ ^∃ p := by
    change p+1 ≤ pair (7 : M) p+1
    exact succ_le_succ_model (le_pair_right (7 : M) p)
  have hc (p q : M) : p+1 ≤ p ^⋏ q := by
    change p+1 ≤ pair (4 : M) (pair p q)+1
    exact succ_le_succ_model (le_trans (le_pair_left p q) (le_pair_right (4 : M) (pair p q)))
  have h1 : (0 : M)+1 ≤ ^∀ (weakAdjInner (M := M)) := le_trans (succ_le_succ_model zero_le) (ha _)
  have h2 : ((0 : M)+1)+1 ≤ weakAdjBody := by
    unfold weakAdjBody
    exact le_trans (succ_le_succ_model h1) (hc _ _)
  have h3 : (((0 : M)+1)+1)+1 ≤ ^∃ (weakAdjBody (M := M)) :=
    le_trans (succ_le_succ_model h2) (he _)
  have h4 : ((((0 : M)+1)+1)+1)+1 ≤ ^∀ (^∃ (weakAdjBody (M := M))) :=
    le_trans (succ_le_succ_model h3) (ha _)
  unfold weakAdjRoot
  exact le_trans h4 (le_trans (le_of_lt (lt_add_one _)) (ha _))

theorem weakAdjunction_reserve (base reserve : M)
    (hz : base + (⌜sourceWeakAdjunction⌝ : M) ≤ reserve) : ((base+1)+1)+1 < reserve := by
  rw [weakAdjRoot_quote] at hz
  obtain ⟨b,hb⟩ := le_iff_exists_add.mp (four_le_weakAdjRoot (M := M))
  have hlt : ((base+1)+1)+1 < (((base+1)+1)+1)+1 := lt_add_one _
  have hle : (((base+1)+1)+1)+1 ≤ base + weakAdjRoot := by
    rw [hb]
    have : base + (((((0 : M)+1)+1)+1)+1 + b) = ((((base+1)+1)+1)+1) + b := by
      simp only [zero_add,add_assoc]
    rw [this]
    exact le_self_add
  exact lt_of_lt_of_le hlt (le_trans hle hz)

/-- **The axiom field of a simulation for the theory with weak adjunction**, under the
single reserve bound used for the equality axioms. -/
theorem simRuleAdjunctiveAxiom (e p : M) (hz : simBase e + p ≤ simReserve e) :
    letI := adjunctiveTheoryDelta
    p ∈ adjunctiveTheory.Δ₁Class →
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1) := by
  letI := adjunctiveTheoryDelta
  intro hax
  rcases (adjunctiveTheory_class p).mp hax with h | h
  · have hrule := finiteEqTheory_axiom_rule e p hz
    exact hrule ((finiteEqTheory_class p).mpr h)
  · subst h
    exact simRuleWeakAdjunction e (weakAdjunction_reserve _ _ hz)

#print axioms adjunctiveTheory_eq
#print axioms adjunctiveTheoryDelta
#print axioms adjunctiveTheory_class
#print axioms adjunctiveTheory_axiom_rule
#print axioms four_le_weakAdjRoot
#print axioms simRuleAdjunctiveAxiom
end models
end PA194ModelLogic
