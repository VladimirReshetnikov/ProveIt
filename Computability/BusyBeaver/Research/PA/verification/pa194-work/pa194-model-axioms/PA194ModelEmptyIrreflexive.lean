import PA194ModelSeparationAxiom

/-!
# The empty set and irreflexivity of membership, at model level

Two fixed sentences of the relational source language that the standard development
supplies in the calculus (`emptySupplier`, `irSupplier`), here for a candidate-PRA model `M`
whose arithmetic reduct satisfies `𝗜𝚺₁` and arbitrary labels of `M`.

* `irreflexivity_target`: `∀x ¬(x ∈ x)`. At the label `0` the membership `0 ∈ 0` is the code
  of falsum, and the bound label is then moved to `x` (`transferBinder_target`).
* `emptySetAtName_target`: `∃c ∀b ¬(b ∈ c)` for `c ≠ b`, from separation with the property
  falsum (`separationAtName_target`); the auxiliary labels are chosen above `b` and `c`.
* `sourceIrreflexivity`, `sourceEmptySet`: the two sentences, with explicit model-valued
  quotes (`irrRoot_quote`, `emptyRoot_quote`).
* `fixedFormulaTranslation_irreflexivity_target`, `fixedFormulaTranslation_emptySet_target`:
  the fixed formula translations are target-provable for arbitrary stacks and labels, with
  no condition on the reserved label.
* `simRuleIrreflexivity`, `simRuleEmptySet`: the axiom leaves of a simulation.

No simulation is constructed, and nothing here yields a consistency implication.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

def sourceIrreflexivity : Sentence M6.PA.RelationalSource.language :=
  ∀⁰ (Semiformula.nrel M6.PA.RelationalSource.Relation.mem ![#0,#0])

def sourceEmptySet : Sentence M6.PA.RelationalSource.language :=
  ∃⁰ ∀⁰ (Semiformula.nrel M6.PA.RelationalSource.Relation.mem ![#0,#1])

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance emptyIrrZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance emptyIrrOne : One M := ⟨F oneCode Fin.elim0⟩
local instance emptyIrrAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance emptyIrrMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance emptyIrrLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance emptyIrrIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The membership `0 ∈ 0` is the code of falsum. -/
theorem memValue_zero_zero : memValue (0 : M) 0 = 1 := by
  simp [memValue,impValue,cantor,triangle]

/-- **Irreflexivity of membership**, for an arbitrary bound label. -/
theorem irreflexivity_target (x : M) : TargetProvable (allValue x (negValue (memValue x x))) := by
  have raw : TargetProvable (allValue (0 : M) (negValue (memValue (0 : M) 0))) := by
    rw [memValue_zero_zero]
    exact tp_gen 0 (imp_refl 1)
  by_cases hx : x = 0
  · rw [hx]
    exact raw
  · have h0 : (0 : M) ≠ x := Ne.symm hx
    let atom : M := negValue (memValue (0 : M) 0)
    let target : M := negValue (memValue x x)
    have hvT : TargetProvable (impValue target (allValue 0 target)) :=
      negationVacuity 0 _ (membershipVacuity_target x x 0 h0 h0)
    have hvA : TargetProvable (impValue (allValue 0 atom) (allValue x (allValue 0 atom))) :=
      universalVacuity x 0 atom (negationVacuity x _ (membershipVacuity_target 0 0 x hx hx))
    have hr : TargetProvable (impValue (eqValue x 0) (impValue atom target)) := by
      let he : Ctx [memValue x x,atom,eqValue x 0] (eqValue x 0) := .assumption (by simp)
      let hn : Ctx [memValue x x,atom,eqValue x 0] (negValue (memValue (0 : M) 0)) :=
        .assumption (by simp [atom])
      let hm : Ctx [memValue x x,atom,eqValue x 0] (memValue x x) := .assumption (by simp)
      let h1 : Ctx [memValue x x,atom,eqValue x 0] (memValue 0 x) :=
        .mp hm (.mp he (.closed (memLeft x 0 x)))
      let h2 : Ctx [memValue x x,atom,eqValue x 0] (memValue (0 : M) 0) :=
        .mp h1 (.mp he (.closed (memRight x 0 0)))
      let h3 : Ctx [memValue x x,atom,eqValue x 0] 1 := .mp h2 hn
      let h4 : Ctx [atom,eqValue x 0] (negValue (memValue x x)) := h3.deduction
      exact h4.deduction.deduction.empty
    exact tp_mp raw (transferBinder_target 0 x atom target hvT hvA hr)

/-- **The empty set**: some `c` has no member. -/
theorem emptySetAtName_target (c b : M) (hcb : c ≠ b) :
    TargetProvable (exValue c (allValue b (negValue (memValue c b)))) := by
  let s : M := c + b
  let z : M := s + 1
  let a : M := (s + 1) + 1
  let q : M := ((s + 1) + 1) + 1
  have hcs : c ≤ s := le_self_add
  have hbs : b ≤ s := le_add_self
  have hsz : s < z := lt_add_one s
  have hza : z < a := lt_add_one (s + 1)
  have haq : a < q := lt_add_one ((s + 1) + 1)
  have hcz : c < z := lt_of_le_of_lt hcs hsz
  have hbz : b < z := lt_of_le_of_lt hbs hsz
  have hsep : TargetProvable (exValue c (separationBody a b 1 c)) :=
    separationAtName_target a b c z 1 q haq (lt_trans hbz (lt_trans hza haq))
      (lt_trans hcz (lt_trans hza haq)) (lt_trans hza haq)
      (ne_of_lt (lt_trans hcz hza)) hcb (ne_of_gt hbz) (ne_of_gt hcz)
      (explosion _) (explosion _) (explosion _)
  have hpt : TargetProvable (impValue (iffValue (memValue c b) (conjValue (memValue a b) 1))
      (negValue (memValue c b))) := by
    let hI : Ctx [memValue c b,iffValue (memValue c b) (conjValue (memValue a b) 1)]
        (conjValue (impValue (memValue c b) (conjValue (memValue a b) 1))
          (impValue (conjValue (memValue a b) 1) (memValue c b))) :=
      .assumption (by simp [iffValue])
    let hm : Ctx [memValue c b,iffValue (memValue c b) (conjValue (memValue a b) 1)]
        (memValue c b) := .assumption (by simp)
    let hX : Ctx [memValue c b,iffValue (memValue c b) (conjValue (memValue a b) 1)]
        (conjValue (memValue a b) 1) := .mp hm hI.andLeft
    let hbot : Ctx [memValue c b,iffValue (memValue c b) (conjValue (memValue a b) 1)] 1 :=
      hX.andRight
    let hneg : Ctx [iffValue (memValue c b) (conjValue (memValue a b) 1)]
        (negValue (memValue c b)) := hbot.deduction
    exact hneg.deduction.empty
  unfold separationBody at hsep
  exact tp_mp hsep (existentialMonotonicity c (liftImp b hpt))

noncomputable def irrRoot : M := ^∀ (^nrel (2 : M) (1 : M) (relExtVector 0 0))
noncomputable def emptyRoot : M := ^∃ (^∀ (^nrel (2 : M) (1 : M) (relExtVector 0 1)))

theorem irrRoot_quote : (⌜sourceIrreflexivity⌝ : M) = irrRoot := by
  simp [Sentence.quote_def, sourceIrreflexivity, Semiformula.quote_all, irrRoot,
    relExtVector, Matrix.vecHead, Matrix.vecTail, Function.comp_def, adjoin_def]
  change ((1 : ℕ) : M) = 1
  simp

theorem emptyRoot_quote : (⌜sourceEmptySet⌝ : M) = emptyRoot := by
  simp [Sentence.quote_def, sourceEmptySet, Semiformula.quote_all, emptyRoot,
    relExtVector, Matrix.vecHead, Matrix.vecTail, Function.comp_def, adjoin_def]
  change ((1 : ℕ) : M) = 1
  simp

/-- The translation of the irreflexivity code, for arbitrary stacks and labels. -/
theorem fixedFormulaTranslation_irrRoot (initial free base reserve : M) :
    F fixedFormulaTranslation ![irrRoot,initial,free,base,reserve] =
      allValue base (negValue (memValue base base)) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hneg : IsUFormula SourceL (^nrel (2 : M) (1 : M) (relExtVector 0 0)) := by
    simp only [IsUFormula.nrel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 0⟩
  rw [irrRoot,fixedFormulaTranslation_all _ _ _ _ _ hneg,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr (relExt_vector_valid 0 0)]
  simp only [fixedTranslation_membershipBound,nth_cons_zero']

/-- The translation of the empty-set code, for arbitrary stacks and labels. -/
theorem fixedFormulaTranslation_emptyRoot (initial free base reserve : M) :
    F fixedFormulaTranslation ![emptyRoot,initial,free,base,reserve] =
      exValue base (allValue (base+1) (negValue (memValue base (base+1)))) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hneg : IsUFormula SourceL (^nrel (2 : M) (1 : M) (relExtVector 0 1)) := by
    simp only [IsUFormula.nrel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 1⟩
  have hall : IsUFormula SourceL (^∀ (^nrel (2 : M) (1 : M) (relExtVector 0 1))) := by
    simpa only [IsUFormula.all] using hneg
  rw [emptyRoot,fixedFormulaTranslation_ex _ _ _ _ _ hall,
    fixedFormulaTranslation_all _ _ _ _ _ hneg,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr (relExt_vector_valid 0 1)]
  simp only [fixedTranslation_membershipBound,nth_cons_zero',nth_cons_one']

/-- **The translation of the quoted irreflexivity sentence is target-provable.** -/
theorem fixedFormulaTranslation_irreflexivity_target (initial free base reserve : M) :
    TargetProvable (F fixedFormulaTranslation
      ![(⌜sourceIrreflexivity⌝ : M),initial,free,base,reserve]) := by
  rw [irrRoot_quote,fixedFormulaTranslation_irrRoot]
  exact irreflexivity_target base

/-- **The translation of the quoted empty-set sentence is target-provable.** -/
theorem fixedFormulaTranslation_emptySet_target (initial free base reserve : M) :
    TargetProvable (F fixedFormulaTranslation
      ![(⌜sourceEmptySet⌝ : M),initial,free,base,reserve]) := by
  rw [emptyRoot_quote,fixedFormulaTranslation_emptyRoot]
  exact emptySetAtName_target base (base+1) (ne_of_lt (lt_add_one base))

theorem simRuleIrreflexivity (e : M) :
    TargetProvable (impValue (negatedTranslation e (⌜sourceIrreflexivity⌝ : M)) 1) :=
  positiveTarget_rule e _
    (fixedFormulaTranslation_irreflexivity_target (simBound e) (simFree e) (simBase e)
      (simReserve e))

theorem simRuleEmptySet (e : M) :
    TargetProvable (impValue (negatedTranslation e (⌜sourceEmptySet⌝ : M)) 1) :=
  positiveTarget_rule e _
    (fixedFormulaTranslation_emptySet_target (simBound e) (simFree e) (simBase e)
      (simReserve e))

#print axioms irreflexivity_target
#print axioms emptySetAtName_target
#print axioms irrRoot_quote
#print axioms emptyRoot_quote
#print axioms fixedFormulaTranslation_irreflexivity_target
#print axioms fixedFormulaTranslation_emptySet_target
#print axioms simRuleIrreflexivity
#print axioms simRuleEmptySet
end models
end PA194ModelLogic
