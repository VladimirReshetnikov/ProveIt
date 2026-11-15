import PA194ModelWeakAdjunction

/-!
# The translated weak-adjunction sentence is a theorem of the numerical calculus

In a candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`.

`sourceWeakAdjunction` is the weak-adjunction sentence of the relational source language,
`∀a ∀b ∃c ((∀m (m ∈ a → m ∈ c)) ∧ b ∈ c)`, with the implication written as a disjunction as in
`M6.PA.RelationalSource.weakAdjunctionFormula`. This file evaluates the fixed formula
translation of `pa194-model-logic` on the model-valued quote of that sentence, for arbitrary
bound and free stacks and labels, and identifies the result with the code proved by
`weakAdjunction_supplier`.

* `weakAdjRoot_quote`: the quote of the sentence is the explicit code `weakAdjRoot`.
* `fixedFormulaTranslation_weakAdjRoot`: the translation of `weakAdjRoot`, with the four
  binder labels `base, base+1, base+2, base+3`.
* `fixedFormulaTranslation_weakAdjunction_target`: the translation is target-provable when
  the reserved label differs from `base+1`, `base+2`, `base+3`.
* `simRuleWeakAdjunction`: the corresponding leaf for the negated translation of a
  simulation, `(¬ tr e ⌜σ⌝) → 1`.

This is one fixed source axiom. Nothing here constructs a simulation or yields a
consistency implication.
-/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
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

/-- Weak adjunction in the relational source language: for all `a`, `b` there is `c` that
contains every member of `a` and contains `b`. -/
def sourceWeakAdjunction : Sentence M6.PA.RelationalSource.language :=
  ∀⁰ ∀⁰ ∃⁰ ((∀⁰ (Semiformula.nrel M6.PA.RelationalSource.Relation.mem ![#0,#3] ⋎
      Semiformula.rel M6.PA.RelationalSource.Relation.mem ![#0,#1])) ⋏
    Semiformula.rel M6.PA.RelationalSource.Relation.mem ![#1,#0])

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance weakAdjAxZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance weakAdjAxOne : One M := ⟨F oneCode Fin.elim0⟩
local instance weakAdjAxAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance weakAdjAxMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance weakAdjAxLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance weakAdjAxIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def weakAdjInner : M :=
  (^nrel (2 : M) (1 : M) (relExtVector 0 3)) ^⋎ (^rel (2 : M) (1 : M) (relExtVector 0 1))
noncomputable def weakAdjBody : M :=
  (^∀ (weakAdjInner (M := M))) ^⋏ (^rel (2 : M) (1 : M) (relExtVector 1 0))
noncomputable def weakAdjRoot : M := ^∀ (^∀ (^∃ (weakAdjBody (M := M))))

theorem weakAdjRoot_quote : (⌜sourceWeakAdjunction⌝ : M) = weakAdjRoot := by
  simp [Sentence.quote_def, sourceWeakAdjunction, Semiformula.quote_all, weakAdjRoot,
    weakAdjBody, weakAdjInner, relExtVector, Matrix.vecHead, Matrix.vecTail,
    Function.comp_def, adjoin_def]
  change ((1 : ℕ) : M) = 1
  simp

theorem weakAdjInner_valid :
    IsUFormula M6.PA.RelationalSource.language (weakAdjInner (M := M)) := by
  simp only [weakAdjInner,IsUFormula.or,IsUFormula.nrel,IsUFormula.rel]
  exact ⟨⟨relExt_relation_one,relExt_vector_valid 0 3⟩,⟨relExt_relation_one,relExt_vector_valid 0 1⟩⟩

theorem weakAdjBody_valid :
    IsUFormula M6.PA.RelationalSource.language (weakAdjBody (M := M)) := by
  simp only [weakAdjBody,IsUFormula.and,IsUFormula.all,IsUFormula.rel]
  exact ⟨weakAdjInner_valid,relExt_relation_one,relExt_vector_valid 1 0⟩

theorem weakAdjRoot_valid :
    IsUFormula M6.PA.RelationalSource.language (weakAdjRoot (M := M)) := by
  simpa only [weakAdjRoot,IsUFormula.all,IsUFormula.ex] using weakAdjBody_valid (M := M)

/-- A positive membership atom on two bound variables reads the two labels from the bound
stack. -/
theorem fixedTranslation_membershipBound (i j bound free base reserve : M) :
    F fixedFormulaTranslation ![^rel (2 : M) (1 : M) (relExtVector i j),bound,free,base,reserve] =
      memValue (bound.[j]) (bound.[i]) := by
  have hr : M6.PA.RelationalSource.language.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hv := relExt_vector_valid (M := M) i j
  rw [fixedFormulaTranslation_positiveAtom _ _ _ _ _ _ hr hv]
  simp only [Arithmetic.one_ne_zero,ite_false]
  unfold relExtVector
  rw [membershipAtom_model (^#i) (^#j) bound free reserve,termLabel_bound_nth,termLabel_bound_nth]

theorem nth_cons_zero' (x v : M) : (pair x v + 1).[0] = x := by
  rw [←adjoin_def,nth_adjoin_zero]

theorem nth_cons_succ' (x v i : M) : (pair x v + 1).[i+1] = v.[i] := by
  rw [←adjoin_def,nth_adjoin_succ]

theorem nth_cons_one' (x y v : M) : (pair x (pair y v + 1) + 1).[1] = y := by
  have h := nth_cons_succ' x (pair y v + 1) 0
  rw [zero_add] at h
  rw [h,nth_cons_zero']

theorem nth_cons_three' (x0 x1 x2 x3 v : M) :
    (pair x0 (pair x1 (pair x2 (pair x3 v + 1) + 1) + 1) + 1).[3] = x3 := by
  have e : (0 : M) + 1 + 1 + 1 = 3 := by norm_num
  have h := nth_cons_succ' x0 (pair x1 (pair x2 (pair x3 v + 1) + 1) + 1) (0+1+1)
  rw [e] at h
  rw [h,nth_cons_succ',nth_cons_succ',nth_cons_zero']

/-- The translation of the weak-adjunction code, for arbitrary stacks and labels. -/
theorem fixedFormulaTranslation_weakAdjRoot (initial free base reserve : M) :
    F fixedFormulaTranslation ![weakAdjRoot,initial,free,base,reserve] =
      allValue base (allValue (base+1) (exValue ((base+1)+1)
        (conjValue
          (allValue (((base+1)+1)+1)
            (impValue (negValue (negValue (memValue base (((base+1)+1)+1))))
              (memValue ((base+1)+1) (((base+1)+1)+1))))
          (memValue ((base+1)+1) (base+1))))) := by
  have hr : M6.PA.RelationalSource.language.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hneg : IsUFormula M6.PA.RelationalSource.language
      (^nrel (2 : M) (1 : M) (relExtVector 0 3)) := by
    simp only [IsUFormula.nrel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 3⟩
  have hpos : IsUFormula M6.PA.RelationalSource.language
      (^rel (2 : M) (1 : M) (relExtVector 0 1)) := by
    simp only [IsUFormula.rel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 1⟩
  have hpt : IsUFormula M6.PA.RelationalSource.language
      (^rel (2 : M) (1 : M) (relExtVector 1 0)) := by
    simp only [IsUFormula.rel]
    exact ⟨relExt_relation_one,relExt_vector_valid 1 0⟩
  have hall : IsUFormula M6.PA.RelationalSource.language (^∀ (weakAdjInner (M := M))) := by
    simpa only [IsUFormula.all] using weakAdjInner_valid (M := M)
  have hex : IsUFormula M6.PA.RelationalSource.language (^∃ (weakAdjBody (M := M))) := by
    simpa only [IsUFormula.ex] using weakAdjBody_valid (M := M)
  have hallex : IsUFormula M6.PA.RelationalSource.language (^∀ (^∃ (weakAdjBody (M := M)))) := by
    simpa only [IsUFormula.all] using hex
  rw [weakAdjRoot,fixedFormulaTranslation_all _ _ _ _ _ hallex,
    fixedFormulaTranslation_all _ _ _ _ _ hex,
    fixedFormulaTranslation_ex _ _ _ _ _ weakAdjBody_valid,weakAdjBody,
    fixedFormulaTranslation_and _ _ _ _ _ _ hall hpt,
    fixedFormulaTranslation_all _ _ _ _ _ weakAdjInner_valid,weakAdjInner,
    fixedFormulaTranslation_or _ _ _ _ _ _ hneg hpos,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr (relExt_vector_valid 0 3),
    fixedTranslation_membershipBound,fixedTranslation_membershipBound,
    fixedTranslation_membershipBound,
    nth_cons_three',nth_cons_zero',nth_cons_one',nth_cons_zero',nth_cons_one']

/-- **The translation of the quoted weak-adjunction sentence is target-provable.** -/
theorem fixedFormulaTranslation_weakAdjunction_target (initial free base reserve : M)
    (h1 : reserve ≠ base+1) (h2 : reserve ≠ (base+1)+1) (h3 : reserve ≠ ((base+1)+1)+1) :
    TargetProvable (F fixedFormulaTranslation
      ![(⌜sourceWeakAdjunction⌝ : M),initial,free,base,reserve]) := by
  rw [weakAdjRoot_quote,fixedFormulaTranslation_weakAdjRoot]
  exact weakAdjunction_supplier base reserve h1 h2 h3

/-- The same when the reserved label lies above the four binder labels. -/
theorem fixedFormulaTranslation_weakAdjunction_target_of_lt (initial free base reserve : M)
    (h : ((base+1)+1)+1 < reserve) :
    TargetProvable (F fixedFormulaTranslation
      ![(⌜sourceWeakAdjunction⌝ : M),initial,free,base,reserve]) := by
  have l2 : (base+1)+1 < reserve := lt_trans (lt_add_one _) h
  have l1 : base+1 < reserve := lt_trans (lt_add_one _) l2
  exact fixedFormulaTranslation_weakAdjunction_target initial free base reserve
    (ne_of_gt l1) (ne_of_gt l2) (ne_of_gt h)

/-- **The axiom leaf of a simulation for weak adjunction**: the negated translation of the
sentence is refuted, under every environment whose reserved label lies above the four binder
labels. -/
theorem simRuleWeakAdjunction (e : M) (h : ((simBase e+1)+1)+1 < simReserve e) :
    TargetProvable (impValue (negatedTranslation e (⌜sourceWeakAdjunction⌝ : M)) 1) :=
  positiveTarget_rule e _
    (fixedFormulaTranslation_weakAdjunction_target_of_lt (simBound e) (simFree e) (simBase e)
      (simReserve e) h)

#print axioms weakAdjRoot_quote
#print axioms weakAdjRoot_valid
#print axioms fixedTranslation_membershipBound
#print axioms fixedFormulaTranslation_weakAdjRoot
#print axioms fixedFormulaTranslation_weakAdjunction_target
#print axioms fixedFormulaTranslation_weakAdjunction_target_of_lt
#print axioms simRuleWeakAdjunction
end models
end PA194ModelLogic
