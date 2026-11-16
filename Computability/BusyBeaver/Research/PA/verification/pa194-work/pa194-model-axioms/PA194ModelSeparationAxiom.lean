import PA194ModelSeparation
import PA194ModelLowVacuity
import PA194ModelWeakAdjunctionAxiom
import PA194ModelSimAxiomRules

/-!
# Translated instances of the separation scheme, at model level

For an internal formula code `φ` of a candidate-PRA model `M` whose arithmetic reduct
satisfies `𝗜𝚺₁`, `sepRoot φ` is the code of the separation instance

  `∀a ∃c ∀b ((b ∉ c ∨ (b ∈ a ∧ φ)) ∧ ((b ∉ a ∨ ¬φ) ∨ b ∈ c))`,

where `¬φ` is Foundation's internal negation and `φ` is used under the three binders as it
is: a formula of arity one mentions only the innermost bound variable `b`, and its code does
not depend on the number of binders around it. The formula may be nonstandard and may have
free variables.

* `fixedFormulaTranslation_sepRoot`: the fixed formula translation of `sepRoot φ` for
  arbitrary stacks, with the binder labels `base`, `base+1`, `base+2` and the translations
  of `φ` and `¬φ` under the extended bound stack.
* `fixedFormulaTranslation_separation_target`: the translation is target-provable when `φ`
  has arity one, the free stack does not contain the output label `base+1` up to index `φ`,
  and the reserved label differs from `base+1` and `base+2`. The three vacuity hypotheses of
  `separationAtName_target` come from `lowVacuity_all_codes` (output label) and
  `generalVacuity_all_codes` (the padding label and the code of the padded property); the
  negated property is handled by `translationDual_all_codes`.
* `simRuleSeparation`: the corresponding axiom leaf of a simulation.

No theory with these instances as axioms is defined here, no simulation is constructed, and
nothing here yields a consistency implication.
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
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance sepAxZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance sepAxOne : One M := ⟨F oneCode Fin.elim0⟩
local instance sepAxAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance sepAxMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance sepAxLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance sepAxIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- `(b ∉ c ∨ (b ∈ a ∧ φ)) ∧ ((b ∉ a ∨ ¬φ) ∨ b ∈ c)` under the binders `a, c, b`. -/
noncomputable def sepInner (φ : M) : M :=
  ((^nrel (2 : M) (1 : M) (relExtVector 0 1)) ^⋎
      ((^rel (2 : M) (1 : M) (relExtVector 0 2)) ^⋏ φ)) ^⋏
    (((^nrel (2 : M) (1 : M) (relExtVector 0 2)) ^⋎ neg SourceL φ) ^⋎
      (^rel (2 : M) (1 : M) (relExtVector 0 1)))

/-- The code of the separation instance for the internal formula `φ`. -/
noncomputable def sepRoot (φ : M) : M := ^∀ (^∃ (^∀ (sepInner φ)))

theorem sepInner_valid (φ : M) (hφ : IsUFormula SourceL φ) :
    IsUFormula SourceL (sepInner φ) := by
  simp only [sepInner,IsUFormula.and,IsUFormula.or,IsUFormula.nrel,IsUFormula.rel,
    IsUFormula.neg_iff]
  exact ⟨⟨⟨relExt_relation_one,relExt_vector_valid 0 1⟩,
      ⟨relExt_relation_one,relExt_vector_valid 0 2⟩,hφ⟩,
    ⟨⟨relExt_relation_one,relExt_vector_valid 0 2⟩,hφ⟩,
      ⟨relExt_relation_one,relExt_vector_valid 0 1⟩⟩

theorem sepRoot_valid (φ : M) (hφ : IsUFormula SourceL φ) :
    IsUFormula SourceL (sepRoot φ) := by
  simpa only [sepRoot,IsUFormula.all,IsUFormula.ex] using sepInner_valid φ hφ

theorem nth_cons_two' (x0 x1 x2 v : M) :
    (pair x0 (pair x1 (pair x2 v + 1) + 1) + 1).[2] = x2 := by
  have e : (1 : M) + 1 = 2 := one_add_one_eq_two
  have h := nth_cons_succ' x0 (pair x1 (pair x2 v + 1) + 1) 1
  rw [e] at h
  rw [h,nth_cons_one']

/-- The translation of a separation instance, for arbitrary stacks and labels. -/
theorem fixedFormulaTranslation_sepRoot (φ initial free base reserve : M)
    (hφ : IsUFormula SourceL φ) :
    F fixedFormulaTranslation ![sepRoot φ,initial,free,base,reserve] =
      allValue base (exValue (base+1) (allValue ((base+1)+1)
        (conjValue
          (impValue (negValue (negValue (memValue (base+1) ((base+1)+1))))
            (conjValue (memValue base ((base+1)+1))
              (F fixedFormulaTranslation ![φ,
                pair ((base+1)+1) (pair (base+1) (pair base initial+1)+1)+1,
                free,((base+1)+1)+1,reserve])))
          (impValue
            (negValue (impValue (negValue (negValue (memValue base ((base+1)+1))))
              (F fixedFormulaTranslation ![neg SourceL φ,
                pair ((base+1)+1) (pair (base+1) (pair base initial+1)+1)+1,
                free,((base+1)+1)+1,reserve])))
            (memValue (base+1) ((base+1)+1)))))) := by
  have hr : SourceL.IsRel (2 : M) (1 : M) := relExt_relation_one
  have hnφ : IsUFormula SourceL (neg SourceL φ) := IsUFormula.neg hφ
  have hA : IsUFormula SourceL (^rel (2 : M) (1 : M) (relExtVector 0 1)) := by
    simp only [IsUFormula.rel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 1⟩
  have hA' : IsUFormula SourceL (^nrel (2 : M) (1 : M) (relExtVector 0 1)) := by
    simp only [IsUFormula.nrel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 1⟩
  have hB : IsUFormula SourceL (^rel (2 : M) (1 : M) (relExtVector 0 2)) := by
    simp only [IsUFormula.rel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 2⟩
  have hB' : IsUFormula SourceL (^nrel (2 : M) (1 : M) (relExtVector 0 2)) := by
    simp only [IsUFormula.nrel]
    exact ⟨relExt_relation_one,relExt_vector_valid 0 2⟩
  have hBφ : IsUFormula SourceL ((^rel (2 : M) (1 : M) (relExtVector 0 2)) ^⋏ φ) := by
    simpa only [IsUFormula.and] using And.intro hB hφ
  have hBn : IsUFormula SourceL
      ((^nrel (2 : M) (1 : M) (relExtVector 0 2)) ^⋎ neg SourceL φ) := by
    simpa only [IsUFormula.or] using And.intro hB' hnφ
  have hl : IsUFormula SourceL ((^nrel (2 : M) (1 : M) (relExtVector 0 1)) ^⋎
      ((^rel (2 : M) (1 : M) (relExtVector 0 2)) ^⋏ φ)) := by
    simpa only [IsUFormula.or] using And.intro hA' hBφ
  have hrr : IsUFormula SourceL
      (((^nrel (2 : M) (1 : M) (relExtVector 0 2)) ^⋎ neg SourceL φ) ^⋎
        (^rel (2 : M) (1 : M) (relExtVector 0 1))) := by
    simpa only [IsUFormula.or] using And.intro hBn hA
  have hin := sepInner_valid φ hφ
  have hall : IsUFormula SourceL (^∀ (sepInner φ)) := by
    simpa only [IsUFormula.all] using hin
  have hex : IsUFormula SourceL (^∃ (^∀ (sepInner φ))) := by
    simpa only [IsUFormula.ex] using hall
  rw [sepRoot,fixedFormulaTranslation_all _ _ _ _ _ hex,
    fixedFormulaTranslation_ex _ _ _ _ _ hall,
    fixedFormulaTranslation_all _ _ _ _ _ hin,sepInner,
    fixedFormulaTranslation_and _ _ _ _ _ _ hl hrr,
    fixedFormulaTranslation_or _ _ _ _ _ _ hA' hBφ,
    fixedFormulaTranslation_and _ _ _ _ _ _ hB hφ,
    fixedFormulaTranslation_or _ _ _ _ _ _ hBn hA,
    fixedFormulaTranslation_or _ _ _ _ _ _ hB' hnφ,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr (relExt_vector_valid 0 1),
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr (relExt_vector_valid 0 2)]
  simp only [fixedTranslation_membershipBound,nth_cons_zero',nth_cons_one',nth_cons_two']

/-- **The translation of a separation instance is target-provable**, for an internal formula
of arity one, possibly nonstandard and with free variables. -/
theorem fixedFormulaTranslation_separation_target (φ initial free base reserve : M)
    (hφ : IsSemiformula SourceL 1 φ)
    (hfree : ∀ i ≤ φ, free.[i] ≠ base+1)
    (h1 : reserve ≠ base+1) (h2 : reserve ≠ (base+1)+1) :
    TargetProvable (F fixedFormulaTranslation ![sepRoot φ,initial,free,base,reserve]) := by
  have hu : IsUFormula SourceL φ := hφ.isUFormula
  rw [fixedFormulaTranslation_sepRoot φ initial free base reserve hu]
  let a : M := base
  let c : M := base+1
  let b : M := (base+1)+1
  let base3 : M := ((base+1)+1)+1
  let bound3 : M := pair b (pair c (pair a initial+1)+1)+1
  let P : M := F fixedFormulaTranslation ![φ,bound3,free,base3,reserve]
  let Pn : M := F fixedFormulaTranslation ![neg SourceL φ,bound3,free,base3,reserve]
  have lac : a < c := lt_add_one base
  have lcb : c < b := lt_add_one (base+1)
  have lb3 : b < base3 := lt_add_one ((base+1)+1)
  -- vacuity at the output label
  have hPc : TargetProvable (impValue P (allValue c P)) := by
    have h := lowVacuity_all_codes c φ bound3 free base3 reserve 1 hφ (lt_trans lcb lb3)
      (by
        intro i hi
        have hi0 : i = 0 := lt_one_iff_eq_zero.mp hi
        rw [hi0]
        change (pair b (pair c (pair a initial+1)+1)+1).[0] ≠ c
        rw [nth_cons_zero']
        exact ne_of_gt lcb)
      hfree (Ne.symm h1)
    unfold GeneralVacuity at h
    simpa only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] using h
  -- a label above everything the translation reads or allocates
  let S : M := bound3 + free + base3 + φ + reserve
  let q : M := S + 1
  have hSq : S < q := lt_add_one S
  have hbS : bound3 ≤ S :=
    le_trans (le_trans (le_trans le_self_add le_self_add) le_self_add) le_self_add
  have hfS : free ≤ S :=
    le_trans (le_trans (le_trans le_add_self le_self_add) le_self_add) le_self_add
  have h3S : base3 ≤ S := le_trans (le_trans le_add_self le_self_add) le_self_add
  have hzS : reserve ≤ S := le_add_self
  have hbaseS : base3 + φ ≤ S := by
    have h : base3 + φ ≤ (bound3 + free) + (base3 + φ) := le_add_self
    exact le_trans (by simpa only [add_assoc] using h) le_self_add
  have hzq : reserve < q := lt_of_le_of_lt hzS hSq
  have h3q : base3 < q := lt_of_le_of_lt h3S hSq
  have hbq : b < q := lt_trans lb3 h3q
  have hcq : c < q := lt_trans lcb hbq
  have haq : a < q := lt_trans lac hcq
  have hPq : TargetProvable (impValue P (allValue q P)) := by
    have h := generalVacuity_all_codes q φ bound3 free base3 reserve hu
      (le_trans hbaseS (le_of_lt hSq))
      (fun i _ => lt_of_le_of_lt (le_trans (nth_le bound3 i) hbS) hSq)
      (fun i _ => lt_of_le_of_lt (le_trans (nth_le free i) hfS) hSq)
      (ne_of_gt hzq)
    unfold GeneralVacuity at h
    simpa only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] using h
  let X : M := conjValue (memValue a b) P
  let d : M := allValue q X
  have hqd : q < d := label_lt_allValue q X
  have hSd : S < d := lt_trans hSq hqd
  have hPd : TargetProvable (impValue P (allValue d P)) := by
    have h := generalVacuity_all_codes d φ bound3 free base3 reserve hu
      (le_trans hbaseS (le_of_lt hSd))
      (fun i _ => lt_of_le_of_lt (le_trans (nth_le bound3 i) hbS) hSd)
      (fun i _ => lt_of_le_of_lt (le_trans (nth_le free i) hfS) hSd)
      (ne_of_gt (lt_of_le_of_lt hzS hSd))
    unfold GeneralVacuity at h
    simpa only [simBound,simFree,simBase,simReserve,pi₁_pair,pi₂_pair] using h
  have hsep : TargetProvable (exValue c (separationBody a b P c)) :=
    separationAtName_target a b c reserve P q haq hbq hcq hzq (ne_of_gt lac) (ne_of_lt lcb)
      h2 h1 hPc hPq hPd
  -- the negated property
  have hdual := translationDual_all_codes φ bound3 free base3 reserve hu
  unfold TranslationDual TargetDual at hdual
  have hnP : TargetProvable (impValue (negValue Pn) P) :=
    imp_trans (contrapose hdual.2) (doubleNegationElimination P)
  -- from the equivalence to the source shape of the instance
  let ma : M := memValue a b
  let mc : M := memValue c b
  let nnma : M := negValue (negValue ma)
  let nnmc : M := negValue (negValue mc)
  let I : M := iffValue mc X
  let N : M := negValue (impValue nnma Pn)
  have hpt : TargetProvable (impValue I
      (conjValue (impValue nnmc X) (impValue N mc))) := by
    let f1 : Ctx [nnmc,I] (conjValue (impValue mc X) (impValue X mc)) :=
      .assumption (by simp [I,iffValue])
    let f2 : Ctx [nnmc,I] (negValue (negValue mc)) := .assumption (by simp [nnmc])
    let f3 : Ctx [nnmc,I] X := .mp f2.dne f1.andLeft
    let part1 : Ctx [I] (impValue nnmc X) := f3.deduction
    let g1 : Ctx [nnma,Pn,N,I] Pn := .assumption (by simp)
    let g2 : Ctx [Pn,N,I] (impValue nnma Pn) := g1.deduction
    let gN : Ctx [Pn,N,I] (negValue (impValue nnma Pn)) := .assumption (by simp [N])
    let g3 : Ctx [Pn,N,I] 1 := .mp g2 gN
    let g4 : Ctx [N,I] (negValue Pn) := g3.deduction
    let gP : Ctx [N,I] P := .mp g4 (.closed hnP)
    let k1 : Ctx [nnma,negValue nnma,N,I] nnma := .assumption (by simp)
    let k2 : Ctx [nnma,negValue nnma,N,I] (negValue nnma) := .assumption (by simp)
    let k3 : Ctx [nnma,negValue nnma,N,I] Pn := (Ctx.mp k1 k2).explosion Pn
    let k4 : Ctx [negValue nnma,N,I] (impValue nnma Pn) := k3.deduction
    let kN : Ctx [negValue nnma,N,I] (negValue (impValue nnma Pn)) :=
      .assumption (by simp [N])
    let k5 : Ctx [negValue nnma,N,I] 1 := .mp k4 kN
    let k6 : Ctx [N,I] (negValue (negValue (negValue (negValue ma)))) := k5.deduction
    let kma : Ctx [N,I] ma := k6.dne.dne
    let gX : Ctx [N,I] (conjValue ma P) := .andIntro kma gP
    let hI2 : Ctx [N,I] (conjValue (impValue mc X) (impValue X mc)) :=
      .assumption (by simp [I,iffValue])
    let gmc : Ctx [N,I] mc := .mp gX hI2.andRight
    let part2 : Ctx [I] (impValue N mc) := gmc.deduction
    exact (Ctx.andIntro part1 part2).deduction.empty
  unfold separationBody at hsep
  exact tp_gen a (tp_mp hsep (existentialMonotonicity c (liftImp b hpt)))

/-- **The axiom leaf of a simulation for a separation instance**. -/
theorem simRuleSeparation (e φ : M) (hφ : IsSemiformula SourceL 1 φ)
    (hfree : ∀ i ≤ φ, (simFree e).[i] ≠ simBase e+1)
    (h1 : simReserve e ≠ simBase e+1) (h2 : simReserve e ≠ (simBase e+1)+1) :
    TargetProvable (impValue (negatedTranslation e (sepRoot φ)) 1) :=
  positiveTarget_rule e _
    (fixedFormulaTranslation_separation_target φ (simBound e) (simFree e) (simBase e)
      (simReserve e) hφ hfree h1 h2)

#print axioms sepRoot_valid
#print axioms fixedFormulaTranslation_sepRoot
#print axioms fixedFormulaTranslation_separation_target
#print axioms simRuleSeparation
end models
end PA194ModelLogic
