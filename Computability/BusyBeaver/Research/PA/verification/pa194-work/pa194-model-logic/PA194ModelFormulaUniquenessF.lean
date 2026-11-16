import PA194ModelFormulaUniqueness

/-! Σ₁-bounded agreement predicate for internal uniqueness of source-formula
translation. The remaining budget is bounded by a fixed model value; no
unbounded environment or budget quantifier is used in this predicate. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode PRASubAddition
 PA194NumeralCode PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem boundedAgreementF_definable (spec : M → M → M) (B params metadata : M)
    (hdefSpec : 𝚺₁-Function₂ spec) :
    𝚺₁-Predicate (fun p : M => ∀ b ≤ B, p ≤ b →
      F formulaHistory ![p,b,params,metadata] = spec p b) := by
  let f : M → M → M := fun p b => F formulaHistory ![p,b,params,metadata]
  haveI : 𝚺₁-Relation (agreementPair f spec) :=
    agreementRelation_definable f spec (evalTwo_definable formulaHistory params metadata) hdefSpec
  change 𝚺₁-Predicate (fun p : M => ∀ b ≤ B, agreementPair f spec p b)
  definability

/-- Constructor equations for a Σ₁-definable comparison function, restricted to
valid source constructors. These are model hypotheses, not an existence theorem. -/
structure FormulaRecurrenceF (spec : M → M → M) (params metadata : M) : Prop where
  positive (r v b : M) (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) : spec (pair (0 : M) (pair 2 (pair r v))+1) (b) = atomValue 0 r v b params metadata
  negative (r v b : M) (hr : M6.PA.RelationalSource.language.IsRel 2 r)
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) : spec (pair (1 : M) (pair 2 (pair r v))+1) (b) = negValue (atomValue 1 r v b params metadata)
  truth (b : M) : spec (pair (2 : M) 0+1) (b) = 0
  falsum (b : M) : spec (pair (3 : M) 0+1) (b) = memValue 0 0
  andRule (p q b : M) (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) : spec (pair (4 : M) (pair p q)+1) (b) =
    conjValue (spec (p) (b)) (spec (q) (b))
  orRule (p q b : M) (hp : IsUFormula M6.PA.RelationalSource.language p)
    (hq : IsUFormula M6.PA.RelationalSource.language q) : spec (pair (5 : M) (pair p q)+1) (b) =
    impValue (negValue (spec (p) (b))) (spec (q) (b))
  allRule (p b : M) (hp : IsUFormula M6.PA.RelationalSource.language p) : spec (pair (6 : M) p+1) (b+1) =
    allValue (labelValue (b+1) metadata) (spec (p) (b))
  exRule (p b : M) (hp : IsUFormula M6.PA.RelationalSource.language p) : spec (pair (7 : M) p+1) (b+1) =
    exValue (labelValue (b+1) metadata) (spec (p) (b))

/-- Internal Σ₁ structural induction yields agreement for nonstandard valid source codes,
provided the definable comparison function satisfies the constructor equations in this model. -/
theorem boundedAgreementF_of_recurrence (spec : M → M → M) (B params metadata : M)
    (hdefSpec : 𝚺₁-Function₂ spec) (hs : FormulaRecurrenceF spec params metadata) (p : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    ∀ b ≤ B, p ≤ b → F formulaHistory ![p,b,params,metadata] = spec (p) (b) := by
  have hdef := boundedAgreementF_definable (M := M) spec B params metadata hdefSpec
  apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv b hb hcode
    have hk := PA194AtomShiftCodeModel.sourceRelation_arity hr
    subst k
    simpa only [qqRel] using (history_positive_expected r v b params metadata).trans (hs.positive r v b hr hv).symm
  · intro k r v hr hv b hb hcode
    have hk := PA194AtomShiftCodeModel.sourceRelation_arity hr
    subst k
    simpa only [qqNRel] using (history_negative_expected r v b params metadata).trans (hs.negative r v b hr hv).symm
  · intro b hb hcode
    simpa only [qqVerum] using (formulaHistory_truth (0 : M) b params metadata).trans (hs.truth b).symm
  · intro b hb hcode
    simpa only [qqFalsum] using (formulaHistory_falsum (0 : M) b params metadata).trans (hs.falsum b).symm
  · intro p q hp hq ihp ihq b hb hcode
    have hl : p < pair (4 : M) (pair p q)+1 :=
      lt_of_le_of_lt (le_trans (le_pair_left p q) (le_pair_right (4 : M) (pair p q))) (lt_add_one _)
    have hr : q < pair (4 : M) (pair p q)+1 :=
      lt_of_le_of_lt (le_trans (le_pair_right p q) (le_pair_right (4 : M) (pair p q))) (lt_add_one _)
    have hcode' : pair (4 : M) (pair p q)+1 ≤ b := by simpa only [qqAnd] using hcode
    have hp' : p ≤ b := le_trans (le_of_lt hl) hcode'
    have hq' : q ≤ b := le_trans (le_of_lt hr) hcode'
    calc
      F formulaHistory ![p ^⋏ q,b,params,metadata] = conjValue (F formulaHistory ![p,b,params,metadata]) (F formulaHistory ![q,b,params,metadata]) := by simpa only [qqAnd] using formulaHistory_and p q b params metadata
      _ = conjValue (spec (p) (b)) (spec (q) (b)) := by rw [ihp b hb hp',ihq b hb hq']
      _ = spec (p ^⋏ q) (b) := by simpa only [qqAnd] using (hs.andRule p q b hp hq).symm
  · intro p q hp hq ihp ihq b hb hcode
    have hl : p < pair (5 : M) (pair p q)+1 :=
      lt_of_le_of_lt (le_trans (le_pair_left p q) (le_pair_right (5 : M) (pair p q))) (lt_add_one _)
    have hr : q < pair (5 : M) (pair p q)+1 :=
      lt_of_le_of_lt (le_trans (le_pair_right p q) (le_pair_right (5 : M) (pair p q))) (lt_add_one _)
    have hcode' : pair (5 : M) (pair p q)+1 ≤ b := by simpa only [qqOr] using hcode
    have hp' : p ≤ b := le_trans (le_of_lt hl) hcode'
    have hq' : q ≤ b := le_trans (le_of_lt hr) hcode'
    calc
      F formulaHistory ![p ^⋎ q,b,params,metadata] = impValue (negValue (F formulaHistory ![p,b,params,metadata])) (F formulaHistory ![q,b,params,metadata]) := by simpa only [qqOr] using formulaHistory_or p q b params metadata
      _ = impValue (negValue (spec (p) (b))) (spec (q) (b)) := by rw [ihp b hb hp',ihq b hb hq']
      _ = spec (p ^⋎ q) (b) := by simpa only [qqOr] using (hs.orRule p q b hp hq).symm
  · intro p hp ih b hb hcode
    have hpos : (0 : M) < pair (6 : M) p+1 := by simp
    have hcode' : pair (6 : M) p+1 ≤ b := by simpa only [qqAll] using hcode
    rcases zero_or_succ b with (rfl | ⟨j,rfl⟩)
    · exact False.elim ((not_le_of_gt hpos) hcode')
    · have hc : p < pair (6 : M) p+1 := lt_of_le_of_lt (le_pair_right (6 : M) p) (lt_add_one _)
      have hpj : p ≤ j := lt_succ_iff_le.mp (lt_of_lt_of_le hc hcode')
      have hjB : j ≤ B := le_trans (le_of_lt (lt_add_one j)) hb
      calc
        F formulaHistory ![^∀ p,j+1,params,metadata] = allValue (labelValue (j+1) metadata) (F formulaHistory ![p,j,params,metadata]) := by simpa only [qqAll] using history_all_expected p j params metadata
        _ = allValue (labelValue (j+1) metadata) (spec (p) (j)) := by rw [ih j hjB hpj]
        _ = spec (^∀ p) (j+1) := by simpa only [qqAll] using (hs.allRule p j hp).symm
  · intro p hp ih b hb hcode
    have hpos : (0 : M) < pair (7 : M) p+1 := by simp
    have hcode' : pair (7 : M) p+1 ≤ b := by simpa only [qqExs] using hcode
    rcases zero_or_succ b with (rfl | ⟨j,rfl⟩)
    · exact False.elim ((not_le_of_gt hpos) hcode')
    · have hc : p < pair (7 : M) p+1 := lt_of_le_of_lt (le_pair_right (7 : M) p) (lt_add_one _)
      have hpj : p ≤ j := lt_succ_iff_le.mp (lt_of_lt_of_le hc hcode')
      have hjB : j ≤ B := le_trans (le_of_lt (lt_add_one j)) hb
      calc
        F formulaHistory ![^∃ p,j+1,params,metadata] = exValue (labelValue (j+1) metadata) (F formulaHistory ![p,j,params,metadata]) := by simpa only [qqExs] using history_exs_expected p j params metadata
        _ = exValue (labelValue (j+1) metadata) (spec (p) (j)) := by rw [ih j hjB hpj]
        _ = spec (^∃ p) (j+1) := by simpa only [qqExs] using (hs.exRule p j hp).symm

/-- Root convention: take the input formula code itself as initial budget. -/
theorem rootAgreementF_of_recurrence (spec : M → M → M) (params metadata p : M)
    (hdefSpec : 𝚺₁-Function₂ spec) (hs : FormulaRecurrenceF spec params metadata)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F formulaHistory ![p,p,params,metadata] = spec (p) (p) :=
  boundedAgreementF_of_recurrence spec p params metadata hdefSpec hs p hp p (le_refl p) (le_refl p)

#print axioms boundedAgreementF_definable
#print axioms boundedAgreementF_of_recurrence
#print axioms rootAgreementF_of_recurrence
end models
end PA194ModelLogic
