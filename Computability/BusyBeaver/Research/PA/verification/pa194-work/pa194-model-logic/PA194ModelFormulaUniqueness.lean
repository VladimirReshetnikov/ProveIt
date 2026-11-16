import PA194ModelFormulaDispatch

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

theorem evalTwo_definable (code : Code 4) (params metadata : M) :
    𝚺₁-Function₂ (fun p b : M => F code ![p,b,params,metadata]) := by
  have hg : 𝚺₁.DefinableFunction (fun v : Fin 4 → M => F code v) :=
    HierarchySymbol.Defined.to_definable _ (PA194CodeGraph.modelGraph (M := M) code)
  have hi : ∀ j : Fin 4, 𝚺₁.DefinableFunction
      (fun v : Fin 2 → M => ![v 0,v 1,params,metadata] j) := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact HierarchySymbol.DefinableFunction.var 0
    · refine Fin.cases ?_ (fun l => ?_) k
      · exact HierarchySymbol.DefinableFunction.var 1
      · refine Fin.cases ?_ (fun m => ?_) l
        · exact HierarchySymbol.DefinableFunction.const params
        · exact Fin.cases (HierarchySymbol.DefinableFunction.const metadata) (fun n => Fin.elim0 n) m
  have h := HierarchySymbol.DefinableFunction.substitution hg hi
  simpa using h

def agreementPair (f g : M → M → M) (p b : M) : Prop := p ≤ b → f p b = g p b

theorem agreementRelation_definable (f g : M → M → M)
    (hf : 𝚺₁-Function₂ f) (hg : 𝚺₁-Function₂ g) :
    𝚺₁-Relation (agreementPair f g) := by
  haveI := hf
  haveI := hg
  unfold agreementPair
  definability

theorem boundedAgreement_definable (spec : Code 4) (B params metadata : M) :
    𝚺₁-Predicate (fun p : M => ∀ b ≤ B, p ≤ b →
      F formulaHistory ![p,b,params,metadata] = F spec ![p,b,params,metadata]) := by
  let f : M → M → M := fun p b => F formulaHistory ![p,b,params,metadata]
  let g : M → M → M := fun p b => F spec ![p,b,params,metadata]
  haveI : 𝚺₁-Relation (agreementPair f g) :=
    agreementRelation_definable f g (evalTwo_definable formulaHistory params metadata)
      (evalTwo_definable spec params metadata)
  change 𝚺₁-Predicate (fun p : M => ∀ b ≤ B, agreementPair f g p b)
  definability

/-- These values depend only on the remaining budget and fixed parameters. -/
noncomputable def boundValue (b params metadata : M) : M :=
  F boundAtBudget ![b,π₁ metadata,π₁ (π₂ metadata),π₁ params]
noncomputable def labelValue (b metadata : M) : M :=
  F labelAtBudget ![b,π₁ metadata,π₁ (π₂ metadata)]

theorem currentValues_any (p b hist params metadata : M) :
    let e := ![pair p b,hist,params,metadata]
    F currentBound e = boundValue b params metadata ∧
    F currentLabel e = labelValue b metadata ∧
    F freeEnvironment e = π₂ params ∧ F reservedLabel e = π₂ (π₂ metadata) := by
  dsimp only
  have hc := currentContext_model (M := M) p b hist (π₁ params) (π₂ params)
    (π₁ metadata) (π₁ (π₂ metadata)) (π₂ (π₂ metadata))
  have hf := fixedParameters_model (M := M) (pair p b) hist (π₁ params) (π₂ params)
    (π₁ metadata) (π₁ (π₂ metadata)) (π₂ (π₂ metadata))
  simp only [pair_unpair] at hc hf
  exact ⟨hc.2.1,hc.2.2,hf.2.1,hf.2.2.2.2⟩

noncomputable def atomValue (tag relation vector b params metadata : M) : M :=
  let atom := pair tag (pair 2 (pair relation vector))+1
  if relation = 0 then F equalityAtomCode ![atom,boundValue b params metadata,π₂ params,π₂ (π₂ metadata)]
  else F membershipAtomCode ![atom,boundValue b params metadata,π₂ params,π₂ (π₂ metadata)]

theorem history_positive_expected (r v b params metadata : M) :
    F formulaHistory ![pair (0 : M) (pair 2 (pair r v))+1,b,params,metadata] =
      atomValue 0 r v b params metadata := by
  let atom := pair (0 : M) (pair 2 (pair r v))+1
  let hist := F (PA194ParamHistory.historyCode formulaNext) ![pair atom b,params,metadata]
  have hc := currentValues_any atom b hist params metadata
  dsimp only at hc
  have h := formulaHistory_positiveAtom r v b params metadata
  dsimp only at h
  change F formulaHistory ![atom,b,params,metadata] = _ at h
  rw [hc.1,hc.2.2.1,hc.2.2.2] at h
  exact h

theorem history_negative_expected (r v b params metadata : M) :
    F formulaHistory ![pair (1 : M) (pair 2 (pair r v))+1,b,params,metadata] =
      negValue (atomValue 1 r v b params metadata) := by
  let atom := pair (1 : M) (pair 2 (pair r v))+1
  let hist := F (PA194ParamHistory.historyCode formulaNext) ![pair atom b,params,metadata]
  have hc := currentValues_any atom b hist params metadata
  dsimp only at hc
  have h := formulaHistory_negativeAtom r v b params metadata
  dsimp only at h
  change F formulaHistory ![atom,b,params,metadata] = _ at h
  rw [hc.1,hc.2.2.1,hc.2.2.2] at h
  exact h

theorem history_all_expected (p b params metadata : M) :
    F formulaHistory ![pair (6 : M) p+1,b+1,params,metadata] =
      allValue (labelValue (b+1) metadata) (F formulaHistory ![p,b,params,metadata]) := by
  let atom := pair (6 : M) p+1
  let hist := F (PA194ParamHistory.historyCode formulaNext) ![pair atom (b+1),params,metadata]
  have hc := currentValues_any atom (b+1) hist params metadata
  dsimp only at hc
  have h := formulaHistory_all p b params metadata
  dsimp only at h
  change F formulaHistory ![atom,b+1,params,metadata] = _ at h
  rw [hc.2.1] at h
  exact h

theorem history_exs_expected (p b params metadata : M) :
    F formulaHistory ![pair (7 : M) p+1,b+1,params,metadata] =
      exValue (labelValue (b+1) metadata) (F formulaHistory ![p,b,params,metadata]) := by
  let atom := pair (7 : M) p+1
  let hist := F (PA194ParamHistory.historyCode formulaNext) ![pair atom (b+1),params,metadata]
  have hc := currentValues_any atom (b+1) hist params metadata
  dsimp only at hc
  have h := formulaHistory_exs p b params metadata
  dsimp only at h
  change F formulaHistory ![atom,b+1,params,metadata] = _ at h
  rw [hc.2.1] at h
  exact h

/-- Constructor equations for a candidate-PRA comparison code. These are external
hypotheses about its behavior in the current model, not evidence of its existence. -/
structure FormulaRecurrence (spec : Code 4) (params metadata : M) : Prop where
  positive (r v b : M) : F spec ![pair (0 : M) (pair 2 (pair r v))+1,b,params,metadata] = atomValue 0 r v b params metadata
  negative (r v b : M) : F spec ![pair (1 : M) (pair 2 (pair r v))+1,b,params,metadata] = negValue (atomValue 1 r v b params metadata)
  truth (b : M) : F spec ![pair (2 : M) 0+1,b,params,metadata] = 0
  falsum (b : M) : F spec ![pair (3 : M) 0+1,b,params,metadata] = memValue 0 0
  andRule (p q b : M) : F spec ![pair (4 : M) (pair p q)+1,b,params,metadata] =
    conjValue (F spec ![p,b,params,metadata]) (F spec ![q,b,params,metadata])
  orRule (p q b : M) : F spec ![pair (5 : M) (pair p q)+1,b,params,metadata] =
    impValue (negValue (F spec ![p,b,params,metadata])) (F spec ![q,b,params,metadata])
  allRule (p b : M) : F spec ![pair (6 : M) p+1,b+1,params,metadata] =
    allValue (labelValue (b+1) metadata) (F spec ![p,b,params,metadata])
  exRule (p b : M) : F spec ![pair (7 : M) p+1,b+1,params,metadata] =
    exValue (labelValue (b+1) metadata) (F spec ![p,b,params,metadata])

/-- Internal Σ₁ structural induction yields agreement for nonstandard valid source codes,
provided the comparison code satisfies the constructor equations in this model. -/
theorem boundedAgreement_of_recurrence (spec : Code 4) (B params metadata : M)
    (hs : FormulaRecurrence spec params metadata) (p : M)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    ∀ b ≤ B, p ≤ b → F formulaHistory ![p,b,params,metadata] = F spec ![p,b,params,metadata] := by
  have hdef := boundedAgreement_definable (M := M) spec B params metadata
  apply IsUFormula.ISigma1.sigma1_succ_induction hdef ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ p hp
  · intro k r v hr hv b hb hcode
    have hk := PA194AtomShiftCodeModel.sourceRelation_arity hr
    subst k
    simpa only [qqRel] using (history_positive_expected r v b params metadata).trans (hs.positive r v b).symm
  · intro k r v hr hv b hb hcode
    have hk := PA194AtomShiftCodeModel.sourceRelation_arity hr
    subst k
    simpa only [qqNRel] using (history_negative_expected r v b params metadata).trans (hs.negative r v b).symm
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
      _ = conjValue (F spec ![p,b,params,metadata]) (F spec ![q,b,params,metadata]) := by rw [ihp b hb hp',ihq b hb hq']
      _ = F spec ![p ^⋏ q,b,params,metadata] := by simpa only [qqAnd] using (hs.andRule p q b).symm
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
      _ = impValue (negValue (F spec ![p,b,params,metadata])) (F spec ![q,b,params,metadata]) := by rw [ihp b hb hp',ihq b hb hq']
      _ = F spec ![p ^⋎ q,b,params,metadata] := by simpa only [qqOr] using (hs.orRule p q b).symm
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
        _ = allValue (labelValue (j+1) metadata) (F spec ![p,j,params,metadata]) := by rw [ih j hjB hpj]
        _ = F spec ![^∀ p,j+1,params,metadata] := by simpa only [qqAll] using (hs.allRule p j).symm
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
        _ = exValue (labelValue (j+1) metadata) (F spec ![p,j,params,metadata]) := by rw [ih j hjB hpj]
        _ = F spec ![^∃ p,j+1,params,metadata] := by simpa only [qqExs] using (hs.exRule p j).symm

/-- Root convention: take the input formula code itself as initial budget. -/
theorem rootAgreement_of_recurrence (spec : Code 4) (params metadata p : M)
    (hs : FormulaRecurrence spec params metadata)
    (hp : IsUFormula M6.PA.RelationalSource.language p) :
    F formulaHistory ![p,p,params,metadata] = F spec ![p,p,params,metadata] :=
  boundedAgreement_of_recurrence spec p params metadata hs p hp p (le_refl p) (le_refl p)

#print axioms rootAgreement_of_recurrence
#print axioms boundedAgreement_of_recurrence
#print axioms history_positive_expected
#print axioms history_negative_expected
#print axioms history_all_expected
#print axioms history_exs_expected
#print axioms currentValues_any
#print axioms agreementRelation_definable
#print axioms evalTwo_definable
#print axioms boundedAgreement_definable
end models
end PA194ModelLogic
