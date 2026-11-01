import DiophantineConsistency.PRAWitnessRefutationOuter
import DiophantineConsistency.PRAWitnessZFCAxioms
import DiophantineConsistency.PRAWitnessFormulaSetCandidate
import DiophantineConsistency.PRAWitnessSetShiftCandidate
/-! # Witness bounds for ZFC derivations -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAWitnessDerivation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open StrictSigmaOneInduction PRAWitnessCalculus PRAWitnessArithmetic PRAWitnessVectors PRAWitnessSetTerms
  PRAWitnessTermRec PRAWitnessTermFunctions PRAWitnessFormulas PRAWitnessFormulaRec PRAWitnessRepeatVec
  PRAWitnessExpBounds PRAWitnessFormulaFunctions PRAWitnessCodeGrowth PRAWitnessSubsts PRAWitnessBoundTerms
  PRAWitnessBoundTerms.BoundTerm PRAWitnessPR PRAWitnessZFCAxioms LeanProofs.ZFCinPA

section sigma1
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem le_insert_self (x s : V) : s ≤ insert x s :=
  le_of_subset (fun y hy => by simp [hy])

end sigma1

syntax "der_close" : tactic
macro_rules
  | `(tactic| der_close) => `(tactic| first
    | (apply wb_not_mem; assumption)
    | (apply wb_mem; assumption)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simp; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simp; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#2’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simp; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; apply le_of_lt; apply lt_of_mem; simp_all; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; apply le_of_lt; apply lt_of_mem; simp_all; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#2’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; apply le_of_lt; apply lt_of_mem; simp_all; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#3’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; apply le_of_lt; apply lt_of_mem; simp_all; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#4’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; apply le_of_lt; apply lt_of_mem; simp_all; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#0’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; simp_all [le_insert_self]; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘#1’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; simp_all [le_insert_self]; done)); wb_auto; all_goals der_close)
    | (refine wb_exs_bt _ (by simp) (tauT (add (poly ‘#0’) (poly ‘8’)) (add (mul (poly ‘2’) (poly ‘#0’)) (poly ‘6’)))
        (fun V _ _ e u h => ?hle) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using neg_le' (e 0) (e 0) le_rfl; done)); wb_auto; all_goals der_close)
    | (refine wb_exs_bt _ (by simp) (tauT (add (poly ‘#3’) (poly ‘8’)) (add (mul (poly ‘2’) (poly ‘#3’)) (poly ‘6’)))
        (fun V _ _ e u h => ?hle) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using neg_le' (e 3) (e 3) le_rfl; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(2 + 0 + 1) * (2 + 0 + 1) + 1’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [qqVerum, numeral_eq_natCast] using code2_le (2 : V) 0; done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(4 + (#3 + #2 + 1) * (#3 + #2 + 1) + 1) * (4 + (#3 + #2 + 1) * (#3 + #2 + 1) + 1) + 1’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [qqAnd, numeral_eq_natCast] using code3_le 4 (e 3) (e 2); done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(5 + (#2 + #1 + 1) * (#2 + #1 + 1) + 1) * (5 + (#2 + #1 + 1) * (#2 + #1 + 1) + 1) + 1’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [qqOr, numeral_eq_natCast] using code3_le 5 (e 2) (e 1); done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(6 + #1 + 1) * (6 + #1 + 1) + 1’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [qqAll, numeral_eq_natCast] using code2_le 6 (e 1); done)); wb_auto; all_goals der_close)
    | (refine PRAWitnessTransfer.wb_exs_poly _ (by simp) ‘(7 + #2 + 1) * (7 + #2 + 1) + 1’
        (fun V _ _ e u h => ⟨u, ?hle, h⟩) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [qqExs, numeral_eq_natCast] using code2_le 7 (e 2); done)); wb_auto; all_goals der_close)
    | (refine wb_exs_bt _ (by simp) (add (poly ‘#4’) (exp2 (poly ‘#2’) (poly ‘0’)))
        (fun V _ _ e u h => ?hle) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [vval] using insert_le_of_le_of_le (le_refl (e 2)) (le_refl (e 4)); done)); wb_auto; all_goals der_close)
    | (refine wb_exs_bt _ (by simp) (tauT (poly ‘0 + ((#2 + 2) * (#2 + 2) + 1) + 8’) (poly ‘0 + 4 * #2 + 6’))
        (fun V _ _ e u h => ?hle) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using free_le (e 2); done)); wb_auto; all_goals der_close)
    | (refine wb_exs_bt _ (by simp) (exp2 (poly ‘1’) (poly ‘((#4 + 2) * (#4 + 2) + 1 + 8 + 4) * (#4 * #4 * 64) + 1’))
        (fun V _ _ e u h => ?hle) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [vval, numeral_eq_natCast] using setShift_le (e 4); done)); wb_auto; all_goals der_close)
    | (refine wb_exs_bt _ (by simp) (exp2 (poly ‘1’) (poly ‘((#0 + 2) * (#0 + 2) + 1 + 8 + 4) * (#0 * #0 * 64) + 1’))
        (fun V _ _ e u h => ?hle) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [vval, numeral_eq_natCast] using setShift_le (e 0); done)); wb_auto; all_goals der_close)
    | (refine wb_exs_bt _ (by simp) (tauT (poly ‘#2 + #3 + 8’) (poly ‘0 + 4 * #3 + 6’))
        (fun V _ _ e u h => ?hle) ?hwb; (case hle => (have h' := h; simp at h'; rw [h'.1]; simpa [vval_tauT, vval, numeral_eq_natCast] using substs1_le (e 2) (e 3); done)); wb_auto; all_goals der_close))

section models
open PRAFiniteFunctionCodes PRALanguage PRATheory
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩

theorem wb_isFormulaSet_sigma : WB M (isFormulaSet ℒₛₑₜ).sigma.val :=
  PRAWitnessFormulaSetCandidate.wb_isFormulaSet_sigma

theorem wb_isFormulaSet_neg_pi : WB M (∼(isFormulaSet ℒₛₑₜ).pi.val) :=
  PRAWitnessFormulaSetCandidate.wb_isFormulaSet_neg_pi

theorem wb_setShiftGraph : WB M (setShiftGraph ℒₛₑₜ).val :=
  PRAWitnessSetShiftCandidate.wb_setShiftGraph

set_option maxHeartbeats 4000000 in
theorem wb_derivation_core_sigma : WB M (Derivation.blueprint (𝗭𝗙𝗖 : SetTheory)).core.sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_fstIdxDef (M := M); have := wb_negGraph (M := M); have := wb_bitDef (M := M)
  have hn := wb_neg_bitDef (M := M); have := wb_qqVerumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_insertDef (M := M); have := wb_freeGraph (M := M); have := wb_setShiftGraph (M := M)
  have := wb_substs1Graph (M := M); have := wb_bitSubsetDef (M := M)
  have := wb_axLGraph (M := M); have := wb_verumIntroGraph (M := M); have := wb_andIntroGraph (M := M)
  have := wb_orIntroGraph (M := M); have := wb_allIntroGraph (M := M); have := wb_exsIntroGraph (M := M)
  have := wb_wkRuleGraph (M := M); have := wb_shiftRuleGraph (M := M); have := wb_cutRuleGraph (M := M)
  have := wb_axmGraph (M := M)
  have := wb_isFormulaSet_sigma (M := M); have := wb_isSemiterm_sigma (M := M)
  have : WB M (𝗭𝗙𝗖 : SetTheory).Δ₁ch.sigma.val := goodCh_zfc.1
  simp only [Derivation.blueprint, HierarchySymbol.Semiformula.sigma_mkDelta,
    HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto
  all_goals der_close

set_option maxHeartbeats 4000000 in
theorem wb_derivation_core_neg_pi : WB M (∼(Derivation.blueprint (𝗭𝗙𝗖 : SetTheory)).core.pi.val) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_fstIdxDef (M := M); have := wb_negGraph (M := M); have := wb_bitDef (M := M)
  have hn := wb_neg_bitDef (M := M); have := wb_qqVerumDef (M := M); have := wb_qqAndDef (M := M)
  have := wb_qqOrDef (M := M); have := wb_qqAllDef (M := M); have := wb_qqExsDef (M := M)
  have := wb_insertDef (M := M); have := wb_freeGraph (M := M); have := wb_setShiftGraph (M := M)
  have := wb_substs1Graph (M := M); have := wb_bitSubsetDef (M := M)
  have := wb_axLGraph (M := M); have := wb_verumIntroGraph (M := M); have := wb_andIntroGraph (M := M)
  have := wb_orIntroGraph (M := M); have := wb_allIntroGraph (M := M); have := wb_exsIntroGraph (M := M)
  have := wb_wkRuleGraph (M := M); have := wb_shiftRuleGraph (M := M); have := wb_cutRuleGraph (M := M)
  have := wb_axmGraph (M := M)
  have := wb_isFormulaSet_neg_pi (M := M); have := wb_isSemiterm_neg_pi (M := M)
  have := wb_neg_qqVerumDef (M := M); have := wb_neg_qqAndDef (M := M); have := wb_neg_qqOrDef (M := M)
  have := wb_neg_qqAllDef (M := M); have := wb_neg_qqExsDef (M := M); have := wb_neg_insertDef (M := M)
  have := wb_neg_bitSubsetDef (M := M); have := wb_neg_fstIdxDef (M := M)
  have := wb_neg_axLGraph (M := M); have := wb_neg_verumIntroGraph (M := M)
  have := wb_neg_andIntroGraph (M := M); have := wb_neg_orIntroGraph (M := M)
  have := wb_neg_allIntroGraph (M := M); have := wb_neg_exsIntroGraph (M := M)
  have := wb_neg_wkRuleGraph (M := M); have := wb_neg_shiftRuleGraph (M := M)
  have := wb_neg_cutRuleGraph (M := M); have := wb_neg_axmGraph (M := M)
  have : WB M (∼(𝗭𝗙𝗖 : SetTheory).Δ₁ch.pi.val) := goodCh_zfc.2
  simp only [Derivation.blueprint, HierarchySymbol.Semiformula.pi_mkDelta,
    HierarchySymbol.Semiformula.val_mkPi]
  wb_auto
  all_goals der_close

theorem wb_derivation_sigma : WB M (derivation (𝗭𝗙𝗖 : SetTheory)).sigma.val :=
  PRAHistoryTruncation.wb_fixpoint_sigma _ wb_derivation_core_sigma wb_derivation_core_neg_pi

theorem wb_derivation_neg_pi : WB M (∼(derivation (𝗭𝗙𝗖 : SetTheory)).pi.val) :=
  PRAHistoryTruncation.wb_fixpoint_neg_pi _ wb_derivation_core_sigma wb_derivation_core_neg_pi

theorem wb_derivationOf_sigma : WB M (derivationOf (𝗭𝗙𝗖 : SetTheory)).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_fstIdxDef (M := M); have := wb_derivation_sigma (M := M)
  simp only [derivationOf, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  wb_auto

theorem wb_proof_sigma : WB M (proof (𝗭𝗙𝗖 : SetTheory)).sigma.val := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  have := wb_insertDef (M := M); have := wb_derivationOf_sigma (M := M)
  simp only [proof, HierarchySymbol.Semiformula.sigma_mkDelta, HierarchySymbol.Semiformula.val_mkSigma]
  exact wb_exs_bt _ (by simp) (add (poly ‘0’) (exp2 (poly ‘#1’) (poly ‘0’)))
    (fun V _ _ e u h => by
      have h' := h; simp at h'
      rw [h'.1]; simpa [vval] using insert_le_of_le_of_le (le_refl (e 1)) (le_refl (0 : V)))
    (by wb_auto)

/-- **The provability sentence `ZFC ⊢ ⊥` has bounded witnesses**: its outer
witness, the derivation, needs only a constant bound, the sentence being
closed. -/
theorem wb_provable_falsum :
    WB M (provabilityPred (𝗭𝗙𝗖 : SetTheory) (⊥ : SetTheorySentence)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := PRAModelIOpenPairing.standardModelISigmaZero
  letI : M↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory (U := 𝗜𝚺₀) inferInstance
  exact PRAWitnessRefutationOuter.wb_provabilityPred (𝗭𝗙𝗖 : SetTheory) ⊥ wb_derivation_sigma

end models
end DiophantineConsistency.PRAWitnessDerivation
