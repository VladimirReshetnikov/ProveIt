import PA194EqualGateNumeric
import PA194GeneralGateWitness
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 5000000
namespace PA194DistinctGateNumeric
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194ReplacementOpening
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194SourceHead5Preservation
open PA194SourceGateReduction PA194CloseSubstitution PA194EqualGateWitness PA194SourceFreshClose PA194SourceDiagonalPreservation PA194SourceHead1Syntax PA194EqualGateNumeric
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma close_bit_twice_other (a b c : M) (hab : a ≠ b) (hca : c ≠ a) :
    PA194InternalFormulaClose.close c 1 (PA194InternalFormulaClose.close b 0 (PA194SourceEqualityPreservation.bitFormula a b).val) =
      ((PA194SourceHead5Preservation.bitBase (M := M)).subst (![Bootstrapping.Semiterm.bvar 0,Bootstrapping.Semiterm.fvar a] : Bootstrapping.SemitermVec M ℒₒᵣ 2 2)).val := by
  rw [close_bitFormula]
  have h := close_bit_template c 1 (^#0) (^&a) (by simp) (by simp)
  simp only [PA194InternalClose.close, Language.TermRec.Construction.result_bvar, Language.TermRec.Construction.result_fvar,
    PA194InternalClose.construction,Matrix.cons_val_zero,Matrix.cons_val_one] at h
  simpa [closedBit,PA194SourceHead5Preservation.bitBase,Bootstrapping.Semiformula.val_substs,
    Bootstrapping.SemitermVec.val,matrixToVec,adjoin_def,Bootstrapping.Semiterm.bvar,Bootstrapping.Semiterm.fvar,
    hca,hab,Ne.symm hab] using h
lemma gateSeparation_code_distinct (a b c : M) :
    translated (gateSeparation a b c) = ^∀ (PA194InternalFormulaClose.close b 0
      (imp ℒₒᵣ
        (imp ℒₒᵣ (imp ℒₒᵣ (PA194SourceEqualityPreservation.bitFormula a b).val
          (imp ℒₒᵣ (translated c) (PA194SourceEqualityPreservation.bitFormula c b).val))
          (imp ℒₒᵣ (imp ℒₒᵣ (PA194SourceEqualityPreservation.bitFormula c b).val (translated c)) (translated 1)))
        (translated 1))) := by
  have hpoint : impSource c (memSource c b) ≠ 0 := imp_nonzero_right _ _ (memSource_nonzero c b)
  have hleft : impSource (memSource a b) (gatePoint b c) ≠ 0 := imp_nonzero_left _ _ (memSource_nonzero a b)
  have hright : impSource (memSource c b) c ≠ 0 := imp_nonzero_left _ _ (memSource_nonzero c b)
  unfold gateSeparation
  rw [universal_code, gateConj_code, imp_code _ _ hleft, imp_code _ _ hright]
  unfold gatePoint
  rw [imp_code _ _ hpoint]
  simp only [membership_code]

noncomputable def gateSepFormDistinct (a b c : M) : Bootstrapping.Semiformula M ℒₒᵣ 1 :=
  ∀⁰ (relConj
    ((PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.fvar a)) 🡒
      (((gateProperty b c).subst ![Bootstrapping.Semiterm.bvar 0]) 🡒
        PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)))
    ((PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)) 🡒
      (gateProperty b c).subst ![Bootstrapping.Semiterm.bvar 0]) (gateDelta2 b c))

lemma close_gate_separation_distinct (a b c : M) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    PA194InternalFormulaClose.close c 0 (translated (gateSeparation a b c)) = (gateSepFormDistinct a b c).val := by
  let X : M := (PA194SourceEqualityPreservation.bitFormula a b).val
  let Y : M := (PA194SourceEqualityPreservation.bitFormula c b).val
  let P : M := translated c
  let D : M := translated 1
  have hx : IsFormula ℒₒᵣ X := (PA194SourceEqualityPreservation.bitFormula a b).isSemiformula
  have hy : IsFormula ℒₒᵣ Y := (PA194SourceEqualityPreservation.bitFormula c b).isSemiformula
  have hp : IsFormula ℒₒᵣ P := (fixed_all_wf c).1
  have hd : IsFormula ℒₒᵣ D := (fixed_all_wf 1).1
  have hz : IsFormula ℒₒᵣ (imp ℒₒᵣ (imp ℒₒᵣ (imp ℒₒᵣ X (imp ℒₒᵣ P Y))
      (imp ℒₒᵣ (imp ℒₒᵣ Y P) D)) D) := by simp [hx,hy,hp,hd]
  rw [gateSeparation_code_distinct]
  change PA194InternalFormulaClose.close c 0 (^∀ (PA194InternalFormulaClose.close b 0
    (imp ℒₒᵣ (imp ℒₒᵣ (imp ℒₒᵣ X (imp ℒₒᵣ P Y)) (imp ℒₒᵣ (imp ℒₒᵣ Y P) D)) D))) = _
  rw [PA194InternalFormulaClose.close_all c 0 _ (PA194InternalFormulaClose.close_wellformed b 0 _ hz).isUFormula]
  simp only [zero_add]
  have hPfresh : PA194InternalFormulaClose.close c 1 (PA194InternalFormulaClose.close b 0 P) = PA194InternalFormulaClose.close b 0 P := by
    have hf := source_bounded_fresh c c (le_refl c)
    have hf' := formula_close_keeps_fixed c (c+1) b 0 P (ne_of_lt (lt_add_one c)) hp hf
    have hw : IsSemiformula ℒₒᵣ 1 (PA194InternalFormulaClose.close b 0 P) := by simpa using PA194InternalFormulaClose.close_wellformed b 0 P hp
    exact formula_close_of_fixed c (c+1) 1 _ (ne_of_lt (lt_add_one c)) hw hf'
  simp only [close_twice_imp, IsSemiformula.imp, hx,hy,hp,hd, and_self, hPfresh,
    close_bit_twice_other a b c hab hca,close_bit_twice_cross b c hcb]
  dsimp only [X,Y]
  rw [close_bit_twice_other a b c hab hca,close_bit_twice_cross b c hcb]
  have hpLift := semiformula_lift_val (gateProperty b c)
  change _ = ^∀ (relConj _ _ (gateDelta2 b c)).val
  simp only [relConj,Bootstrapping.Semiformula.val_imp,PA194ConditionalSingleton.Bit,
    PA194SourceHead5Preservation.bitBase]
  rw [hpLift]
  rfl

lemma distinct_gate_tail (a b c : M) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (gateNeg (gateTail a b c))) := by
  let P := gateProperty b c
  let D2 := gateDelta2 b c
  let Point := gatePointForm b c
  let Sep := gateSepFormDistinct a b c
  let E := gateDelta c
  let C : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1,(fixed_all_wf 1).1⟩
  have hw : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∃⁰ (Point ⋏ Sep) := by
    change (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∃⁰ (PA194GeneralGateWitness.witnessBody a b P D2)
    exact PA194GeneralGateWitness.witness a b P D2
  have he : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∀⁰ ∼E := by
    exact PA194RelativeFalseAll.internal_relative_false_all c
  have hres := tail_from_witness Point Sep E C hw he
  have hp : IsFormula ℒₒᵣ (translated (gatePoint b c)) := (fixed_all_wf _).1
  have hs : IsFormula ℒₒᵣ (translated (gateSeparation a b c)) := (fixed_all_wf _).1
  have hd : IsFormula ℒₒᵣ (translated (1:M)) := (fixed_all_wf _).1
  have hnegpoint : impSource (gatePoint b c) 1 ≠ 0 := imp_nonzero_right _ _ (by norm_num)
  have hinner : impSource (gateSeparation a b c) (impSource (gatePoint b c) 1) ≠ 0 :=
    imp_nonzero_left _ _ (allSource_nonzero _ _)
  have hout : impSource (allSource c (impSource (gateSeparation a b c) (impSource (gatePoint b c) 1))) 1 ≠ 0 :=
    imp_nonzero_left _ _ (allSource_nonzero _ _)
  unfold gateNeg gateTail
  change Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource (allSource c (impSource (gateSeparation a b c) (impSource (gatePoint b c) 1))) 1))
  rw [imp_code _ _ hout, universal_code, imp_code _ _ hinner, imp_code _ _ hnegpoint]
  rw [close_imp_at c 0 _ _ hs (IsSemiformula.imp.mpr ⟨hp,hd⟩),
    close_imp_at c 0 _ _ hp hd, close_gate_separation_distinct a b c hab hca hcb, close_gate_point b c hcb]
  change Provable (𝗣𝗔 : ArithmeticTheory) (((∀⁰ (Sep 🡒 Point 🡒 E)) 🡒 C).val)
  exact (tprovable_iff_provable).mp hres

#print axioms distinct_gate_tail
#print axioms close_gate_separation_distinct
#print axioms gateSeparation_code_distinct
#print axioms close_bit_twice_other
end models
end PA194DistinctGateNumeric
