import PA194SourceGateReduction
import PA194CloseSubstitution
import PA194EqualGateWitness
import PA194RelativeFalseAll
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194EqualGateNumeric
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
open PA194GenericRenameBase PA194GenericRenameAxiom PA194GenericRenameRules PA194RenameShiftCompatibility PA194ReplacementOpening
open PA194SourceOutputWF PA194SourceRho8Preservation PA194SourceEqualityPreservation PA194SourceHead6Preservation PA194SourceHead5Preservation
open PA194SourceGateReduction PA194CloseSubstitution PA194EqualGateWitness PA194SourceFreshClose PA194SourceDiagonalPreservation PA194SourceHead1Syntax
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

lemma close_imp_at (label depth p q : M) (hp : IsSemiformula ℒₒᵣ depth p) (hq : IsSemiformula ℒₒᵣ depth q) :
    PA194InternalFormulaClose.close label depth (imp ℒₒᵣ p q) =
      imp ℒₒᵣ (PA194InternalFormulaClose.close label depth p) (PA194InternalFormulaClose.close label depth q) := by
  unfold imp
  rw [PA194InternalFormulaClose.close_or label depth _ _ hp.isUFormula.neg hq.isUFormula,
    PA194CloseNegation.close_neg label depth p hp]

lemma close_twice_imp (b c p q : M) (hp : IsFormula ℒₒᵣ p) (hq : IsFormula ℒₒᵣ q) :
    PA194InternalFormulaClose.close c 1 (PA194InternalFormulaClose.close b 0 (imp ℒₒᵣ p q)) =
      imp ℒₒᵣ (PA194InternalFormulaClose.close c 1 (PA194InternalFormulaClose.close b 0 p))
        (PA194InternalFormulaClose.close c 1 (PA194InternalFormulaClose.close b 0 q)) := by
  rw [close_imp_at b 0 p q hp hq]
  have hp' : IsSemiformula ℒₒᵣ 1 (PA194InternalFormulaClose.close b 0 p) := by simpa using PA194InternalFormulaClose.close_wellformed b 0 p hp
  have hq' : IsSemiformula ℒₒᵣ 1 (PA194InternalFormulaClose.close b 0 q) := by simpa using PA194InternalFormulaClose.close_wellformed b 0 q hq
  exact close_imp_at c 1 _ _ hp' hq'

lemma gateConj_code (p q : M) :
    translated (gateConj p q) = imp ℒₒᵣ (imp ℒₒᵣ (translated p) (imp ℒₒᵣ (translated q) (translated 1))) (translated 1) := by
  have hq : impSource q 1 ≠ 0 := imp_nonzero_right q 1 (by norm_num)
  have hp : impSource p (impSource q 1) ≠ 0 := imp_nonzero_right _ _ hq
  have ho : impSource (impSource p (impSource q 1)) 1 ≠ 0 := imp_nonzero_right _ _ (by norm_num)
  unfold gateConj gateNeg
  rw [imp_code _ _ ho, imp_code _ _ hp, imp_code _ _ hq]

noncomputable def gateProperty (b c : M) : Bootstrapping.Semiformula M ℒₒᵣ 1 :=
  ⟨PA194InternalFormulaClose.close b 0 (translated c), by
    simpa using PA194InternalFormulaClose.close_wellformed b 0 (translated c) (fixed_all_wf c).1⟩

noncomputable def gatePointForm (b c : M) : Bootstrapping.Semiformula M ℒₒᵣ 1 :=
  (((gateProperty b c).subst ![Bootstrapping.Semiterm.fvar b]).subst ![]) 🡒
    PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.fvar b) (Bootstrapping.Semiterm.bvar 0)

lemma formula_lift_val (p : Bootstrapping.Formula M ℒₒᵣ) :
    (p.subst (![] : Bootstrapping.SemitermVec M ℒₒᵣ 0 1)).val = p.val := by
  change subst ℒₒᵣ 0 p.val = p.val
  exact subst_eq_self p.isSemiformula (by simp) (by simp)

lemma close_gate_point (b c : M) (hcb : c ≠ b) :
    PA194InternalFormulaClose.close c 0 (translated (gatePoint b c)) = (gatePointForm b c).val := by
  have hnz : impSource c (memSource c b) ≠ 0 := imp_nonzero_right _ _ (memSource_nonzero c b)
  have hp : IsFormula ℒₒᵣ (translated c) := (fixed_all_wf c).1
  have hm : IsFormula ℒₒᵣ (translated (memSource c b)) := (fixed_all_wf _).1
  unfold gatePoint
  rw [imp_code _ _ hnz, close_imp_at c 0 _ _ hp hm, membership_code, close_bit_point b c hcb]
  have hfresh : PA194InternalFormulaClose.close c 0 (translated c) = translated c :=
    formula_close_of_fixed c (c+1) 0 (translated c) (ne_of_lt (lt_add_one c)) hp (source_bounded_fresh c c (le_refl c))
  rw [hfresh]
  have hP : ((gateProperty b c).subst (![Bootstrapping.Semiterm.fvar b] : Bootstrapping.SemitermVec M ℒₒᵣ 1 0)).val = translated c := by
    change substs1 ℒₒᵣ (^&b) (PA194InternalFormulaClose.close b 0 (translated c)) = translated c
    exact reopen_identity b (translated c) hp
  have hLift : (((gateProperty b c).subst (![Bootstrapping.Semiterm.fvar b] : Bootstrapping.SemitermVec M ℒₒᵣ 1 0)).subst
      (![] : Bootstrapping.SemitermVec M ℒₒᵣ 0 1)).val = translated c := (formula_lift_val _).trans hP
  change imp ℒₒᵣ (translated c) _ = imp ℒₒᵣ _ _
  rw [hLift]
  rfl

lemma gateSeparation_code (b c : M) :
    translated (gateSeparation b b c) = ^∀ (PA194InternalFormulaClose.close b 0
      (imp ℒₒᵣ
        (imp ℒₒᵣ (imp ℒₒᵣ (PA194SourceEqualityPreservation.bitFormula b b).val
          (imp ℒₒᵣ (translated c) (PA194SourceEqualityPreservation.bitFormula c b).val))
          (imp ℒₒᵣ (imp ℒₒᵣ (PA194SourceEqualityPreservation.bitFormula c b).val (translated c)) (translated 1)))
        (translated 1))) := by
  have hpoint : impSource c (memSource c b) ≠ 0 := imp_nonzero_right _ _ (memSource_nonzero c b)
  have hleft : impSource (memSource b b) (gatePoint b c) ≠ 0 := imp_nonzero_left _ _ (memSource_nonzero b b)
  have hright : impSource (memSource c b) c ≠ 0 := imp_nonzero_left _ _ (memSource_nonzero c b)
  unfold gateSeparation
  rw [universal_code, gateConj_code, imp_code _ _ hleft, imp_code _ _ hright]
  unfold gatePoint
  rw [imp_code _ _ hpoint]
  simp only [membership_code]

noncomputable def gateDelta2 (b c : M) : Bootstrapping.Semiformula M ℒₒᵣ 2 :=
  ⟨PA194InternalFormulaClose.close c 1 (PA194InternalFormulaClose.close b 0 (translated 1)), by
    have h1 : IsSemiformula ℒₒᵣ 1 (PA194InternalFormulaClose.close b 0 (translated 1)) := by
      simpa using PA194InternalFormulaClose.close_wellformed b 0 (translated 1) (fixed_all_wf 1).1
    have h2 := PA194InternalFormulaClose.close_wellformed c 1 _ h1
    have hcast : (1:M)+1 = 2 := by norm_num
    rwa [hcast] at h2⟩

noncomputable def gateSepForm (b c : M) : Bootstrapping.Semiformula M ℒₒᵣ 1 :=
  ∀⁰ (relConj
    ((PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 0)) 🡒
      (((gateProperty b c).subst ![Bootstrapping.Semiterm.bvar 0]) 🡒
        PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)))
    ((PA194ConditionalSingleton.Bit (Bootstrapping.Semiterm.bvar 0) (Bootstrapping.Semiterm.bvar 1)) 🡒
      (gateProperty b c).subst ![Bootstrapping.Semiterm.bvar 0]) (gateDelta2 b c))

lemma semiformula_lift_val (p : Bootstrapping.Semiformula M ℒₒᵣ 1) :
    (p.subst (![Bootstrapping.Semiterm.bvar 0] : Bootstrapping.SemitermVec M ℒₒᵣ 1 2)).val = p.val := by
  change subst ℒₒᵣ ?[^#0] p.val = p.val
  exact subst_eq_self p.isSemiformula (by simp) (by simp)

lemma close_gate_separation (b c : M) (hcb : c ≠ b) :
    PA194InternalFormulaClose.close c 0 (translated (gateSeparation b b c)) = (gateSepForm b c).val := by
  let X : M := (PA194SourceEqualityPreservation.bitFormula b b).val
  let Y : M := (PA194SourceEqualityPreservation.bitFormula c b).val
  let P : M := translated c
  let D : M := translated 1
  have hx : IsFormula ℒₒᵣ X := (PA194SourceEqualityPreservation.bitFormula b b).isSemiformula
  have hy : IsFormula ℒₒᵣ Y := (PA194SourceEqualityPreservation.bitFormula c b).isSemiformula
  have hp : IsFormula ℒₒᵣ P := (fixed_all_wf c).1
  have hd : IsFormula ℒₒᵣ D := (fixed_all_wf 1).1
  have hz : IsFormula ℒₒᵣ (imp ℒₒᵣ (imp ℒₒᵣ (imp ℒₒᵣ X (imp ℒₒᵣ P Y))
      (imp ℒₒᵣ (imp ℒₒᵣ Y P) D)) D) := by simp [hx,hy,hp,hd]
  rw [gateSeparation_code]
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
    close_bit_twice_diag b c,close_bit_twice_cross b c hcb]
  dsimp only [X,Y]
  rw [close_bit_twice_diag b c,close_bit_twice_cross b c hcb]
  have hpLift := semiformula_lift_val (gateProperty b c)
  change _ = ^∀ (relConj _ _ (gateDelta2 b c)).val
  simp only [relConj,Bootstrapping.Semiformula.val_imp,PA194ConditionalSingleton.Bit,
    PA194SourceHead5Preservation.bitBase]
  rw [hpLift]
  rfl

noncomputable def gateDelta (c : M) : Bootstrapping.Semiformula M ℒₒᵣ 1 :=
  ⟨PA194InternalFormulaClose.close c 0 (translated 1), by
    simpa using PA194InternalFormulaClose.close_wellformed c 0 (translated 1) (fixed_all_wf 1).1⟩

lemma equal_gate_tail (b c : M) (hcb : c ≠ b) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (gateNeg (gateTail b b c))) := by
  let P := gateProperty b c
  let D2 := gateDelta2 b c
  let Point := gatePointForm b c
  let Sep := gateSepForm b c
  let E := gateDelta c
  let C : Bootstrapping.Formula M ℒₒᵣ := ⟨translated 1,(fixed_all_wf 1).1⟩
  have hw : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∃⁰ (Point ⋏ Sep) := by
    change (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∃⁰ (collisionBody b P D2)
    exact collision_witness b P D2
  have he : (𝗣𝗔 : ArithmeticTheory).internalize M ⊢ ∀⁰ ∼E := by
    exact PA194RelativeFalseAll.internal_relative_false_all c
  have hres := tail_from_witness Point Sep E C hw he
  have hp : IsFormula ℒₒᵣ (translated (gatePoint b c)) := (fixed_all_wf _).1
  have hs : IsFormula ℒₒᵣ (translated (gateSeparation b b c)) := (fixed_all_wf _).1
  have hd : IsFormula ℒₒᵣ (translated (1:M)) := (fixed_all_wf _).1
  have hnegpoint : impSource (gatePoint b c) 1 ≠ 0 := imp_nonzero_right _ _ (by norm_num)
  have hinner : impSource (gateSeparation b b c) (impSource (gatePoint b c) 1) ≠ 0 :=
    imp_nonzero_left _ _ (allSource_nonzero _ _)
  have hout : impSource (allSource c (impSource (gateSeparation b b c) (impSource (gatePoint b c) 1))) 1 ≠ 0 :=
    imp_nonzero_left _ _ (allSource_nonzero _ _)
  unfold gateNeg gateTail
  change Provable (𝗣𝗔 : ArithmeticTheory) (translated (impSource (allSource c (impSource (gateSeparation b b c) (impSource (gatePoint b c) 1))) 1))
  rw [imp_code _ _ hout, universal_code, imp_code _ _ hinner, imp_code _ _ hnegpoint]
  rw [close_imp_at c 0 _ _ hs (IsSemiformula.imp.mpr ⟨hp,hd⟩),
    close_imp_at c 0 _ _ hp hd, close_gate_separation b c hcb, close_gate_point b c hcb]
  change Provable (𝗣𝗔 : ArithmeticTheory) (((∀⁰ (Sep 🡒 Point 🡒 E)) 🡒 C).val)
  exact (tprovable_iff_provable).mp hres

lemma equal_guarded_gate (b c : M) :
    Provable (𝗣𝗔 : ArithmeticTheory) (translated (oldGate b b c)) := by
  apply guarded_gate_if_tail b b c
  intro hcb _
  exact equal_gate_tail b c hcb

lemma equal_old_bundle (b c : M) (hcb : c ≠ b) :
    Provable (𝗣𝗔 : ArithmeticTheory)
      (translated (gateNeg (impSource (impSource (memSource b b) (allSource c (memSource b b))) (gateTail b b c)))) := by
  exact old_gate_reduction b b c (gateTail b b c) hcb hcb (equal_gate_tail b c hcb)

#print axioms equal_guarded_gate
#print axioms equal_old_bundle
#print axioms equal_gate_tail
#print axioms close_gate_separation
#print axioms gateSeparation_code
#print axioms close_gate_point
#print axioms close_twice_imp
#print axioms gateConj_code
end models
end PA194EqualGateNumeric
