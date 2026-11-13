module
public import M6PA.Theory
public import M6PA.Calibration.FoundationPAeqCodeInductionTemplate
@[expose] public section
/-! Literal coded identities linking the successor/additive body template to
its fixed-vector definitions; these are arbitrary-model equalities. -/
namespace M6.PA.FoundationPAeqCode
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem paeqSubstCode_cast {n : Nat} (t : SyntacticSemiterm Presentation.language n) :
    (paeqSubstCode t : V)=(⌜t⌝ : V)∷0 := by
  rw [paeqSubstCode,←Semiterm.quote_eq_encode' (V:=V) ![t]]
  simp [Matrix.constant_eq_singleton,Semiterm.quote_def]
theorem sourceSubstCode_cast {n : Nat} (t : ArithmeticSemiterm Nat n) :
    (substCode t : V)=(⌜t⌝ : V)∷0 := by
  rw [substCode,←Semiterm.quote_eq_encode' (V:=V) ![t]]
  simp [Matrix.constant_eq_singleton,Semiterm.quote_def]

theorem typedInductionBody_val (p : Semiformula V Presentation.language 1) :
    (typedInductionBody p).val=targetIndBody p.val := by
  simp [typedInductionBody,targetIndBody,paeqSubstCode_cast,Semiterm.quote_def]

noncomputable def targetAdditiveBody (p : V) : V :=
  imp Presentation.language (substs1 Presentation.language zeroCode p)
    (imp Presentation.language
      (qqAll (imp Presentation.language p
        (substs1 Presentation.language (qqFunc 2 2 (qqBvar 0∷oneCode∷0)) p))) (qqAll p))
theorem typedAdditiveInductionBody_val (p : Semiformula V Presentation.language 1) :
    (typedAdditiveInductionBody p).val=targetAdditiveBody p.val := by
  simp [typedAdditiveInductionBody,targetAdditiveBody,substs1,oneCode]

theorem induction_body_transport_raw {p : V} (hp : IsSemiformula Presentation.language 1 p) :
    Provable Presentation.ordinaryPAeq (imp Presentation.language (targetIndBody p) (targetAdditiveBody p)) := by
  simpa only [typedInductionBody_val,typedAdditiveInductionBody_val] using induction_body_transport_numeric p hp


theorem formulaCode_imp (param : V) {p q : V}
    (hp : IsUFormula ℒₒᵣ p) (hq : IsUFormula ℒₒᵣ q) :
    formulaCode param (imp ℒₒᵣ p q)=
      imp Presentation.language (formulaCode param p) (formulaCode param q) := by
  rw [imp,formulaCode_or _ _ _ hp.neg hq,formulaCode_neg _ hp]
  rfl

variable [V↓[ℒₒᵣ] ⊧* theory]

/-- Literal translation of the original additive induction body, for arbitrary
model-valued p. Only the fixed zero and x+1 terms are quoted. -/
theorem formulaCode_indBody {p : V} (hp : IsSemiformula ℒₒᵣ 1 p) :
    formulaCode 0 (indBodyVal p)=targetAdditiveBody (formulaCode 0 p) := by
  have hz : IsSemiterm ℒₒᵣ (0:V) (⌜(‘0’ : ArithmeticSemiterm Nat 0)⌝ : V) := by
    simp [Semiterm.quote_def]
  have hs : IsSemiterm ℒₒᵣ (1:V) (⌜(‘#0 + 1’ : ArithmeticSemiterm Nat 1)⌝ : V) :=
    (⌜(‘#0 + 1’ : ArithmeticSemiterm Nat 1)⌝ : Bootstrapping.Semiterm V ℒₒᵣ 1).isSemiterm_one
  have hpz := IsSemiformula.substs1 hz hp
  have hps := IsSemiformula.substs1 hs hp
  rw [indBodyVal,sourceSubstCode_cast,sourceSubstCode_cast,←substs1,←substs1]
  rw [formulaCode_imp _ hpz.isUFormula (by simp [imp,hp.isUFormula,hps.isUFormula]),
    formulaCode_imp _ (by simp [imp,hp.isUFormula,hps.isUFormula]) (by simp [hp.isUFormula]),
    formulaCode_all _ _ (by simp [imp,hp.isUFormula,hps.isUFormula]),
    formulaCode_all _ _ hp.isUFormula,
    formulaCode_imp _ hp.isUFormula hps.isUFormula,
    formulaCode_substs1 _ hp hz,formulaCode_substs1 _ hp hs,
    termCode_quote,termCode_quote]
  rw [show Presentation.term (‘0’ : ArithmeticSemiterm Nat 0)=Presentation.zero from rfl,
    show Presentation.term (‘#0 + 1’ : ArithmeticSemiterm Nat 1)=
      Presentation.add (.bvar 0) (Presentation.succ Presentation.zero) from rfl]
  simp [targetAdditiveBody,Presentation.quote_zero,Presentation.quote_successor,
    quote_paeq_add,oneCode,zeroCode]

/-- An actual target proof number of the successor-to-original-body implication.
This does not supply a canonical closed successor induction axiom. -/
theorem original_indBody_transport {p : V} (hp : IsSemiformula ℒₒᵣ 1 p) :
    Provable Presentation.ordinaryPAeq
      (imp Presentation.language (targetIndBody (formulaCode 0 p))
        (formulaCode 0 (indBodyVal p))) := by
  rw [formulaCode_indBody hp]
  exact induction_body_transport_raw (formulaCode_valid 0 hp)

#print axioms formulaCode_imp
#print axioms formulaCode_indBody
#print axioms original_indBody_transport
#print axioms paeqSubstCode_cast
#print axioms sourceSubstCode_cast
#print axioms typedInductionBody_val
#print axioms typedAdditiveInductionBody_val
#print axioms induction_body_transport_raw
end M6.PA.FoundationPAeqCode


