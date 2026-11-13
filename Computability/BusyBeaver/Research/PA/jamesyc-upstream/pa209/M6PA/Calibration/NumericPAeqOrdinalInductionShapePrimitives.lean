module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSuccessorCalibration
public import M6PA.Calibration.RelationalPredicateTemplateOrdinalCode
@[expose] public section
namespace M6.PA.NumericPAeqOrdinalInductionShape
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateTemplate RelationalPredicateTemplate.Ordinal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem closed_imp_value {s:Nat} (p q:RelationalPredicateTemplate.Formula s) {n P b f:V}
    (hP:IsSemiformula L 1 P) (h:EnvironmentsValid (s:V) n b f) (hc:p.freeVariables=∅):
    formulaValue (p 🡒 q) P b f=imp L (formulaValue p P b f) (formulaValue q P b f) := by
  change qqOr (formulaValue p.neg P b f) (formulaValue q P b f)=_
  rw [formulaValue_neg p hP h (by intro i hi; simp [FFL.FirstOrder.Semiformula.FVar?,hc] at hi)]
  rfl

theorem domain_two_value (i:Fin 2) {P b f:V} (h:EnvironmentsValid (2:V) 2 b f) (hb:IdentityBound 2 b):
    formulaValue (domain (.bvar i : Term 2)) P b f=NumericPAeqTerm.domainCode (qqBvar (i.val:V)) := by
  have he := lift_domain (.bvar i : Semiterm L Nat 2)
  simp only [liftTerm,FFL.FirstOrder.Semiterm.lMap] at he
  rw [←he,closed_formulaValue_lift _ (by simpa using h) hb (by
    intro j hj
    have hc : (RelationalSource.Ordinal.domain (.bvar i : Semiterm L Nat 2)).freeVariables=∅ := by fin_cases i <;> decide
    simp [FFL.FirstOrder.Semiformula.FVar?,hc] at hj)]
  simpa using (NumericPAeqTerm.domainCode_quote (V:=V) (.bvar i : Semiterm L Nat 2)).symm

theorem zero_body_value {P b f:V} (h:EnvironmentsValid (1:V) 1 b f) (hb:IdentityBound 1 b):
    formulaValue (zero (.bvar 0 : Term 1)) P b f=NumericPAeqTerm.zeroCode (qqBvar 0) := by
  have he := lift_zero (.bvar 0 : Semiterm L Nat 1)
  simp only [liftTerm,FFL.FirstOrder.Semiterm.lMap] at he
  rw [←he,closed_formulaValue_lift _ (by simpa using h) hb (by
    intro j hj
    have hc : (RelationalSource.Ordinal.zero (.bvar 0 : Semiterm L Nat 1)).freeVariables=∅ := by decide
    simp [FFL.FirstOrder.Semiformula.FVar?,hc] at hj)]
  simpa using (NumericPAeqTerm.zeroCode_quote (V:=V) (.bvar 0 : Semiterm L Nat 1)).symm

theorem successor_step_value {P b f:V} (h:EnvironmentsValid (2:V) 2 b f) (hb:IdentityBound 2 b):
    formulaValue (successor (.bvar 1 : Term 2) (.bvar 0)) P b f=
      NumericPAeqTerm.successorCode (qqBvar 1) (qqBvar 0) := by
  have he := lift_successor (.bvar 1 : Semiterm L Nat 2) (.bvar 0)
  simp only [liftTerm,FFL.FirstOrder.Semiterm.lMap] at he
  rw [←he,closed_formulaValue_lift _ (by simpa using h) hb (by
    intro j hj
    have hc : (RelationalSource.Ordinal.successor (.bvar 1 : Semiterm L Nat 2) (.bvar 0)).freeVariables=∅ := by decide
    simp [FFL.FirstOrder.Semiformula.FVar?,hc] at hj)]
  simpa using (NumericPAeqTerm.successorCode_quote (V:=V) (.bvar 1 : Semiterm L Nat 2) (.bvar 0)).symm

theorem hole_at_value {s:Nat} (i:Fin s) {P b f:V} (hb:IdentityBound s b):
    formulaValue (.rel .predicate ![.bvar i]) P b f=substs1 L (qqBvar (i.val:V)) P := by
  simp only [formulaValue,atomValue,termValue,Matrix.cons_val_zero,hb i]
#print axioms closed_imp_value
#print axioms domain_two_value
#print axioms zero_body_value
#print axioms successor_step_value
#print axioms hole_at_value
end M6.PA.NumericPAeqOrdinalInductionShape
