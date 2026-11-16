module
public import M6PA.Theory
public import M6PA.Calibration.RelationalPredicateTemplateSuccessorSyntax
public import M6PA.Calibration.RelationalPredicateTemplateClosedCalibration
public import M6PA.Calibration.RelationalPredicateTemplateLiftSyntax
public import M6PA.Calibration.RelationalPredicateTemplateNegation
public import PA196.Arithmetic.Transport.FoundationRelationalSequentSeparationCode
public import M6PA.Calibration.NumericPAeqTermConstructors
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalPredicateTemplate
open M6.PA.RelationalPredicateTemplate.Successor

namespace PA196.Arithmetic.Transport.RelationalPredicateTemplate.Successor
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Ordinal
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local notation "L" => RelationalSource.language

theorem domain_body_value {P b f : V} (h : EnvironmentsValid (1:V) 1 b f)
    (hb : IdentityBound 1 b) :
    formulaValue (domain (.bvar 0 : Term 1)) P b f=NumericPAeqTerm.domainCode (qqBvar 0) := by
  have he := lift_domain (.bvar 0 : Semiterm L Nat 1)
  simp only [liftTerm,FFL.FirstOrder.Semiterm.lMap] at he
  rw [←he]
  rw [closed_formulaValue_lift _ (by simpa using h) hb (by
    intro i hi
    have hc : (RelationalSource.Ordinal.domain (.bvar 0 : Semiterm L Nat 1)).freeVariables=∅ := by decide
    simp [Semiformula.FVar?,hc] at hi)]
  simpa using (NumericPAeqTerm.domainCode_quote (V:=V) (.bvar 0 : Semiterm L Nat 1)).symm

theorem successor_body_value {P b f : V} (h : EnvironmentsValid (2:V) 2 b f)
    (hb : IdentityBound 2 b) :
    formulaValue (successor (.bvar 0 : Term 2) (.bvar 1)) P b f=
      NumericPAeqTerm.successorCode (qqBvar 0) (qqBvar 1) := by
  have he := lift_successor (.bvar 0 : Semiterm L Nat 2) (.bvar 1)
  simp only [liftTerm,FFL.FirstOrder.Semiterm.lMap] at he
  rw [←he]
  rw [closed_formulaValue_lift _ (by simpa using h) hb (by
    intro i hi
    have hc : (RelationalSource.Ordinal.successor (.bvar 0 : Semiterm L Nat 2) (.bvar 1)).freeVariables=∅ := by decide
    simp [Semiformula.FVar?,hc] at hi)]
  simpa using (NumericPAeqTerm.successorCode_quote (V:=V) (.bvar 0 : Semiterm L Nat 2) (.bvar 1)).symm

theorem pred_zero_value {s : Nat} {P b f : V} (hP : IsSemiformula L 1 P)
    (hb : IdentityBound (s+1) b) :
    formulaValue (pred (.bvar 0 : Term (s+1))) P b f=P := by
  have hi := hb 0
  simp only [Fin.val_zero,Nat.cast_zero] at hi
  simp only [pred,formulaValue,atomValue,termValue,Matrix.cons_val_zero,Fin.val_zero,Nat.cast_zero,hi]
  exact RelationalSource.Numeric.source_identity_subst hP

theorem input_value {P f : V} (hP : IsSemiformula L 1 P)
    (hf : IsSemitermVec L (len f) 0 f) :
    formulaValue input P 0 f=qqExs (qqAnd (NumericPAeqTerm.domainCode (qqBvar 0)) P) := by
  have h0 : EnvironmentsValid (0:V) 0 0 f := ⟨by simp,hf⟩
  have h1 : EnvironmentsValid (1:V) 1 (bindBound 0) (bindFree f) := by simpa using bindEnvironments_valid h0
  have hi : IdentityBound 1 (bindBound (0:V)) := identityBound_bind h0.1 (fun i => Fin.elim0 i)
  change qqExs (qqAnd (formulaValue (domain (.bvar 0 : Term 1)) P (bindBound 0) (bindFree f))
    (formulaValue (pred (.bvar 0 : Term 1)) P (bindBound 0) (bindFree f)))=_
  rw [domain_body_value h1 hi,pred_zero_value hP hi]

theorem output_value {P f : V} (hP : IsSemiformula L 1 P)
    (hf : IsSemitermVec L (len f) 0 f) :
    formulaValue output P 0 f=qqExs (NumericPAeqTerm.successorValue (qqBvar 0) P) := by
  have h0 : EnvironmentsValid (0:V) 0 0 f := ⟨by simp,hf⟩
  have h1 : EnvironmentsValid (1:V) 1 (bindBound 0) (bindFree f) := by simpa using bindEnvironments_valid h0
  have hi1 : IdentityBound 1 (bindBound (0:V)) := identityBound_bind h0.1 (fun i => Fin.elim0 i)
  have h2 : EnvironmentsValid (2:V) 2 (bindBound (bindBound 0)) (bindFree (bindFree f)) := by
    convert bindEnvironments_valid h1 using 1 <;> norm_num
  have hi2 : IdentityBound 2 (bindBound (bindBound (0:V))) := identityBound_bind (s:=1) (by simpa using h1.1) hi1
  change qqExs (qqAnd (formulaValue (domain (.bvar 0 : Term 1)) P (bindBound 0) (bindFree f))
    (qqExs (qqAnd (formulaValue (pred (.bvar 0 : Term 2)) P (bindBound (bindBound 0)) (bindFree (bindFree f)))
      (formulaValue (successor (.bvar 0 : Term 2) (.bvar 1)) P (bindBound (bindBound 0)) (bindFree (bindFree f))))))=_
  rw [domain_body_value h1 hi1,pred_zero_value hP hi2,successor_body_value h2 hi2]
  simp [NumericPAeqTerm.successorValue]

noncomputable def successorTotalityCode (P : V) : V :=
  imp L (qqExs (qqAnd (NumericPAeqTerm.domainCode (qqBvar 0)) P))
    (qqExs (NumericPAeqTerm.successorValue (qqBvar 0) P))

theorem statement_value {P f : V} (hP : IsSemiformula L 1 P)
    (hf : IsSemitermVec L (len f) 0 f) :
    formulaValue statement P 0 f=successorTotalityCode P := by
  change qqOr (formulaValue (∼input) P 0 f) (formulaValue output P 0 f)=_
  simp only [Semiformula.neg_eq]
  rw [formulaValue_neg input hP (show EnvironmentsValid (0:V) 0 0 f from ⟨by simp,hf⟩)
    (by intro i hi; simp [Semiformula.FVar?,input_closed] at hi),input_value hP hf,output_value hP hf]
  rfl

#print axioms input_value
#print axioms output_value
#print axioms statement_value
end PA196.Arithmetic.Transport.RelationalPredicateTemplate.Successor

