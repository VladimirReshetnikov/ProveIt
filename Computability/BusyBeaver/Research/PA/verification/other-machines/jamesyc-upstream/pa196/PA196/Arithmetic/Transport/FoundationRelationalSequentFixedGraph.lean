module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentZeroEnvironment
public import Foundation.FirstOrder.Arithmetic.R0.Basic
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Fixed standard graph calibration by Sigma-one completeness. Each input
and output is a host natural number. This does not assert computation of
arbitrary nonstandard inputs or uniform internal completeness. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

noncomputable def fixedTranslateSentence (param p : Nat) : ArithmeticSentence :=
  “!translateGraph ↑(translate param p) ↑param ↑p”

theorem pa_proves_fixed_translate (param p : Nat) : theory ⊢ fixedTranslateSentence param p := by
  apply Arithmetic.sigma_one_completeness
  · simp [fixedTranslateSentence]
  · simp [fixedTranslateSentence,models_iff,translate_graph,numeral_eq_natCast,natCast_nat]

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory]

theorem translate_fixed_all_models (param p : Nat) :
    translate (param:V) (p:V)=(translate param p:Nat) := by
  have h := consequence_iff.mp (Theory.Proof.sound (pa_proves_fixed_translate param p)) V inferInstance
  simpa [fixedTranslateSentence,models_iff,translate_graph,numeral_eq_natCast,eq_comm] using h

noncomputable def fixedParametersSentence (b f lo z : Nat) : ArithmeticSentence :=
  “!parametersGraph ↑(parameters b f lo z) ↑b ↑f ↑lo ↑z”

theorem pa_proves_fixed_parameters (b f lo z : Nat) : theory ⊢ fixedParametersSentence b f lo z := by
  apply Arithmetic.sigma_one_completeness
  · simp [fixedParametersSentence]
  · simp [fixedParametersSentence,models_iff,parameters_graph,numeral_eq_natCast,natCast_nat,Matrix.comp_vecCons'']

theorem parameters_fixed_all_models (b f lo z : Nat) :
    parameters (b:V) (f:V) (lo:V) (z:V)=(parameters b f lo z:Nat) := by
  have h := consequence_iff.mp (Theory.Proof.sound (pa_proves_fixed_parameters b f lo z)) V inferInstance
  simpa [fixedParametersSentence,models_iff,parameters_graph,numeral_eq_natCast,eq_comm,Matrix.comp_vecCons''] using h

noncomputable def fixedZeroEnvironmentSentence (n : Nat) : ArithmeticSentence :=
  “!zeroEnvironmentGraph ↑(zeroEnvironment n) ↑n”

theorem pa_proves_fixed_zeroEnvironment (n : Nat) : theory ⊢ fixedZeroEnvironmentSentence n := by
  apply Arithmetic.sigma_one_completeness
  · simp [fixedZeroEnvironmentSentence]
  · simp [fixedZeroEnvironmentSentence,models_iff,zeroEnvironment_graph,numeral_eq_natCast,natCast_nat]

theorem zeroEnvironment_fixed_all_models (n : Nat) :
    zeroEnvironment (n:V)=(zeroEnvironment n:Nat) := by
  have h := consequence_iff.mp (Theory.Proof.sound (pa_proves_fixed_zeroEnvironment n)) V inferInstance
  simpa [fixedZeroEnvironmentSentence,models_iff,zeroEnvironment_graph,numeral_eq_natCast,eq_comm] using h

theorem translate_fixed_parameters_all_models (b f lo z p : Nat) :
    translate (parameters (b:V) (f:V) (lo:V) (z:V)) (p:V)=
      (translate (parameters b f lo z) p:Nat) := by
  rw [parameters_fixed_all_models]
  exact translate_fixed_all_models _ _

#print axioms pa_proves_fixed_translate
#print axioms translate_fixed_all_models
#print axioms pa_proves_fixed_parameters
#print axioms parameters_fixed_all_models
#print axioms pa_proves_fixed_zeroEnvironment
#print axioms zeroEnvironment_fixed_all_models
#print axioms translate_fixed_parameters_all_models
end PA196.Arithmetic.Transport.RelationalSource.Numeric

