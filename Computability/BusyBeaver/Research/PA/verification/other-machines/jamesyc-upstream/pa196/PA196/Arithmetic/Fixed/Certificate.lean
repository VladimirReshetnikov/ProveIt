module
public import PA196.Arithmetic.Certificates.Logic
public import PA196.Commands.Compiler
public import M6PA.Model.PATheory
public import Foundation.FirstOrder.Arithmetic.R0.Basic
@[expose] public section

/-! A fixed standard derivation supplies a genuine numeric checker witness.
The encoder is assembled from the already proved all-model constructors,
specialized to Nat. Sigma-one completeness subsequently transfers only this
fixed standard conclusion; no internal universal completeness is assumed. -/
namespace PA196.Arithmetic.Fixed
open M6.PA
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open Certificates Certificates.Dominated Checker HeadGraphs

 theorem implication_standard (a b : Nat) :
    Certificates.Dominated.wim a b = PA196.Logic.wim a b := by
  rw [Certificates.Dominated.wim,implicationValue,M6.PA.ActualArithmeticGraph.eval_standard,
    implication_exact]
  rfl

 theorem universal_standard (a b : Nat) :
    Certificates.Logic.wal a b = PA196.Logic.wal a b := by
  rw [Certificates.Logic.wal,universalValue,M6.PA.ActualArithmeticGraph.eval_standard,
    universal_exact]
  rfl

section GenericLeaves
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
noncomputable def leaf1 (a b : V) :
    Certificate (M6.PA.ActualArithmeticGraph.eval head1Expr a b 0 0) :=
  ⟨leafCertificate 2 (pack2Value a b),verify_head1 a b⟩
noncomputable def leaf2 (a b c : V) :
    Certificate (M6.PA.ActualArithmeticGraph.eval head2Expr a b c 0) :=
  ⟨leafCertificate 3 (pack3Value a b c),verify_head2 a b c⟩
noncomputable def leaf3 (a b c : V) :
    Certificate (M6.PA.ActualArithmeticGraph.eval head3Expr a b c 0) :=
  ⟨leafCertificate 4 (pack3Value a b c),verify_head3 a b c⟩
noncomputable def leaf4 (a b c : V) :
    Certificate (M6.PA.ActualArithmeticGraph.eval head4Expr a b c 0) :=
  ⟨leafCertificate 5 (pack3Value a b c),verify_head4 a b c⟩
noncomputable def leaf5 (a b : V) :
    Certificate (M6.PA.ActualArithmeticGraph.eval head5Expr a b 0 0) :=
  ⟨leafCertificate 6 (pack2Value a b),verify_head5 a b⟩
noncomputable def leaf6 (a b c : V) :
    Certificate (M6.PA.ActualArithmeticGraph.eval head6Expr a b c 0) :=
  ⟨leafCertificate 7 (pack3Value a b c),verify_head6 a b c⟩
noncomputable def leaf8 (a b c u : V) (hu : u ≤ a) :
    Certificate (M6.PA.ActualArithmeticGraph.eval rho8Expr a b c u) :=
  ⟨leafCertificate 8 (pack4Value a b c u),verify_r8 a b c u hu⟩
noncomputable def leafGate (a b c : V) (ha : c ≠ a) (hb : c ≠ b) :
    Certificate (M6.PA.ActualArithmeticGraph.eval bundleExpr a b c 0) :=
  ⟨leafCertificate 9 (pack3Value a b c),verify_bundle a b c ha hb⟩
end GenericLeaves

noncomputable def ofDerivation {a : Nat} (p : PA196.Logic.Derivation a) : Certificate a := by
  induction p with
  | @mp a b p q ihp ihq =>
    exact Certificate.mp ihp ((implication_standard a b).symm ▸ ihq)
  | @all x a p ih =>
    exact universal_standard x a ▸ Certificate.all x ih
  | h1 d h =>
    simpa only [M6.PA.ActualArithmeticGraph.eval_standard,head1_exact,
      ← Commands.logic_head1_code] using leaf1 d h
  | h2 d a h =>
    simpa only [M6.PA.ActualArithmeticGraph.eval_standard,head2_exact,
      ← Commands.logic_head2_code] using leaf2 d a h
  | h3 h d a =>
    simpa only [M6.PA.ActualArithmeticGraph.eval_standard,head3_exact,
      ← Commands.logic_head3_code] using leaf3 d a h
  | h4 h d a =>
    simpa only [M6.PA.ActualArithmeticGraph.eval_standard,head4_exact,
      ← Commands.logic_head4_code] using leaf4 d a h
  | h5 d h =>
    simpa only [M6.PA.ActualArithmeticGraph.eval_standard,head5_exact,
      ← Commands.logic_head5_code] using leaf5 d h
  | h6 d a h =>
    simpa only [M6.PA.ActualArithmeticGraph.eval_standard,head6_exact,
      ← Commands.logic_head6_code] using leaf6 d a h
  | r8 a b c u hu =>
    simpa only [M6.PA.ActualArithmeticGraph.eval_standard,rho8_exact,
      ← Commands.logic_rho8_code] using leaf8 a b c u (Nat.eq_or_lt_of_le hu)
  | gate a b c ha hb =>
    simpa only [M6.PA.ActualArithmeticGraph.eval_standard,bundle_exact,
      ← Commands.logic_bundle_code] using leafGate a b c ha hb

noncomputable def sentence (a : Nat) : ArithmeticSentence :=
  “∃ code, !verifyGraph ↑(a+1) code”

theorem sentence_sigma (a : Nat) : ℬ[<,ℒₒᵣ].Hierarchy 𝚺 1 (sentence a) := by
  simp [sentence]

theorem sentence_nat {a : Nat} (p : PA196.Logic.Derivation a) :
    Nat↓[ℒₒᵣ] ⊧ sentence a := by
  simp [sentence,models_iff,verify_graph,numeral_eq_natCast,natCast_nat]
  exact ⟨(ofDerivation p).code,(ofDerivation p).accepted.symm⟩

theorem pa_proves_fixed {a : Nat} (p : PA196.Logic.Derivation a) :
    theory ⊢ sentence a :=
  Arithmetic.sigma_one_completeness (sentence_sigma a) (sentence_nat p)

theorem fixed_all_models {a : Nat} (p : PA196.Logic.Derivation a)
    {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* theory] :
    ∃ code : V, verifyValue code = (a : V)+1 := by
  have h := consequence_iff.mp (Theory.Proof.sound (pa_proves_fixed p)) V inferInstance
  simpa [sentence,models_iff,verify_graph,numeral_eq_natCast,eq_comm] using h

#print axioms ofDerivation
#print axioms pa_proves_fixed
#print axioms fixed_all_models
end PA196.Arithmetic.Fixed
