module
public import M6PA.Theory
public import M6PA.Calibration.RelationalSourceND
public import M6PA.Calibration.ActualFixedCertificateExistence
public import M6PA.Calibration.FoundationRelationalCodeAgreement
public import M6PA.Calibration.FoundationRelationalSequentFixedGraph
public import M6PA.Calibration.FoundationRelationalSequentClosedRelocation
@[expose] public section

/-! A fixed CLOSED host relational theorem supplies accepted certificates at
all covered model-valued native label/allocator/reserve parameters. The host
proof is explicit; this is not universal internal completeness. -/
namespace M6.PA.RelationalClosedCertificate
open FFL FFL.FirstOrder RelationalSource ND
open FFL.FirstOrder.Arithmetic FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCheckerBlueprint ActualCertificateConstructors
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem closed_shift (q : Form) (hq : q.freeVariables=∅) : Rewriting.shift q=q := by
  apply Semiformula.rew_eq_self_of
  · intro i; exact Fin.elim0 i
  · intro i hi; simp [Semiformula.FVar?,hq] at hi

theorem closed_quote_shift (q : Form) (hq : q.freeVariables=∅) :
    shift language (⌜q⌝ : V)=(⌜q⌝ : V) := by
  rw [← Semiformula.quote_shift,closed_shift q hq]

theorem seed_translate (q : Form) (hq : q.freeVariables=∅) (reserve b f : Nat) :
    Numeric.translate (Numeric.parameters b f 1 reserve) (⌜q⌝ : Nat)=code q (fun _=>0) 1 reserve := by
  rw [Numeric.translate_quote]
  unfold code
  apply congrArg (NativeCalculus.ActualBasis.relationalCode reserve)
  apply Numeric.toNamed_agree
  · intro i; exact Fin.elim0 i
  · intro i hi; simp [Semiformula.FVar?,hq] at hi

theorem seed_translate_models (q : Form) (hq : q.freeVariables=∅) (reserve : Nat) :
    Numeric.translate (Numeric.parameters (0:V) 0 1 reserve) (⌜q⌝ : V)=(code q (fun _=>0) 1 reserve:V) := by
  rw [← Semiformula.coe_quote_eq_quote]
  have he := Numeric.translate_fixed_parameters_all_models (V:=V) 0 0 1 reserve (⌜q⌝ : Nat)
  simpa only [Nat.cast_zero,Nat.cast_one,seed_translate q hq] using he

theorem seed_coverage (q : Form) (reserve : Nat) (hz : 1+Encodable.encode q≤reserve) :
    Numeric.FormulaCovered (0:V) (Numeric.zeroEnvironment (⌜q⌝ : V)) 1 reserve (⌜q⌝ : V) := by
  have hb : (1:V)+(⌜q⌝ : V)≤(reserve:V) := by
    simpa [Semiformula.quote_eq_encode] using
      (show ((1+Encodable.encode q):V)≤(reserve:V) from by exact_mod_cast hz)
  have he := Numeric.zeroEnvironment_properties (V:=V) (⌜q⌝ : V)
  refine ⟨⟨⟨by simp,?_,?_,?_⟩,hb⟩,?_,he.1.ge⟩
  · exact le_trans (by simp) hb
  · intro i hi; simp at hi
  · intro i hi
    rw [he.1] at hi
    rw [he.2 i hi]
    simp
  · simpa using Semiformula.quote_isSemiformula (V:=V) q

theorem relocated_certificate (q : Form) (hq : q.freeVariables=∅) (reserve : Nat)
    (hz : 1+Encodable.encode q≤reserve)
    (proof : NativeCalculus.ActualBasis.Proof (code q (fun _=>0) 1 reserve))
    (f lo z : V) (h : Numeric.FormulaCovered 0 f lo z (⌜q⌝ : V)) :
    ∃ cert : V, verifyValue cert=Numeric.translate (Numeric.parameters 0 f lo z) (⌜q⌝ : V)+1 := by
  have hclosed := closed_quote_shift (V:=V) q hq
  have hcal : Numeric.translate (Numeric.parameters 0 (Numeric.zeroEnvironment (⌜q⌝ : V)) 1 reserve) (⌜q⌝ : V)=
      (code q (fun _=>0) 1 reserve:V) := by
    rw [← Numeric.translate_closed_free_environments (⌜q⌝ : V) 0 0 (Numeric.zeroEnvironment (⌜q⌝ : V)) 1 reserve
      (Semiformula.quote_isSemiformula (V:=V) q).isUFormula hclosed]
    exact seed_translate_models q hq reserve
  obtain ⟨seed,hs⟩ := ActualFixedCertificateExistence.fixed_all_models (V:=V) proof
  obtain ⟨forward,backward,hforward,hbackward⟩ := Numeric.closed_formula_parameter_certificates
    (⌜q⌝ : V) (Numeric.zeroEnvironment (⌜q⌝ : V)) 1 reserve f lo z hclosed (seed_coverage q reserve hz) h
  have hs' : verifyValue seed=Numeric.translate
      (Numeric.parameters 0 (Numeric.zeroEnvironment (⌜q⌝ : V)) 1 reserve) (⌜q⌝ : V)+1 := by
    rw [hcal]; exact hs
  exact ⟨mpCertificate (Numeric.translate (Numeric.parameters 0 f lo z) (⌜q⌝ : V)) seed forward,
    verify_mp _ _ _ _ hs' hforward⟩

#print axioms closed_shift
#print axioms closed_quote_shift
#print axioms seed_translate
#print axioms seed_translate_models
#print axioms seed_coverage
#print axioms relocated_certificate
end M6.PA.RelationalClosedCertificate

