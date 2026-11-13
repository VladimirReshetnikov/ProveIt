module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityTransportProof
public import PA196.Arithmetic.Transport.RelationalPredicateBinaryRequested
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic

namespace PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityTransport
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalPredicateBinary NumericPAeqValueCoherence PA196.Arithmetic.Checker RelationalSource.Numeric
open PA196.Arithmetic.Certificates.Dominated ActualCertificateEquivalence
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]
local notation "L" => RelationalSource.language

theorem laws_requested_certificate (g lo z : V)
    (hc : FormulaCovered 0 g lo z ((symmetry (domain (V:=V)) isoPredicate ⋏ transitivity domain isoPredicate).val)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z)
      ((symmetry (domain (V:=V)) isoPredicate ⋏ transitivity domain isoPredicate).val)+1 := by
  let A := symmetry (domain (V:=V)) isoPredicate
  let B := transitivity (domain (V:=V)) isoPredicate
  change FormulaCovered 0 g lo z (qqAnd A.val B.val) at hc
  have hca := (coverage_and hc).1
  have hcb := (coverage_and hc).2
  have sa : ∃a,verifyValue a=translate (parameters 0 g lo z) A.val+1 := by
    dsimp [A] at hca ⊢
    rw [symmetry_quote] at hca ⊢
    exact RelationalClosedCertificate.isoSymmetry_certificate g lo z hca
  have sb : ∃b,verifyValue b=translate (parameters 0 g lo z) B.val+1 := by
    dsimp [B] at hcb ⊢
    rw [transitivity_quote] at hcb ⊢
    exact RelationalClosedCertificate.isoTransitivity_certificate g lo z hcb
  obtain ⟨a,ha'⟩ := sa
  obtain ⟨b,hb'⟩ := sb
  let ca : Certificate (translate (parameters 0 g lo z) A.val) := ⟨a,ha'⟩
  let cb : Certificate (translate (parameters 0 g lo z) B.val) := ⟨b,hb'⟩
  let out := (Context.andIntro (.closed ca) (.closed cb)).empty
  refine ⟨out.code,?_⟩
  change verifyValue out.code=translate (parameters 0 g lo z) (qqAnd A.val B.val)+1
  rw [translate_and _ _ _ A.isUFormula B.isUFormula,translationAnd_eq]
  exact out.accepted

theorem transport_requested_certificate (P Q U W g lo z : V)
    (hp : IsSemiformula L 1 P) (hq : IsSemiformula L 1 Q)
    (hu : IsSemiformula L 1 U) (hw : IsSemiformula L 1 W)
    (hc : FormulaCovered 0 g lo z (transportCode P Q U W)) :
    ∃code,verifyValue code=translate (parameters 0 g lo z) (transportCode P Q U W)+1 := by
  let p : SF (V:=V) 1 := ⟨P,by simpa using hp⟩
  let q : SF (V:=V) 1 := ⟨Q,by simpa using hq⟩
  let u : SF (V:=V) 1 := ⟨U,by simpa using hu⟩
  let w : SF (V:=V) 1 := ⟨W,by simpa using hw⟩
  have he := transportStatement_val p q u w
  change (transportStatement domain p q u w isoPredicate).val=transportCode P Q U W at he
  rw [←he] at hc ⊢
  exact singleton_requested_certificate (symmetry domain isoPredicate ⋏ transitivity domain isoPredicate)
    (transportStatement domain p q u w isoPredicate) (transportProof domain p q u w isoPredicate)
    g lo z hc laws_requested_certificate
#print axioms laws_requested_certificate
#print axioms transport_requested_certificate
end PA196.Arithmetic.Transport.NumericPAeqFormulaEqualityTransport

