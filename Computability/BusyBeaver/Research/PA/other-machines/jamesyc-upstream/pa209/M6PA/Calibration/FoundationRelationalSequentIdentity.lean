module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentFold
@[expose] public section

/-! The numeric relational-source identity case. NNF negation is transported
by accepted certificates, never asserted equal to native negation. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def classicalCases {a c : V} (p : Certificate (wim a c))
    (q : Certificate (wim (wn a) c)) : Certificate c := by
  let hn : Context [wn c] (wn c) := .assumption (by simp)
  let na : Context [wn c] (wn a) := .mp hn (.closed (contrapose p))
  let hc : Context [wn c] c := .mp na (.closed q)
  exact (hc.deduction.empty).mp (Dominated.peirce c 1)

theorem sequent_identity_certificate (param s p : V) (hp : IsUFormula language p)
    (hm : p∈s) (hn : Bootstrapping.neg language p∈s) :
    ∃ code, verifyValue code=sequentCode param s+1 := by
  obtain ⟨pos,hpos⟩ := member_certificate param s p hm
  obtain ⟨neg,hneg⟩ := member_certificate param s (Bootstrapping.neg language p) hn
  obtain ⟨forward,backward,hforward,hbackward⟩ := nnf_certificates p param hp
  let negative : Certificate (wim (wn (translate param p)) (sequentCode param s)) :=
    implicationCompose (⟨backward,hbackward⟩ : Certificate
      (wim (wn (translate param p)) (translate param (Bootstrapping.neg language p))))
      ⟨neg,hneg⟩
  let out := classicalCases (⟨pos,hpos⟩ : Certificate
    (wim (translate param p) (sequentCode param s))) negative
  exact ⟨out.code,out.accepted⟩

/-- Weakening consumes an actual accepted source-sequent certificate. -/
theorem sequent_weaken_accepted (param s t code : V) (hst : s⊆t)
    (hc : verifyValue code=sequentCode param s+1) :
    ∃ out, verifyValue out=sequentCode param t+1 := by
  obtain ⟨arrow,ha⟩ := sequent_weakening_certificate param s t hst
  let out := (⟨code,hc⟩ : Certificate (sequentCode param s)).mp ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

#print axioms classicalCases
#print axioms sequent_identity_certificate
#print axioms sequent_weaken_accepted
end M6.PA.RelationalSource.Numeric

