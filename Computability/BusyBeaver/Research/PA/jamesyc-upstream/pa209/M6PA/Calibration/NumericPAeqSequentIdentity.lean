module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentInsert
public import M6PA.Calibration.NumericPAeqFormulaSupportedNegation
public import M6PA.Calibration.FoundationRelationalSequentIdentity
@[expose] public section

/-! Identity and truth for interpreted PAeq HFS sequents. Source NNF negation
is related to native negation by an accepted certificate, never identified
syntactically with native implication-to-bottom. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint
open RelationalSource.Numeric (translate classicalCases translate_verum)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem interpreted_negation_certificates (native param p : V)
    (hp : SupportedFormulaCovered 0 0 param p) :
    ∃ forward backward, BiCertificates forward backward
      (translate native (formulaSyntax param (neg Presentation.language p)))
      (wn (translate native (formulaSyntax param p))) := by
  rw [formulaSyntax_supported_neg hp]
  exact nnf_certificates _ native (formulaSyntax_supported_isSemiformula hp).isUFormula

theorem sequent_identity_certificate (native param s p : V) (hs : SupportedSet param s)
    (hm : p∈s) (hn : neg Presentation.language p∈s) :
    ∃ code, verifyValue code=translate native (sequentCode param s)+1 := by
  obtain ⟨positive,hpositive⟩ := member_certificate native param s p hs hm
  obtain ⟨negative,hnegative⟩ := member_certificate native param s (neg Presentation.language p) hs hn
  obtain ⟨forward,backward,hforward,hbackward⟩ := interpreted_negation_certificates native param p (hs p hm)
  let toS := implicationCompose (⟨backward,hbackward⟩ : Certificate
    (wim (wn (translate native (formulaSyntax param p)))
      (translate native (formulaSyntax param (neg Presentation.language p))))) ⟨negative,hnegative⟩
  let out := classicalCases (⟨positive,hpositive⟩ : Certificate
    (wim (translate native (formulaSyntax param p)) (translate native (sequentCode param s)))) toS
  exact ⟨out.code,out.accepted⟩

theorem sequent_verum_certificate (native param s : V) (hs : SupportedSet param s)
    (hm : qqVerum∈s) :
    ∃ code, verifyValue code=translate native (sequentCode param s)+1 := by
  obtain ⟨arrow,ha⟩ := member_certificate native param s qqVerum hs hm
  rw [formulaSyntax_verum,translate_verum] at ha
  let out := (truthCertificate (V:=V)).mp ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

#print axioms interpreted_negation_certificates
#print axioms sequent_identity_certificate
#print axioms sequent_verum_certificate
end M6.PA.NumericPAeqFormula.Sequent

