module
public import M6PA.Theory
public import M6PA.Calibration.NumericPAeqSequentFold
@[expose] public section

/-! Inserting a member into an HFS sequent is certificate-equivalent to a
native disjunction. This is not a syntactic equality of the canonical scans. -/
namespace M6.PA.NumericPAeqFormula.Sequent
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open RelationalSource.Numeric (translate nativeOr orLeft orRight orEliminate)
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem SupportedSet.insert {param s p : V} (hs : SupportedSet param s)
    (hp : SupportedFormulaCovered 0 0 param p) : SupportedSet param (insert p s) := by
  intro q hq
  rcases (show q=p ∨ q∈s from by simpa using hq) with rfl | h
  · exact hp
  · exact hs q h

theorem insert_forward_certificate (native param s p : V) (hs : SupportedSet param s)
    (hp : SupportedFormulaCovered 0 0 param p) :
    ∃ code, verifyValue code = wim (translate native (sequentCode param (insert p s)))
      (nativeOr (translate native (formulaSyntax param p)) (translate native (sequentCode param s)))+1 := by
  apply sequent_eliminate_certificate native param (insert p s) _ (hs.insert hp)
  intro q hq
  have hx : q=p ∨ q∈s := by simpa using hq
  rcases hx with he | hm
  · subst q
    exact ⟨(orLeft (translate native (formulaSyntax param p)) (translate native (sequentCode param s))).code,
      (orLeft (translate native (formulaSyntax param p)) (translate native (sequentCode param s))).accepted⟩
  · obtain ⟨code,hcode⟩ := member_certificate native param s q hs hm
    let out := implicationCompose (⟨code,hcode⟩ : Certificate
      (wim (translate native (formulaSyntax param q)) (translate native (sequentCode param s))))
      (orRight (translate native (formulaSyntax param p)) (translate native (sequentCode param s)))
    exact ⟨out.code,out.accepted⟩

theorem insert_backward_certificate (native param s p : V) (hs : SupportedSet param s)
    (hp : SupportedFormulaCovered 0 0 param p) :
    ∃ code, verifyValue code = wim (nativeOr (translate native (formulaSyntax param p)) (translate native (sequentCode param s)))
      (translate native (sequentCode param (insert p s)))+1 := by
  obtain ⟨left,hl⟩ := member_certificate native param (insert p s) p (hs.insert hp) (by simp)
  have hsub : s ⊆ insert p s := by intro q hq; simp [hq]
  obtain ⟨right,hr⟩ := sequent_weakening_certificate native param s (insert p s) hs (hs.insert hp) hsub
  let out := orEliminate (⟨left,hl⟩ : Certificate
    (wim (translate native (formulaSyntax param p)) (translate native (sequentCode param (insert p s)))))
    (⟨right,hr⟩ : Certificate (wim (translate native (sequentCode param s)) (translate native (sequentCode param (insert p s)))))
  exact ⟨out.code,out.accepted⟩

theorem insert_bicertificates (native param s p : V) (hs : SupportedSet param s)
    (hp : SupportedFormulaCovered 0 0 param p) :
    ∃ forward backward, BiCertificates forward backward (translate native (sequentCode param (insert p s)))
      (nativeOr (translate native (formulaSyntax param p)) (translate native (sequentCode param s))) := by
  obtain ⟨forward,hf⟩ := insert_forward_certificate native param s p hs hp
  obtain ⟨backward,hb⟩ := insert_backward_certificate native param s p hs hp
  exact ⟨forward,backward,hf,hb⟩

/-- A received accepted insert-sequent code produces a genuine accepted
native disjunction code; no host proof or chosen witness compiler is assumed. -/
theorem insert_accepted_disjunction (native param s p code : V) (hs : SupportedSet param s)
    (hp : SupportedFormulaCovered 0 0 param p)
    (h : verifyValue code=translate native (sequentCode param (insert p s))+1) :
    ∃ out, verifyValue out=nativeOr (translate native (formulaSyntax param p)) (translate native (sequentCode param s))+1 := by
  obtain ⟨arrow,ha⟩ := insert_forward_certificate native param s p hs hp
  let out := (⟨code,h⟩ : Certificate (translate native (sequentCode param (insert p s)))).mp ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

#print axioms SupportedSet.insert
#print axioms insert_forward_certificate
#print axioms insert_backward_certificate
#print axioms insert_bicertificates
#print axioms insert_accepted_disjunction
end M6.PA.NumericPAeqFormula.Sequent

