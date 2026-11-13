module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentIdentity
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Inserting a member into an HFS sequent is certificate-equivalent to a
native disjunction. This is not a syntactic equality of the canonical scans. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem insert_forward_certificate (param s p : V) :
    ∃ code, verifyValue code = wim (sequentCode param (insert p s))
      (nativeOr (translate param p) (sequentCode param s))+1 := by
  apply sequent_eliminate_certificate
  intro q hq
  have hx : q=p ∨ q∈s := by simpa using hq
  rcases hx with he | hm
  · subst q
    exact ⟨(orLeft (translate param p) (sequentCode param s)).code,
      (orLeft (translate param p) (sequentCode param s)).accepted⟩
  · obtain ⟨code,hcode⟩ := member_certificate param s q hm
    let out := implicationCompose (⟨code,hcode⟩ : Certificate
      (wim (translate param q) (sequentCode param s)))
      (orRight (translate param p) (sequentCode param s))
    exact ⟨out.code,out.accepted⟩

theorem insert_backward_certificate (param s p : V) :
    ∃ code, verifyValue code = wim (nativeOr (translate param p) (sequentCode param s))
      (sequentCode param (insert p s))+1 := by
  obtain ⟨left,hl⟩ := member_certificate param (insert p s) p (by simp)
  have hs : s ⊆ insert p s := by intro q hq; simp [hq]
  obtain ⟨right,hr⟩ := sequent_weakening_certificate param s (insert p s) hs
  let out := orEliminate (⟨left,hl⟩ : Certificate
    (wim (translate param p) (sequentCode param (insert p s))))
    (⟨right,hr⟩ : Certificate (wim (sequentCode param s) (sequentCode param (insert p s))))
  exact ⟨out.code,out.accepted⟩

theorem insert_bicertificates (param s p : V) :
    ∃ forward backward, BiCertificates forward backward (sequentCode param (insert p s))
      (nativeOr (translate param p) (sequentCode param s)) := by
  obtain ⟨forward,hf⟩ := insert_forward_certificate param s p
  obtain ⟨backward,hb⟩ := insert_backward_certificate param s p
  exact ⟨forward,backward,hf,hb⟩

/-- A received accepted insert-sequent code produces a genuine accepted
native disjunction code; no host proof or chosen witness compiler is assumed. -/
theorem insert_accepted_disjunction (param s p code : V)
    (h : verifyValue code=sequentCode param (insert p s)+1) :
    ∃ out, verifyValue out=nativeOr (translate param p) (sequentCode param s)+1 := by
  obtain ⟨arrow,ha⟩ := insert_forward_certificate param s p
  let out := (⟨code,h⟩ : Certificate (sequentCode param (insert p s))).mp ⟨arrow,ha⟩
  exact ⟨out.code,out.accepted⟩

#print axioms insert_forward_certificate
#print axioms insert_backward_certificate
#print axioms insert_bicertificates
#print axioms insert_accepted_disjunction
end PA196.Arithmetic.Transport.RelationalSource.Numeric

