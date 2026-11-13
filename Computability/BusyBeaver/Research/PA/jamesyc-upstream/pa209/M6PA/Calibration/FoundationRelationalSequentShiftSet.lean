module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentShift
public import Foundation.FirstOrder.Arithmetic.Bootstrapping.Syntax.Proof.Basic
@[expose] public section

/-! The actual HFS setShift image is certificate-equivalent under the matching
free-environment change. Numeric scan order may change, so equality is not claimed. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

theorem setShift_forward_certificate (param s x : V)
    (hs : ∀ p, p∈s → IsUFormula language p) :
    ∃ code, verifyValue code=wim (sequentCode (prependFree x param) (setShift language s))
      (sequentCode param s)+1 := by
  apply sequent_eliminate_certificate
  intro q hq
  obtain ⟨p,hp,rfl⟩ := mem_setShift_iff.mp hq
  rw [translate_shift p param x (hs p hp)]
  exact member_certificate param s p hp

theorem setShift_backward_certificate (param s x : V)
    (hs : ∀ p, p∈s → IsUFormula language p) :
    ∃ code, verifyValue code=wim (sequentCode param s)
      (sequentCode (prependFree x param) (setShift language s))+1 := by
  apply sequent_eliminate_certificate
  intro p hp
  obtain ⟨code,hcode⟩ := member_certificate (prependFree x param) (setShift language s)
    (Bootstrapping.shift language p) (shift_mem_setShift hp)
  rw [translate_shift p param x (hs p hp)] at hcode
  exact ⟨code,hcode⟩

theorem setShift_bicertificates (param s x : V)
    (hs : ∀ p, p∈s → IsUFormula language p) :
    ∃ forward backward, BiCertificates forward backward
      (sequentCode (prependFree x param) (setShift language s)) (sequentCode param s) := by
  obtain ⟨forward,hf⟩ := setShift_forward_certificate param s x hs
  obtain ⟨backward,hb⟩ := setShift_backward_certificate param s x hs
  exact ⟨forward,backward,hf,hb⟩

/-- Matches actual Foundation formula-set well-formedness, while retaining
explicitly different parameter vectors on the two sides. -/
theorem setShift_formulaSet_bicertificates (param s x : V) (hs : IsFormulaSet language s) :
    ∃ forward backward, BiCertificates forward backward
      (sequentCode (prependFree x param) (setShift language s)) (sequentCode param s) := by
  apply setShift_bicertificates
  intro p hp
  exact (hs p hp).isUFormula

theorem setShift_accepted (param s x code : V) (hs : IsFormulaSet language s)
    (h : verifyValue code=sequentCode param s+1) :
    ∃ out, verifyValue out=sequentCode (prependFree x param) (setShift language s)+1 := by
  obtain ⟨forward,backward,hf,hb⟩ := setShift_formulaSet_bicertificates param s x hs
  let out := (⟨code,h⟩ : Certificate (sequentCode param s)).mp ⟨backward,hb⟩
  exact ⟨out.code,out.accepted⟩

#print axioms setShift_forward_certificate
#print axioms setShift_backward_certificate
#print axioms setShift_bicertificates
#print axioms setShift_formulaSet_bicertificates
#print axioms setShift_accepted
end M6.PA.RelationalSource.Numeric

