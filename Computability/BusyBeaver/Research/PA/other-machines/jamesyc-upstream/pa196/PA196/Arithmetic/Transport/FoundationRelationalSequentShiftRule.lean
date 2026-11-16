module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentProofBudget
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Literal shiftRule environment reconstruction, plus positivity of the
unchanged ten-constructor Foundation derivation code. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open FFL.FirstOrder.Arithmetic.Bootstrapping
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem derivation_positive {T : Theory language} [T.Δ₁] {d : V} (h : Derivation T d) : 0<d := by
  rcases Derivation.case_iff.mp h with ⟨hs,hcases⟩
  rcases hcases with ⟨s,p,rfl,_⟩ | ⟨s,rfl,_⟩ | ⟨s,p,q,dp,dq,rfl,_⟩ |
    ⟨s,p,q,dpq,rfl,_⟩ | ⟨s,p,dp,rfl,_⟩ | ⟨s,p,t,dp,rfl,_⟩ |
    ⟨s,dp,rfl,_⟩ | ⟨s,dp,rfl,_⟩ | ⟨s,p,dp,dq,rfl,_⟩ | ⟨s,p,rfl,_⟩ <;>
    simp [axL,verumIntro,andIntro,orIntro,allIntro,exsIntro,wkRule,shiftRule,cutRule,axm]

theorem derivation_member_lt {T : Theory language} [T.Δ₁] {d p : V}
    (h : Derivation T d) (hp : p∈fstIdx d) : p<d :=
  lt_trans (lt_of_mem hp) (fstIdx_lt_of_positive (derivation_positive h))

theorem derivation_budget_coverage {T : Theory language} [T.Δ₁] {d f lo z : V}
    (hd : Derivation T d) (h : ProofEnvironment d f lo z) :
    (∀ p, p∈fstIdx d → FormulaCovered 0 f lo z p) ∧
    (∀ p, p∈fstIdx d → FormulaCovered 0 f (lo+1) z p) := by
  constructor
  · intro p hp
    exact h.coverage (hd.isFormulaSet p hp) (derivation_member_lt hd hp).le
  · intro p hp
    exact h.raised_coverage (hd.isFormulaSet p hp) (derivation_member_lt hd hp)

variable [V↓[ℒₒᵣ] ⊧* theory]

theorem sequent_shift_certificate (s f lo z child : V) (hs : IsFormulaSet language s)
    (hf : 0<len f)
    (hchild : verifyValue child=sequentCode (parameters 0 (sndIdx f) lo z) s+1) :
    ∃ code, verifyValue code=sequentCode (parameters 0 f lo z) (setShift language s)+1 := by
  obtain ⟨code,hcode⟩ := setShift_accepted (parameters 0 (sndIdx f) lo z) s (nth f 0) child hs hchild
  refine ⟨code,?_⟩
  simpa only [prependFree_parameters,free_environment_reconstruct hf] using hcode

/-- A positive actual parent code and its displayed finite budget guarantee
that the free-vector head/tail reconstruction used by shift is legitimate. -/
theorem proofEnvironment_free_positive {d f lo z : V} (hd : 0<d) (h : ProofEnvironment d f lo z) :
    0<len f := lt_of_lt_of_le hd h.2.1

#print axioms derivation_positive
#print axioms derivation_member_lt
#print axioms derivation_budget_coverage
#print axioms sequent_shift_certificate
#print axioms proofEnvironment_free_positive
end PA196.Arithmetic.Transport.RelationalSource.Numeric
