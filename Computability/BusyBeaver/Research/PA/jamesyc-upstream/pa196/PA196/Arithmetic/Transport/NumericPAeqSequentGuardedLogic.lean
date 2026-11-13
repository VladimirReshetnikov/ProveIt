module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.NumericPAeqSequentIdentity
public import PA196.Arithmetic.Transport.FoundationRelationalSequentPropositional
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.NumericPAeqFormula
open M6.PA.NumericPAeqFormula.Sequent


/-! Finite native recipes retain the guard as an actual Context assumption.
No unguarded accepted proof is inferred from a guarded implication. -/
namespace PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence
open RelationalSource.Numeric (nativeOr resolveDisjunction)
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def contextConjunctionSequent {Γ : List V} {a b c : V}
    (pa : Context Γ (nativeOr a c)) (pb : Context Γ (nativeOr b c))
    (h : Certificate (wim (wa a b) c)) : Context Γ c := by
  let nc : Context (wn c::Γ) (wn c) := .assumption (by simp)
  let ca := resolveDisjunction (pa.up (wn c)) nc
  let cb := resolveDisjunction (pb.up (wn c)) nc
  let cc : Context (wn c::Γ) c := .mp (ca.andIntro cb) (.closed h)
  exact (Context.mp cc nc).deduction.dne

noncomputable def guardedConjunctionSequent {g a b c : V}
    (pa : Certificate (wim g (nativeOr a c))) (pb : Certificate (wim g (nativeOr b c)))
    (h : Certificate (wim (wa a b) c)) : Certificate (wim g c) := by
  let hg : Context [g] g := .assumption (by simp)
  exact (contextConjunctionSequent (.mp hg (.closed pa)) (.mp hg (.closed pb)) h).deduction.empty

noncomputable def contextCutSequent {Γ : List V} {a na c : V}
    (pa : Context Γ (nativeOr a c)) (pn : Context Γ (nativeOr na c))
    (h : Certificate (wim na (wn a))) : Context Γ c := by
  let nc : Context (wn c::Γ) (wn c) := .assumption (by simp)
  let ca := resolveDisjunction (pa.up (wn c)) nc
  let cn : Context (wn c::Γ) (wn a) := .mp (resolveDisjunction (pn.up (wn c)) nc) (.closed h)
  exact (Context.mp ca cn).deduction.dne

noncomputable def guardedCutSequent {g a na c : V}
    (pa : Certificate (wim g (nativeOr a c))) (pn : Certificate (wim g (nativeOr na c)))
    (h : Certificate (wim na (wn a))) : Certificate (wim g c) := by
  let hg : Context [g] g := .assumption (by simp)
  exact (contextCutSequent (.mp hg (.closed pa)) (.mp hg (.closed pn)) h).deduction.empty

#print axioms contextConjunctionSequent
#print axioms guardedConjunctionSequent
#print axioms contextCutSequent
#print axioms guardedCutSequent
end PA196.Arithmetic.Transport.NumericPAeqFormula.Sequent

