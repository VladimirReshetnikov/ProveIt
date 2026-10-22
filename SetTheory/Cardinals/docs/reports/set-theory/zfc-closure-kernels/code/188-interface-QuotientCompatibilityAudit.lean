import BusyBeaver.ZFC.CPGICQHyp
import BusyBeaver.ZFC.KQ1ZF

/- Proposed definitional compatibility audit. MUST be compiled before deployment.
   Both setoid records have literally the same Eqv relation; the remaining
   fields are proofs. Lean's proof irrelevance is kernel conversion, not an
   additional axiom or a chosen equivalence between quotient domains. -/
namespace SetTheory.BusyBeaver.ZFC.CPGICQHyp
open ProfileModel
universe u
variable {V : Type u} (mem : V → V → Prop) (w : V) (h : ModelsCPGIC mem)

example : QuotientModel.modelSetoid mem w h =
    KQ1Model.modelSetoid mem w (ofCPGIC mem w h) := rfl

example : QuotientModel.Domain mem w h =
    KQ1Model.Domain mem w (ofCPGIC mem w h) := rfl

example (x : V) : QuotientModel.mk mem w h x =
    KQ1Model.mk mem w (ofCPGIC mem w h) x := rfl

example : QuotientModel.quotientMember mem w h =
    KQ1Model.quotientMember mem w (ofCPGIC mem w h) := rfl

/-- Same source relation and same final contradiction predicate, not a new model. -/
theorem consistent (mem : V → V → Prop) (w : V) (h : ModelsCPGIC mem) :
    ¬ BProv ZFax_s [] Form.fBot :=
  KQ1ZF.zf_consistent mem w (ofCPGIC mem w h)

#print axioms consistent
end SetTheory.BusyBeaver.ZFC.CPGICQHyp
