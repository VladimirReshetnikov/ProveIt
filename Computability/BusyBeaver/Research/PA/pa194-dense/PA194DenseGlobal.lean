import PA194Global
import PA194DenseBinding

/-! The exact 202-state parent and the delivered dense 194-state PA195 table
have the same ordinary finite-run halting behavior on every tape. This is not
an internal PRA or iPRA theorem and says nothing by itself about Con(PA). -/
set_option autoImplicit false
namespace PA194LocalQuotient

/-- Exact PA194 quotient, including dense control labels, on all full tapes. -/
theorem parent_dense_halts (p : Int) (t : Int → Bool) :
    PA195GenericTrace.Halts (fullStep parent) AtHalt ⟨74, p, t⟩ ↔
    PA195GenericTrace.Halts (fullStep dense) (fun c => c.state = 194) ⟨0, p, t⟩ := by
  exact (halts_iff_any_tape p t).trans (dense_native_halts p t).symm

#print axioms parent_dense_halts
end PA194LocalQuotient
