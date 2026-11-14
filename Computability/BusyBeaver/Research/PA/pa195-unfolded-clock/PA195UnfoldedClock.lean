import PA195ZipRun
import PA195Global

/-! Composition of the exact PA195 bounded-code standard semantics with
202-to-195 quotient halting equivalence. This is not a PRA/iPRA theorem. -/
set_option autoImplicit false
namespace PA195UnfoldedClock
open List.Vector
open PA195LocalQuotient PA195ZipBridge

theorem bounded_code_iff_unfolded :
    (∃ n, DiophantineConsistency.PRAFiniteFunctionCodes.eval PA195Bounded.boundedCode
      (n ::ᵥ List.Vector.nil) = 1) ↔
    PA195GenericTrace.Halts (fullStep parent) AtHalt ⟨74, 0, fun _ => false⟩ := by
  rw [bounded_code_iff_full]
  change PA195GenericTrace.Halts (fullStep dense) (fun c => c.state = 195)
    ⟨0, 0, fun _ => false⟩ ↔ _
  rw [dense_native_halts]
  change PA195GenericTrace.Halts (fullStep folded) AtHalt ⟨74, 0, fun _ => false⟩ ↔ _
  exact (halts_iff_any_tape 0 (fun _ => false)).symm

#print axioms bounded_code_iff_unfolded
end PA195UnfoldedClock
