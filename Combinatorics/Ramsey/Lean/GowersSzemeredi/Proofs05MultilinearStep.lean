import GowersSzemeredi.Proofs05Multiaffine
import GowersSzemeredi.Proofs05BoxTransport

/-!
# The geometric height step for multilinear partitioning

A prescribed-step coarse partition makes the maximal monomial small. Refine
its index models using the lower-height polynomial, then transport and flatten.
The numerical recurrence and scale estimates are explicit inputs to this step.

`multiaffine_box_height_step` is in `Proofs05MultilinearStepSide`, outside the
final route. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
namespace LeanProofs.GowersSzemeredi

/-- Bound a square-free term throughout a modular index box. -/
theorem diameterAtMost_indexModel_monomial {N k u : Nat} [NeZero N]
    (P : Box N k) (S : Finset (Fin k)) (a : ZMod N)
    (hlen : ∀ i, (P.axis i).length ≤ u) :
    diameterAtMost ((boxIndexModel P).carrier.image fun x => a * ∏ i ∈ S, x i)
      (u ^ S.card * centeredAbs a) := by
  have h := diameterAtMost_multiaffine_monomial (boxIndexSet (boxIndexModel P)) S a
    (fun x hx i _ => (Finset.mem_range.mp (Fintype.mem_piFinset.mp hx i)).le.trans (hlen i))
  rw [Box.carrier_eq_index_image, Finset.image_image]
  simpa [Function.comp_def, boxIndexPoint, boxIndexModel, modInterval] using h

end LeanProofs.GowersSzemeredi
