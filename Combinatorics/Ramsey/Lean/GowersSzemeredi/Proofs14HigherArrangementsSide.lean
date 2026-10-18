import GowersSzemeredi.Proofs14HigherArrangements

/-! Declarations of `Proofs14HigherArrangements` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma cor147_arrangement_vertex {N k d : Nat}
    (h : Point N k) (p : cor147PairFamily N k d)
    (e : Fin k → Bool) (j : Fin (2 * d)) :
    (cor147ArrangementEquiv N k d (h, p)).vertex e j =
      appendCoordinate
        (AxisCube.vertex
          ((cor147PairEquiv d (cor147Atom N k) p j).1, h) e)
        (cor147PairEquiv d (cor147Atom N k) p j).2 := rfl

end LeanProofs.GowersSzemeredi
