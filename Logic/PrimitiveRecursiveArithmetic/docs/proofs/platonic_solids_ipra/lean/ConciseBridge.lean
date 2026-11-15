import ConciseIPRA.NativeBiInterpretation

/-!
Integration adapter for the ProveIt checkout at
2811f73af20330d04bf3dae8428f87f7efa6580d.

SOURCE-REVIEWED BUT UNCOMPILED in the production environment.
This adapter does not construct the classification derivation. Its hypothesis
is explicitly that the derivation has already been constructed. It demonstrates
the exact final interface to the existing native scalar calculus.
-/

namespace PlatonicIPRA

open LeanProofs.ConciseIPRA

theorem transportVerifiedTheorem
    (φ : Fm PTm 0) (h : Prf PRAAx [] φ) :
    NPrf [] (NFm.ofPRA φ) := by
  simpa using (pra_iff_native (Γ := []) (φ := φ)).mp h

end PlatonicIPRA
