import GowersSzemeredi.Proofs16PolyPieceTwoData
import GowersSzemeredi.Proofs16Lemma5Side
import GowersSzemeredi.Proofs16PolyPieceTwoSide

/-! Declarations of `Proofs16PolyPieceTwoData` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace LeanProofs.GowersSzemeredi

section
open BaseCase

/-- **A dimension-two piece with its Freiman data, in the original frame.** -/
theorem section16_poly_piece_two_data
    {theta gamma : Real} (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    {N : Nat} [NeZero N] [Fact N.Prime] (Gamma : Finset (Point N 2 × ZMod N))
    (B : Finset (Point N 2)) (phi : Point N 2 → ZMod N)
    (hBG : partialGraph B phi ⊆ Gamma)
    (hBarr : section16ThetaOne theta gamma 1 * (N : Real) ^ (17 * 1 + 15) ≤
        generalArrangementCount 8 B ∧
      (1 - (2 : Real) ^ (-(44 : Real))) * generalArrangementCount 8 B ≤
        respectedGeneralArrangementCount 8 B phi)
    (hprodB : HasProductProperty B phi gamma) :
    Nonempty (PolyPieceTwoData Gamma (section16Zeta theta gamma 1)
      (5 * polyPieceBudget theta gamma) (polyPieceSpecCount theta gamma)
      (polyPieceFaceCount theta gamma) (polyPieceFaceCount theta gamma)) :=
  have hp := lemma_16_5_with_printed_hyps 1 ht ht1 hg hg1
  section16_poly_piece_two_data_with hp.1 hp.2.1 hp.2.2 (by unfold section16Zeta; positivity)
    hg hg1 Gamma B phi hBG hBarr hprodB

end

end LeanProofs.GowersSzemeredi
