import GowersSzemeredi.Proofs16DenseBohrRefinement
import GowersSzemeredi.Proofs16RelationRankBudget

/-! A failed bounded-relation estimate gives a genuine dense row refinement,
with strict relation growth and explicit costs in all parameters. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Refine the relation domain while retaining the dense rows by affine
recentering. The bound depends on the current fixed-frequency cardinality. -/
theorem dense_relation_refinement {N Q : Nat} [NeZero N] [NeZero Q] [Fact N.Prime]
    {κ : Type*} [Fintype κ] (A : Finset (ZMod N × ZMod N))
    (W F Gamma : Finset (ZMod N)) (L : κ → ZMod N → ZMod N)
    (a : ZMod N) {sigma eta alpha theta : Real} (hsigma : 0 < sigma)
    (hsigmaMax : sigma ≤ 1 / (8 * Real.pi)) (heta : 0 ≤ eta)
    (ha : 0 < alpha) (htheta : 0 < theta) (hQ : 4 ≤ sigma * Q)
    (hW : W ⊆ bohr Gamma (sigma / 4))
    (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (hcard : alpha * N ≤ W.card) (hgeom : tupleRowGeometry A W F L a eta)
    (R : Nat)
    (hpairs : theta * ((bohr Gamma (sigma / 4)).card : Real)^2 ≤
      (boundedBadRelationPairs (fun i : ↥F => (i : ZMod N)) (bohr Gamma sigma)
        L (bohr Gamma (sigma / 4)) R).card) :
    let M : Real := ((2 * R + 1)^(F.card + 2 * Fintype.card κ) : Nat)
    ∃ (S : Finset (ZMod N)) (t : ZMod N) (V F' : Finset (ZMod N)),
      Gamma ⊆ S ∧ S.card ≤ relationRankStep theta M Q Gamma.card ∧
      bohr S sigma ⊆ bohr Gamma sigma ∧ bohr S (sigma / 4) ⊆ bohr Gamma (sigma / 4) ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S sigma) L ∧
      V.Nonempty ∧ V ⊆ bohr S (sigma / 4) ∧
      alpha * ((bohr S (sigma / 4)).card : Real) ≤ V.card ∧
      (alpha / (Q : Real)^S.card) * N ≤ V.card ∧
      F ⊆ F' ∧ F'.card ≤ F.card + Fintype.card κ ∧
      (∀ x ∈ V, t + x ∈ W) ∧ tupleRowGeometry A V F' L (a + t) (eta / 2) := by
  dsimp only
  obtain ⟨S, hGS, hScard, hfull, hquarter, hstrict⟩ :=
    bounded_bad_pair_refinement_rank (fun i : ↥F => (i : ZMod N)) Gamma hsigma hsigmaMax hQ
      L hL R htheta hpairs
  obtain ⟨t, V, F', hVne, hV, hrel, habs, hFF', hFcard, hVW, hgeom'⟩ :=
    dense_affine_bohr_refinement A W F Gamma S L a hsigma.le heta ha hQ hW hquarter hL hcard hgeom
  refine ⟨S, t, V, F', hGS, ?_, hfull, hquarter, hstrict, hVne, hV, hrel, habs,
    hFF', hFcard, hVW, hgeom'⟩
  simpa only [Fintype.card_coe] using hScard

end LeanProofs.GowersSzemeredi
