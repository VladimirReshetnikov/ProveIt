import GowersSzemeredi.Proofs16AbstractBSGBoundedImageWords
import GowersSzemeredi.Proofs16BoundedImageQuadSymmetry

/-! BSG applied to the concrete bounded-image family of local maps. Its
symmetries and full-group doubling are proved automatically. Quantitative
weak transitivity and the original-column structure are still inputs. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- The concrete family with level-`16` image bound `E^16` gives a dense
exact word system. Every fixed word length has polynomial radius loss. -/
theorem bounded_image_quad_word_system {N ell : Nat} [NeZero N] [Fact N.Prime]
    (hN : 2 < N) (A Gamma : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 < r) {E : Nat} (hE : 0 < E)
    (htheta : ∀ i, IsFreimanLinearOn A (theta i))
    (hF : ∀ x ∈ A, IsFreimanLinearOn (freimanFrequencyBohr Gamma theta r x) (F x) ∧ F x 0 = 0)
    {c c' : Real} (hc : 0 < c) (hc' : 0 < c') (hcN : 4 ≤ c*N) (k : Nat) :
    let T := fun u => Gamma ∪ Finset.univ.image (fun j => theta j u)
    let Q := boundedImageQuadFamily T F r E
    (∀ i j, i+j ≤ 16 → ∀ a b d e, c'*N ≤ (((A ×ˢ A).filter fun p =>
      Q i a b p.1 p.2 ∧ Q j p.1 p.2 d e).card : Real) → Q (i+j) a b d e) →
    c*(N : Real)^3 ≤ ∑ d ∈ (Finset.univ : Finset (ZMod N))-Finset.univ,
      (diffGoodCount A (Q 1) d : Real) →
    c' ≤ absBsgWordTransitivity c 1 k → (E^16)^(2*k+1) < N →
    ∃ B B' : Finset (ZMod N), B' ⊆ B ∧ B ⊆ A ∧
      absBsgEps c 1*N ≤ (B'.card : Real) ∧ 0 < boundedImageWordRadius r (E^16) k ∧
      ThresholdRelationRichness B (Q 16) (absBsgWordBeta c 1 k) (absBsgWordEta c 1) ∧
      ∀ a : ZMod N, ∀ as : List (ZMod N), (∀ x ∈ a::as, x ∈ B') → as.length ≤ k →
        thresholdColumnWordDensity (absBsgWordLambda c 1) (absBsgWordEta c 1) as.length *
          (N : Real)^(3*as.length+2) ≤ (relationWordRepresentations B (Q 16) (a::as)).card ∧
        ∀ w ∈ relationWordRepresentations B (Q 16) (a::as),
          (relationWordEndpointSpectrum
            (fun u => Gamma ∪ Finset.univ.image (fun j => theta j u)) (a::as) w).card ≤
              4*(k+1)*(Gamma.card+ell) ∧
          ∀ y ∈ bohr (relationWordEndpointSpectrum
            (fun u => Gamma ∪ Finset.univ.image (fun j => theta j u)) (a::as) w)
            (boundedImageWordRadius r (E^16) k),
            columnAnchorEval (fun x => F x y) (a::as) = columnWordEval (fun x => F x y) w := by
  dsimp only
  intro hWT hgood hsmall hEN
  let T := fun u => Gamma ∪ Finset.univ.image (fun j => theta j u)
  let Q := boundedImageQuadFamily T F r E
  have hsym := boundedImageQuadFamily_symmetries T F r E
  have hdoub : (((Finset.univ : Finset (ZMod N))-Finset.univ).card : Real) ≤ (1 : Real)*N := by
    simp
  exact abstract_bsg_bounded_image_words hN A Q (hsym.1 1) (hsym.2.1 4) hsym.2.2
    hc hc' (by norm_num) hWT hdoub hgood hcN k hsmall Gamma theta F hr (pow_pos hE 16)
    htheta hF (fun _ _ _ _ h => h) hEN

end LeanProofs.GowersSzemeredi
