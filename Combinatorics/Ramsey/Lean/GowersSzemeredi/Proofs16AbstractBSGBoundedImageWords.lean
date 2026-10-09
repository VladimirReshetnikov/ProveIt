import GowersSzemeredi.Proofs16AbstractBSGWordBounds
import GowersSzemeredi.Proofs16BoundedImageWordRadius

/-! The abstract BSG tuple construction with exact endpoint identities,
when its quadruple relation has bounded image in a prime cyclic target.
The output uses the same maps and the same actual representation families.
The weak-transitivity and frequency-structure inputs remain explicit. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

theorem abstract_bsg_bounded_image_words {N ell M : Nat} [NeZero N] [Fact N.Prime]
    (hN : 2 < N) (A : Finset (ZMod N))
    (Q : Nat → ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (hS1 : ∀ a b c d, Q 1 a b c d → Q 1 c d a b)
    (hS2 : ∀ a b c d, Q 4 a b c d → Q 4 b a d c)
    (hS3 : ∀ i a b c d, Q i a b c d → Q i a c b d)
    {c c' K : Real} (hc : 0 < c) (hc' : 0 < c') (hK : 0 < K)
    (hWT : ∀ i j, i + j ≤ 16 → ∀ a b d e, c' * N ≤ (((A ×ˢ A).filter fun p =>
      Q i a b p.1 p.2 ∧ Q j p.1 p.2 d e).card : Real) → Q (i+j) a b d e)
    (hdoub : (((Finset.univ : Finset (ZMod N)) - Finset.univ).card : Real) ≤ K*N)
    (hgood : c*(N : Real)^3 ≤ ∑ d ∈
      (Finset.univ : Finset (ZMod N)) - Finset.univ, (diffGoodCount A (Q 1) d : Real))
    (hcN : 4 ≤ c*N) (k : Nat) (hsmall : c' ≤ absBsgWordTransitivity c K k)
    (Gamma : Finset (ZMod N)) (theta : Fin ell → ZMod N → ZMod N)
    (F : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 < r) (hM : 0 < M)
    (htheta : ∀ i, IsFreimanLinearOn A (theta i))
    (hF : ∀ x ∈ A, IsFreimanLinearOn (freimanFrequencyBohr Gamma theta r x) (F x) ∧ F x 0 = 0)
    (himage : ∀ a b d e, Q 16 a b d e → ColumnQuadImageRelation
      (fun u => Gamma ∪ Finset.univ.image (fun j => theta j u)) F r M a b d e)
    (hMN : M^(2*k+1) < N) :
    ∃ B B' : Finset (ZMod N), B' ⊆ B ∧ B ⊆ A ∧
      absBsgEps c K*N ≤ (B'.card : Real) ∧ 0 < boundedImageWordRadius r M k ∧
      ThresholdRelationRichness B (Q 16) (absBsgWordBeta c K k) (absBsgWordEta c K) ∧
      ∀ a : ZMod N, ∀ as : List (ZMod N), (∀ x ∈ a::as, x ∈ B') → as.length ≤ k →
        thresholdColumnWordDensity (absBsgWordLambda c K) (absBsgWordEta c K) as.length *
          (N : Real)^(3*as.length+2) ≤ (relationWordRepresentations B (Q 16) (a::as)).card ∧
        ∀ w ∈ relationWordRepresentations B (Q 16) (a::as),
          (relationWordEndpointSpectrum
            (fun u => Gamma ∪ Finset.univ.image (fun j => theta j u)) (a::as) w).card ≤
              4*(k+1)*(Gamma.card+ell) ∧
          ∀ y ∈ bohr (relationWordEndpointSpectrum
            (fun u => Gamma ∪ Finset.univ.image (fun j => theta j u)) (a::as) w)
            (boundedImageWordRadius r M k),
            columnAnchorEval (fun x => F x y) (a::as) = columnWordEval (fun x => F x y) w := by
  obtain ⟨B, B', hB'B, hBA, hsize, hrich, hwords⟩ :=
    abstract_bsg_word_system hN A Q hS1 hS2 hS3 hc hc' hK hWT hdoub hgood hcN k hsmall
  refine ⟨B, B', hB'B, hBA, hsize, boundedImageWordRadius_pos hr hM k, hrich, ?_⟩
  intro a as has hlen
  refine ⟨hwords a as has hlen, ?_⟩
  intro w hw
  exact coherent_relation_word_exact_uniform B Gamma theta F (Q 16) hr.le hM
    (fun i => (htheta i).mono hBA) (fun x hx => hF x (hBA hx)) himage hMN
    a as w (fun x hx => hB'B (has x hx)) hw hlen

end LeanProofs.GowersSzemeredi
