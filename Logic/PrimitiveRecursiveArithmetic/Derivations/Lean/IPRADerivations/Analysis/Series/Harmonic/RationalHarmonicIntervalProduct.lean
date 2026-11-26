import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicInterval
import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding
import IPRADerivations.Analysis.Names.GaussianNameArithmetic
import IPRADerivations.Analysis.RationalArithmetic.RationalGaussianRealPart

/-!
# Genuine finite harmonic rectangles for a product of positive fractions

The actual interval at ac/bd telescopes through the two actual intervals
at a/b and c/d after their meshes are multiplied by c and b. A common
computed factorial denominator proves literal normalized code equality.
The already proved finite refinement bounds give the actual 2/Q product
error. This is a finite precursor to a logarithm product law.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalHarmonicIntervalProduct

open_ipra
open RationalHarmonicInterval (interval common numerator horizon at_common common_value common_canonical)
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open Products (fact)
open GaussianRationalHorner (qadd)
open RationalGaussianEmbedding (embed)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def commonHorizon (a b c d Q : PTm n) : PTm n := horizon (a*c) (b*d) Q+horizon a b (c*Q)+horizon c d (b*Q)
ipra_subst commonHorizon

theorem common_product (a b c d Q L : PTm n) : Γ ⊢[PRAAx]
    common (a*c) (b*d) Q L ≐ RationalArithmetic.add (common a b (c*Q) L) (common c d (b*Q) L) := by
  let F := fact L
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have r := RationalRepresentations.represents_add _ _ _ _ _ _ (common_value (Γ := Γ) a b (c*Q) L) (common_value c d (b*Q) L)
  apply RationalFiniteSum.canonical_equal _ _ _ _ F (F*F)
    (common_canonical (a*c) (b*d) Q L) (RationalArithmetic.add_guard _ _)
    (common_value (a*c) (b*d) Q L) r hF (RationalAlgebra.positive_product hF hF)
  have e1 := natEq (congrAp2 (sumF hB) (by ipra_ring : Γ ⊢[PRAAx] (c*Q)*a ≐ Q*(a*c)) (.eqRefl F))
  have e2 := natEq (congrAp2 (sumF hB) (by ipra_ring : Γ ⊢[PRAAx] (c*Q)*b ≐ (b*Q)*c) (.eqRefl F))
  have e3 := natEq (congrAp2 (sumF hB) (by ipra_ring : Γ ⊢[PRAAx] (b*Q)*d ≐ Q*(b*d)) (.eqRefl F))
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_add,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  unfold F at e1 e2 e3
  rw [e1,e2,e3]
  ring

/-- Literal equality of the original independently normalized finite
intervals, with no positivity guards needed for the exact telescope. -/
theorem exact_refined_product (a b c d Q : PTm n) : Γ ⊢[PRAAx]
    interval (a*c) (b*d) Q ≐ RationalArithmetic.add (interval a b (c*Q)) (interval c d (b*Q)) := by
  let L := commonHorizon a b c d Q
  have h0 : Γ ⊢[PRAAx] le (horizon (a*c) (b*d) Q) L := le_trans (le_add_right _ _) (le_add_right _ _)
  have h1 : Γ ⊢[PRAAx] le (horizon a b (c*Q)) L := le_trans (le_add_left _ _) (le_add_right _ _)
  have h2 : Γ ⊢[PRAAx] le (horizon c d (b*Q)) L := le_add_left _ _
  exact (at_common _ _ _ L h0).eqSymm.eqTrans ((common_product a b c d Q L).eqTrans
    (RationalAlgebra.add_congr (at_common _ _ _ L h1) (at_common _ _ _ L h2)))

theorem finite_product_error (a b c d Q : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) (hQ : Γ ⊢[PRAAx] le one Q) : Γ ⊢[PRAAx]
    distanceBounded (embed (interval (a*c) (b*d) Q)) (qadd (embed (interval a b Q)) (embed (interval c d Q))) two Q := by
  have left := RationalGaussianNameEmbedding.distance_from_radius _ _ one Q hQ (RationalHarmonicInterval.refinement a b Q c ha hb hQ hc)
  have right := RationalGaussianNameEmbedding.distance_from_radius _ _ one Q hQ (RationalHarmonicInterval.refinement c d Q b hc hd hQ hb)
  have sum := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hQ left right
  have e := (RationalGaussianRealPart.embed_congr (exact_refined_product (Γ := Γ) a b c d Q)).eqTrans (RationalGaussianEmbedding.embed_add _ _)
  exact GaussianRationalDistanceOrder.distance_congr e.eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _) sum

theorem actual_finite_harmonic_product_telescope_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (interval (var 0*var 2) (var 1*var 3) (var 4) ≐
      RationalArithmetic.add (interval (var 0) (var 1) (var 2*var 4)) (interval (var 2) (var 3) (var 1*var 4))) :=
  closeUniv 5 (exact_refined_product _ _ _ _ _)
theorem actual_finite_harmonic_product_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 0) ⋏ (le one (var 1) ⋏ (le one (var 2) ⋏ (le one (var 3) ⋏ le one (var 4))))) ⟶
      distanceBounded (embed (interval (var 0*var 2) (var 1*var 3) (var 4)))
        (qadd (embed (interval (var 0) (var 1) (var 4))) (embed (interval (var 2) (var 3) (var 4)))) two (var 4)) :=
  closeUniv 5 (.impI (finite_product_error _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.RationalHarmonicIntervalProduct
