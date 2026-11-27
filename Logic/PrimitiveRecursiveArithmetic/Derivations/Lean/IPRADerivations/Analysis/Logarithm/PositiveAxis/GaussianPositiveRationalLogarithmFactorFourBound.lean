import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmProperness
import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicIntervalVariation
import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmDyadicTail

/-!
# A late bound for the original logarithm between one quarter and four

The actual harmonic mesh is even. On one factorial scale the four
right-rectangle increments at 2m, 3m, 4m, 6m and 8m sum to at most
5/3. Both orientations of the original interval obey this bound.
The original logarithm-to-interval rate leaves a radius of two after
five bits of precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmFactorFourBound

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianPositiveRationalLogarithm (sample source)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded)
open RationalGaussianEmbedding (embed native)
open RationalHarmonicInterval (horizon interval numerator)
open Products (fact)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "absGap" => Probability.Variance.ad

private theorem step (c m F : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (c*S ((c+one)*m) F) (c*S (c*m) F+F) := by
  let v := c*m
  let u := v+m
  have diff : Γ ⊢[PRAAx] monus u v ≐ m := add_monus' m v
  have value : Γ ⊢[PRAAx] S u F ≐ S ((c+one)*m) F :=
    congrAp2 (sumF hB) (by dsimp [u,v]; ipra_ring) (.eqRefl _)
  have native := RationalHarmonicIntervalVariation.harmonic_increment (Γ := Γ) u v F (le_add_right v m)
  have changed := le_congr (congrMul (.eqRefl _) value) (congrAdd (.eqRefl _) (congrMul diff (.eqRefl _))) native
  apply RationalValueBounds.positive_cancel hm
  exact le_congr (by dsimp [v]; ipra_ring) (by dsimp [v]; ipra_ring) changed

private theorem rectangles (m F : PTm n) (hm : Γ ⊢[PRAAx] le one m) :
    Γ ⊢[PRAAx] le (num 3*S (num 8*m) F) (num 3*S (two*m) F+num 5*F) := by
  have e (a b : PTm n) (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] S a F ≐ S b F :=
    congrAp2 (sumF hB) h (.eqRefl _)
  have oneStep : Γ ⊢[PRAAx] le (two*S (num 3*m) F) (two*S (two*m) F+F) :=
    le_congr (congrMul (.eqRefl _) (e _ _ (by ipra_ring))) (.eqRefl _) (step two m F hm)
  have twoStep : Γ ⊢[PRAAx] le (num 3*S (num 4*m) F) (num 3*S (num 3*m) F+F) :=
    le_congr (congrMul (.eqRefl _) (e _ _ (by ipra_ring))) (.eqRefl _) (step (num 3) m F hm)
  have ht := positive_product (Γ := Γ) two m (le_succ_self one) hm
  have threeStep : Γ ⊢[PRAAx] le (two*S (num 6*m) F) (two*S (num 4*m) F+F) :=
    le_congr (congrMul (.eqRefl _) (e _ _ (by ipra_ring)))
      (congrAdd (congrMul (.eqRefl _) (e _ _ (by ipra_ring))) (.eqRefl _)) (step two (two*m) F ht)
  have fourStep : Γ ⊢[PRAAx] le (num 3*S (num 8*m) F) (num 3*S (num 6*m) F+F) :=
    le_congr (congrMul (.eqRefl _) (e _ _ (by ipra_ring)))
      (congrAdd (congrMul (.eqRefl _) (e _ _ (by ipra_ring))) (.eqRefl _)) (step (num 3) (two*m) F ht)
  apply RationalValueBounds.positive_cancel (c := two) (le_succ_self one)
  ipra_le 3*sl oneStep+2*sl twoStep+3*sl threeStep+2*sl fourStep

private theorem mesh_interval_upper (p a b F : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] le a (num 4*b)) :
    Γ ⊢[PRAAx] le (num 3*S (GammaEulerConstantName.mesh p*a) F)
      (num 3*S (GammaEulerConstantName.mesh p*b) F+num 5*F) := by
  let Q := GammaEulerConstantName.mesh p
  let m := (two*unit p)*b
  have hm := positive_product _ _ (positive_product _ _ (le_succ_self one) (unit_positive p)) hb
  have range : Γ ⊢[PRAAx] le (Q*a) (num 8*m) :=
    le_congr (.eqRefl _) (by dsimp [Q,m,GammaEulerConstantName.mesh, GammaEulerConstantName.unit, unit]; ipra_ring)
      (le_mul_mono (le_refl Q) h)
  have base : Γ ⊢[PRAAx] S (two*m) F ≐ S (Q*b) F :=
    congrAp2 (sumF hB) (by dsimp [Q,m,GammaEulerConstantName.mesh, GammaEulerConstantName.unit, unit]; ipra_ring) (.eqRefl _)
  exact le_trans (le_mul_mono (le_refl (num 3)) (S_mono F range))
    (le_congr (.eqRefl _) (congrAdd (congrMul (.eqRefl _) base) (.eqRefl _)) (rectangles m F hm))

theorem finite_bound (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le a (num 4*b)) (hba : Γ ⊢[PRAAx] le b (num 4*a)) :
    Γ ⊢[PRAAx] bounded (embed (interval a b (GammaEulerConstantName.mesh p))) (num 5) (num 3) := by
  let Q := GammaEulerConstantName.mesh p
  let L := horizon a b Q
  let F := fact L
  let A := S (Q*a) F
  let B := S (Q*b) F
  let v := native (numerator a b Q L)
  let hu := mesh_interval_upper p a b F hs.andE₂ hab
  let hv := mesh_interval_upper p b a F hs.andE₁ hba
  have bound : Γ ⊢[PRAAx] le (num 3*absGap A B) (num 5*F) :=
    le_congr (Probability.MedianWeighted.ad_mul _ A B) (.eqRefl _)
      (Probability.MedianWeighted.ad_le_of hu hv)
  have norm : Γ ⊢[PRAAx] ComplexLogarithmRemainder.normSq v ≐ absGap A B*absGap A B := by
    have e := natEq (Probability.Variance.ad_sq (Γ := Γ) A B)
    apply deriveNat
    rw [ComplexLogarithmRemainder.normSq_eval]
    simp only [v,native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]
    simp only [numerator,ZT.toZ]
    dsimp only [A,B] at e
    simp only [IPRA.Q.mk_add,IPRA.Q.mk_mul,map_add,map_mul] at e
    ipra_simps
    linear_combination -e
  have hF := GammaEulerMesh.factorial_positive (Γ := Γ) L
  have h3 : Γ ⊢[PRAAx] le one (num 3 : PTm n) := by ipra_le 2
  apply GaussianRationalMetric.bounded_of_cleared _ v F (num 5) (num 3) hF h3
    (RationalGaussianEmbedding.embed_from_representation _ _ _ (RationalHarmonicInterval.common_value a b Q L))
  exact le_congr
    ((by ipra_ring : Γ ⊢[PRAAx] (num 3*absGap A B)*(num 3*absGap A B) ≐ (num 3*num 3)*(absGap A B*absGap A B)).eqTrans
      (congrMul (.eqRefl _) norm.eqSymm)) (by ipra_ring) (le_mul_mono bound bound)

private theorem unit_late (p : PTm n) (hp : Γ ⊢[PRAAx] le (num 5) p) : Γ ⊢[PRAAx] le (num 32) (unit p) := by
  have e : Γ ⊢[PRAAx] unit (num 5 : PTm n) ≐ num 32 :=
    (pw_succ two (num 4)).eqTrans ((congrMul GaussianFiniteLogarithmDyadicTail.two_four (.eqRefl _)).eqTrans (by ipra_ring))
  exact le_congr e (.eqRefl _) (GaussianExponentialReference.unit_monotone hp)

theorem sample_bound (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b)
    (hab : Γ ⊢[PRAAx] le a (num 4*b)) (hba : Γ ⊢[PRAAx] le b (num 4*a))
    (hp : Γ ⊢[PRAAx] le (num 5) p) : Γ ⊢[PRAAx] bounded (sample p a b) two one := by
  have u := unit_positive (Γ := Γ) p
  have h3 : Γ ⊢[PRAAx] le one (num 3 : PTm n) := by ipra_le 2
  have raw := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ u h3
    (GaussianPositiveRationalLogarithmProperness.sample_interval_error p a b hs) (finite_bound p a b hs hab hba)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ u h3) (le_refl one)
    (by ipra_le sl (unit_late p hp)+8) raw

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmFactorFourBound
