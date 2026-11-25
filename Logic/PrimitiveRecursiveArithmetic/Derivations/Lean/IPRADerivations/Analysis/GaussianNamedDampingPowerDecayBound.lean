import IPRADerivations.Analysis.GaussianNamedDampingPowerPositive
import IPRADerivations.Analysis.GaussianEulerNamedUpperTail

/-!
# Uniform unit bound for the actual named damping factor

Late chart samples are nonnegative, so the fixed rational exponential
comparison applies to each sufficiently late frozen negative sample.
A finite slack removal yields the unit bound with only the requested
observation error for the original decay program.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerDecayBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianNamedDampingPowerChart (source nameF data)
open GaussianNamedDampingPowerPositive (original_positive_at)
open GaussianNamedDampingPowerRealSamples (powerDenominator chart_real negative_real decay_real)
open GaussianEulerDampedNamedIntegrand (decayF decayData)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianRadiusExponentialName (input bounded_samples_at)
open GaussianRationalHorner (canonical qzero positive_product)
open GaussianRationalMetric (bounded qnegative qsub qsub_canonical qnegative_canonical)
open GaussianRationalSyntheticDivision (qone)
open GaussianSignedNameExponentialOrder (realSamples real_sample_at)
open GaussianNamedPositiveExponentialOrder (real_order_at scalar_coordinate_distance)
open GaussianNamedInverseRate (rateNumerator rateDenominator rate_at denominator_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open RationalValueBounds (upper upper_congr upper_of_radius upper_triangle upper_mono)
open RationalSupMetric (denominatorOf)
open RationalGaussianEmbedding (axis scalarZero embed canonical_axis_roundtrip embed_zero)
open RationalArgmin (rationalLE rationalLE_congr)
open GaussianNamedRealOrderTransport (upperSlack remove_upper_slack)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def cost (K : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor K+num 3

private theorem zero_scalar : Γ ⊢[PRAAx] fstT (qzero : PTm n) ≐ scalarZero :=
  (congrFst (embed_zero (Γ := Γ))).eqSymm.eqTrans
    ((fst_pair _ _).eqTrans RationalGaussianEmbedding.scalar_recode_zero)

private theorem negative_order (F : PR 2) (x j : PTm n)
    (h : Γ ⊢[PRAAx] GaussianPositiveRealArithmetic.positive
      (ap2 F (GaussianFastValueCut.exponent (one+one) j) x)) : Γ ⊢[PRAAx]
    rationalLE (fstT (ap2 (negativeF F) j (negativeData x))) (fstT qzero) := by
  let v := ap2 F (GaussianFastValueCut.exponent (one+one) j) x
  let a := fstT v
  let N := GaussianPositiveRealArithmetic.numerator a
  let D := denominatorOf a
  have neg := GaussianRationalSyntheticDivision.qzero_add (Γ := Γ) (qnegative v) (qnegative_canonical v)
  have name := (GaussianNameRingLaws.negative_at (Γ := Γ) F x j).eqTrans
    ((GaussianNameArithmetic.recode_congr neg).eqTrans (GaussianExponentialReference.recode_fixed _ (qnegative_canonical v)))
  have read := (congrFst name).eqTrans (fst_pair _ _)
  have pos := GaussianPositiveRealArithmetic.natural_representation a h.andE₂
  have repr := RationalRepresentations.represents_negative a (ZT.ofNat N) D pos
  have zeroRepr := RationalGaussianEmbedding.scalar_zero_represents (Γ := Γ) one
  exact rationalLE_congr read.eqSymm zero_scalar.eqSymm
    (RationalArithmetic.order_of_representations _ _ (-ZT.ofNat N) (ZT.ofNat zero) D one repr zeroRepr
      (RationalArgmin.denominator_positive a) (le_refl one) (by
        apply zle_of_toZ N
        simp only [ZT.toZ_mul,ZT.toZ_neg,ZT.toZ_ofNat]
        ipra_simps
        ring))

private theorem zero_at (K j : PTm n) : Γ ⊢[PRAAx]
    ap2 (GaussianRadiusExponentialName.nameF constantF) j (GaussianRadiusExponentialName.data K qzero) ≐ qone :=
  (GaussianRadiusExponentialName.sample_at constantF K j qzero).eqTrans
    ((GaussianNameConjugation.scalar_sum_congr _ (constant_at _ _)).eqTrans
      (GaussianGammaCanonicalTailExponential.scalar_zero_point _))

private theorem sampled_bound (F : PR 2) (K x p j : PTm n)
    (hf : Γ ⊢[PRAAx] input F K x) (hr : Γ ⊢[PRAAx] realSamples F x)
    (hj : Γ ⊢[PRAAx] rationalLE (fstT (ap2 F j x)) (fstT qzero)) : Γ ⊢[PRAAx]
    upperSlack (fstT (ap2 (GaussianRadiusExponentialName.nameF F) p (GaussianRadiusExponentialName.data K x)))
      (fstT qone) one (unit p) (cost K) j := by
  let P := unit p
  let J := unit j
  let v := ap2 F j x
  let Y := ap2 (GaussianRadiusExponentialName.nameF F) p (GaussianRadiusExponentialName.data K x)
  let Z := ap2 (GaussianRadiusExponentialName.nameF constantF) j (GaussianRadiusExponentialName.data K v)
  let L := GaussianRadiusExponentialLipschitzRate.factor K
  let A := rateNumerator (L*one) J p j
  let D := rateDenominator J p j
  have hD := denominator_positive (Γ := Γ) J p j (unit_positive j)
  have near := rate_at _ _ _ _ _ _ p j (GaussianSignedNameExponentialOrder.exponential_own_sample_rate F K x j hf)
  have first : Γ ⊢[PRAAx] upper (fstT Y) (fstT Z) A D :=
    upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hD near)
  have comp := GaussianSignedNameExponentialOrder.constant_real_order v qzero K (real_sample_at F x j hr)
    (.andI GaussianRationalSyntheticDivision.qzero_canonical RationalGaussianEmbedding.axis_zero)
    (bounded_samples_at F K x j hf.andE₂) (GaussianEulerNamedUpperTail.zero_bound K one (le_refl one)) hj
  have second := upper_congr (.eqRefl _) (congrFst (zero_at K j)) (.eqRefl _) (.eqRefl _)
    (real_order_at _ _ _ _ j j comp)
  have joined := upper_triangle _ _ _ _ _ _ _ first second
  refine upper_mono _ _ _ _ _ _ (positive_product _ _ hD (positive_product _ _ (unit_positive j) (unit_positive j))) joined ?_
  exact le_of_eq_add (d := zero) (by dsimp only [A,D,rateNumerator,rateDenominator,cost,L,P,J]; ipra_ring)

private theorem scalar_upper (F G : PR 2) (p x y C₀ C R₀ R E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source F G x y C₀ C R₀ R E T a b) : Γ ⊢[PRAAx]
    upper (fstT (ap2 (decayF (nameF F G)) p (decayData (nameF F G) (data F G x y a b))))
      (fstT qone) one (unit p) := by
  let F₀ := nameF F G
  let X₀ := data F G x y a b
  let f := negativeF F₀
  let X := negativeData X₀
  let K := GaussianNameBounds.U f X
  let v := fstT (ap2 (decayF F₀) p (decayData F₀ X₀))
  let M := two*powerDenominator R E T
  let j₀ := GaussianNamedRealOrderTransport.precision v (fstT qone) (unit p) (cost K)
  let j := j₀+M
  let k := GaussianFastValueCut.exponent (one+one) j
  have regular := GaussianNamedDampingPowerChart.name_regular F G x y C₀ C R₀ R E T a b hs
  have hi := GaussianGammaFiniteApproximantName.exponential_input f X (GaussianNameRingLaws.negative_fast F₀ X₀ regular)
  have hr := negative_real F₀ X₀ (chart_real F G x y C₀ C R₀ R a b hs.andE₁ hs.andE₂.andE₁)
  have hM : Γ ⊢[PRAAx] le M k := le_trans (le_add_left M j₀) (le_add_right j _)
  have pay : Γ ⊢[PRAAx] le M (unit k) := le_trans hM (le_trans (le_succ_self k) (RationalClosure.succ_le_two_pow k))
  have sign := negative_order F₀ X₀ j (original_positive_at F G k x y C₀ C R₀ R E T a b hs pay)
  have raw : Γ ⊢[PRAAx] upperSlack v (fstT qone) one (unit p) (cost K) j := sampled_bound f K X p j hi hr sign
  have later := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) j₀ j (le_add_right j₀ M)
  have pre : Γ ⊢[PRAAx] upperSlack v (fstT qone) one (unit p) (cost K) j₀ := by
    refine upper_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive j)) raw ?_
    ipra_le (Groth.ι (Q.mk Γ (cost K*unit p*unit p)))*sl later
  exact remove_upper_slack _ _ _ _ _ pre

theorem original_decay_bound (F G : PR 2) (p x y C₀ C R₀ R E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source F G x y C₀ C R₀ R E T a b) : Γ ⊢[PRAAx]
    bounded (ap2 (decayF (nameF F G)) p (decayData (nameF F G) (data F G x y a b))) (unit p+one) (unit p) := by
  let F₀ := nameF F G
  let X₀ := data F G x y a b
  let f := negativeF F₀
  let X := negativeData X₀
  let K := GaussianNameBounds.U f X
  let V := ap2 (decayF F₀) p (decayData F₀ X₀)
  let P := unit p
  have hp := unit_positive (Γ := Γ) p
  have regular := GaussianNamedDampingPowerChart.name_regular F G x y C₀ C R₀ R E T a b hs
  have hi := GaussianGammaFiniteApproximantName.exponential_input f X (GaussianNameRingLaws.negative_fast F₀ X₀ regular)
  have hr := negative_real F₀ X₀ (chart_real F G x y C₀ C R₀ R a b hs.andE₁ hs.andE₂.andE₁)
  have real := real_sample_at _ _ p (decay_real F G x y C₀ C R₀ R a b hs.andE₁ hs.andE₂.andE₁)
  have lower : Γ ⊢[PRAAx] upper scalarZero (fstT V) one P :=
    GaussianRealNameExponentialNonnegative.original_observation_nonnegative f K X p hi hr
  have low : Γ ⊢[PRAAx] upper scalarZero (fstT V) (P+one) P := upper_mono _ _ _ _ _ _ hp lower
    (le_congr (.eqRefl _) (by unfold P; ipra_ring) (le_add_right (one*P) (P*P)))
  have qoneBound := (GaussianReconstructionRoots.distance_zero_iff (Γ := Γ) qone one one (le_refl one)).iffMpr
    GaussianRationalReciprocal.qone_bounded
  have unitBound := upper_congr (.eqRefl _) zero_scalar (.eqRefl _) (.eqRefl _)
    (upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ one one (le_refl one) qoneBound))
  have up0 := upper_triangle _ _ _ _ _ _ _ (scalar_upper F G p x y C₀ C R₀ R E T a b hs) unitBound
  have up : Γ ⊢[PRAAx] upper (fstT V) scalarZero (P+one) P := upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (by ipra_ring) up0
  have radius := RationalValueBounds.radius_of_upper _ _ _ _ up low
  have dist := GaussianRationalDistanceOrder.distance_congr (canonical_axis_roundtrip V real.andE₁ real.andE₂) embed_zero
    (.eqRefl _) (.eqRefl _) (RationalGaussianNameEmbedding.distance_from_radius _ _ _ _ hp radius)
  exact (GaussianReconstructionRoots.distance_zero_iff V _ _ hp).iffMp dist

theorem actual_named_power_damping_factor_unit_bound_closed (F G : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (source F G (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
        bounded (ap2 (decayF (nameF F G)) (var 0) (decayData (nameF F G) (data F G (var 1) (var 2) (var 9) (var 10))))
          (unit (var 0)+one) (unit (var 0))) :=
  closeUniv 11 (.impI (original_decay_bound F G _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerDecayBound
