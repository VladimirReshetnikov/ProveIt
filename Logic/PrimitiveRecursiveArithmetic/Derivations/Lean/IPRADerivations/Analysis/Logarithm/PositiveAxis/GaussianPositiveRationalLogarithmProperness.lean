import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithm
import IPRADerivations.Analysis.Series.Harmonic.RationalHarmonicInterval

/-!
# Original positive rational logarithm samples and harmonic intervals

Actual old integer logarithms are placed on one proved factorial scale.
Their common H_Q terms cancel in field value. The resulting actual finite
harmonic interval will compare the original logarithm names without
assuming that exponentiation is injective.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmProperness

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.MeshChange (S_denom)
open Products (fact)
open RationalHarmonicInterval (horizon interval)
open GammaEulerMesh (factorial_positive)
open GaussianRationalHorner (canonical_unique represents_congr)
open GaussianRationalMetric (qsub distanceBounded)
open RationalGaussianEmbedding (embed embed_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def logNumerator (a Q L : PTm n) : ZT n := ⟨S (Q*a) (fact L),S Q (fact L)⟩
def commonLog (a Q L : PTm n) : PTm n := RationalIntegerNormalization.normalize (logNumerator a Q L) (fact L)

theorem log_at_common (a Q L : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hL : Γ ⊢[PRAAx] le (Q*a) L) : Γ ⊢[PRAAx]
    commonLog a Q L ≐ GammaMeshRobinLogBridge.harmonicLog a Q := by
  have qn : Γ ⊢[PRAAx] le Q (Q*a) := by ipra_le 𝔞 Q*sl ha
  have left := natEq (S_denom (le_refl (Q*a)) hL)
  have right := natEq (S_denom qn hL)
  apply RationalFiniteSum.canonical_equal (commonLog a Q L) (GammaMeshRobinLogBridge.harmonicLog a Q)
    (logNumerator a Q L) (GammaMeshRobinLogBridge.harmonicNumerator a Q) (fact L) (fact (Q*a))
    (RationalNormalForm.normalize_well_formed _ _ (factorial_positive L))
    (RationalNormalForm.normalize_well_formed _ _ (factorial_positive (Q*a)))
    (RationalIntegerNormalization.normalize_preserves_value _ _ (factorial_positive L))
    (RationalIntegerNormalization.normalize_preserves_value _ _ (factorial_positive (Q*a)))
    (factorial_positive L) (factorial_positive (Q*a))
  apply ZT.derive
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [logNumerator,GammaMeshRobinLogBridge.harmonicNumerator,ZT.toZ]
  ipra_simps
  linear_combination left-right

theorem common_difference (a b Q L : PTm n) : Γ ⊢[PRAAx]
    qsub (embed (commonLog a Q L)) (embed (commonLog b Q L)) ≐ embed (RationalHarmonicInterval.common a b Q L) := by
  have hF := factorial_positive (Γ := Γ) L
  have left := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (commonLog a Q L) (logNumerator a Q L) (fact L)
    (RationalIntegerNormalization.normalize_preserves_value _ _ hF)
  have right := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (commonLog b Q L) (logNumerator b Q L) (fact L)
    (RationalIntegerNormalization.normalize_preserves_value _ _ hF)
  have difference := GaussianRationalMetric.qsub_represents _ _ _ _ _ hF left right
  have target := RationalGaussianEmbedding.embed_from_representation (Γ := Γ) (RationalHarmonicInterval.common a b Q L)
    (RationalHarmonicInterval.numerator a b Q L) (fact L) (RationalHarmonicInterval.common_value a b Q L)
  have same : Γ ⊢[PRAAx] GaussianRootAlgebra.equal
      (GaussianRootAlgebra.sub (RationalGaussianEmbedding.native (logNumerator a Q L))
        (RationalGaussianEmbedding.native (logNumerator b Q L)))
      (RationalGaussianEmbedding.native (RationalHarmonicInterval.numerator a b Q L)) := by
    apply GaussianRootAlgebra.equal_of_values
      (a := GaussianRootAlgebra.sub (RationalGaussianEmbedding.native (logNumerator a Q L))
        (RationalGaussianEmbedding.native (logNumerator b Q L)))
      (b := RationalGaussianEmbedding.native (RationalHarmonicInterval.numerator a b Q L))
    all_goals simp only [GaussianRootAlgebra.re_sub,GaussianRootAlgebra.im_sub]
    all_goals simp only [RationalGaussianEmbedding.native,ComplexLogarithmRemainder.eval_re_code,ComplexLogarithmRemainder.eval_im_code]
    all_goals try simp only [ZT.toZ_ofNat]
    all_goals try simp only [logNumerator,RationalHarmonicInterval.numerator,ZT.toZ]
    all_goals try ipra_simps
    all_goals ring
  exact canonical_unique _ _ (RationalGaussianEmbedding.native (RationalHarmonicInterval.numerator a b Q L))
    (fact L) (GaussianRationalMetric.qsub_canonical _ _) (RationalGaussianEmbedding.embed_canonical _) hF
    (represents_congr (.eqRefl _) same (.eqRefl _) difference) target

/-- Exact original common-mesh cancellation, including either sign of a-b. -/
theorem original_finite_difference (a b Q : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qsub (embed (GammaMeshRobinLogBridge.harmonicLog a Q)) (embed (GammaMeshRobinLogBridge.harmonicLog b Q)) ≐ embed (interval a b Q) := by
  let L := horizon a b Q
  have ea := log_at_common a Q L ha (RationalHarmonicInterval.left_horizon a b Q)
  have eb := log_at_common b Q L hb (RationalHarmonicInterval.right_horizon a b Q)
  exact (GaussianRationalSyntheticDivision.qsub_congr (embed_congr ea).eqSymm (embed_congr eb).eqSymm).eqTrans
    (common_difference a b Q L)


open GaussianPositiveRationalLogarithm (logF baseF data source sample differenceF differenceData name_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianNameEquivalence (crossEquivalent)

/-- The true normalized logarithm observation is close to its actual
common-mesh harmonic interval; all three original name clocks are kept. -/
theorem sample_interval_error (p a b : PTm n) (h : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (embed (interval a b (GammaEulerConstantName.mesh p))) (num 8) (unit p) := by
  let F := baseF
  let G := GaussianNameRingLaws.negativeF F
  let Y := GaussianNameRingLaws.negativeData b
  let A := ap2 F p a
  let B := ap2 F p b
  have fa := GaussianGammaFiniteApproximantName.log_regular a h.andE₁
  have fb := GaussianGammaFiniteApproximantName.log_regular b h.andE₂
  have nb := GaussianNameRingLaws.negative_fast F b fb
  have old := GaussianNameEquivalence.cross_at logF differenceF (data a b) (differenceData a b) p p
    (GaussianPositiveRationalLogarithm.original_logarithm_difference a b h)
  have first : Γ ⊢[PRAAx] distanceBounded (sample p a b) (ap2 differenceF p (differenceData a b)) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (GaussianRationalHorner.positive_product _ _ (unit_positive p) (unit_positive p)) (unit_positive p)
      (le_of_eq_add (d := zero) (by ipra_ring)) old
  have added := GaussianNameRingLaws.add_sample_error F G a Y p fa nb
  have negated := GaussianNameRingLaws.sum_right_error A _ _ _ _ (unit_positive p)
    (GaussianNameRingLaws.negative_sample_error F b p fb)
  have eq : Γ ⊢[PRAAx] GaussianRationalHorner.qadd A (qsub GaussianRationalHorner.qzero B) ≐ qsub A B :=
    GaussianRationalSyntheticDivision.qadd_congr (.eqRefl _)
      (GaussianRationalSyntheticDivision.qzero_add _ (GaussianRationalMetric.qnegative_canonical B))
  have near : Γ ⊢[PRAAx] distanceBounded (sample p a b) (qsub A B) (num 8) (unit p) :=
    distance_congr (.eqRefl _) eq (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first
        (distance_triangle_same _ _ _ _ _ _ (unit_positive p) added negated))
  have finite : Γ ⊢[PRAAx] qsub A B ≐ embed (interval a b (GammaEulerConstantName.mesh p)) :=
    (GaussianRationalSyntheticDivision.qsub_congr (GaussianGammaFiniteApproximantName.log_sample_at p a)
      (GaussianGammaFiniteApproximantName.log_sample_at p b)).eqTrans
        (original_finite_difference a b (GammaEulerConstantName.mesh p) h.andE₁ h.andE₂)
  exact distance_congr (.eqRefl _) finite (.eqRefl _) (.eqRefl _) near

theorem equal_ratio_diagonal (p a b c d : PTm n) (hab : Γ ⊢[PRAAx] source a b)
    (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (sample p c d) (num 17) (unit p) := by
  let Q := GammaEulerConstantName.mesh p
  have qpos := GammaEulerConstantName.mesh_positive (Γ := Γ) p
  have finite := RationalGaussianNameEmbedding.distance_from_radius _ _ two Q qpos
    (RationalHarmonicInterval.equal_ratio_finite a b c d Q hab.andE₁ hab.andE₂ hcd.andE₁ hcd.andE₂ qpos he)
  have middle : Γ ⊢[PRAAx] distanceBounded (embed (interval a b Q)) (embed (interval c d Q)) one (unit p) :=
    distance_radius_mono _ _ _ _ _ _ qpos (unit_positive p)
      (le_of_eq_add (d := two*unit p) (by unfold GammaEulerConstantName.mesh GammaEulerConstantName.unit unit; ipra_ring)) finite
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p)
      (distance_triangle_same _ _ _ _ _ _ (unit_positive p) (sample_interval_error p a b hab) middle)
      (distance_symmetric _ _ _ _ (unit_positive p) (sample_interval_error p c d hcd)))

/-- Encoding properness for the unchanged original logarithm program,
proved from the actual finite harmonic comparison and finite error removal. -/
theorem original_logarithm_proper (a b c d : PTm n) (hab : Γ ⊢[PRAAx] source a b)
    (hcd : Γ ⊢[PRAAx] source c d) (he : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    crossEquivalent logF logF (data a b) (data c d) := by
  refine GaussianNameRingLaws.equivalent_of_envelope logF logF (data a b) (data c d) (num 17)
    (name_regular a b hab) (name_regular c d hcd) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using hab.shift
  have ht : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift c) (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hcd.shift
  have eq : Γ.map Fm.shift ⊢[PRAAx] Syn.shift a*Syn.shift d ≐ Syn.shift b*Syn.shift c := by simpa [Fm.shift,Syn.shift] using he.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal,sample,Syn.shift,
    GaussianPositiveRationalLogarithm.subst_data,PTm.subst_num,unit] using
    equal_ratio_diagonal (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift c) (Syn.shift d) hs ht eq


theorem original_logarithm_rescale (a b E : PTm n) (hab : Γ ⊢[PRAAx] source a b)
    (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx] crossEquivalent logF logF (data (E*a) (E*b)) (data a b) :=
  original_logarithm_proper _ _ _ _ (.andI (RationalAlgebra.positive_product hE hab.andE₁)
    (RationalAlgebra.positive_product hE hab.andE₂)) hab (by ipra_ring)

theorem original_finite_harmonic_logarithm_difference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ qsub (embed (GammaMeshRobinLogBridge.harmonicLog (var 0) (var 2)))
      (embed (GammaMeshRobinLogBridge.harmonicLog (var 1) (var 2))) ≐ embed (interval (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_finite_difference _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))
theorem actual_original_logarithm_harmonic_interval_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 1) (var 2) ⟶ distanceBounded (sample (var 0) (var 1) (var 2))
      (embed (interval (var 1) (var 2) (GammaEulerConstantName.mesh (var 0)))) (num 8) (unit (var 0))) :=
  closeUniv 3 (.impI (sample_interval_error _ _ _ Prf.hyp0))
theorem original_positive_rational_logarithm_encoding_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) ⟶ source (var 2) (var 3) ⟶ var 0*var 3 ≐ var 1*var 2 ⟶
      crossEquivalent logF logF (data (var 0) (var 1)) (data (var 2) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (original_logarithm_proper _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))
theorem original_positive_rational_logarithm_rescaling_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ le one (var 2) ⟶ crossEquivalent logF logF
      (data (var 2*var 0) (var 2*var 1)) (data (var 0) (var 1))) :=
  closeUniv 3 (.impI (.impI (original_logarithm_rescale _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianPositiveRationalLogarithmProperness
