import IPRADerivations.Analysis.Beta.GaussianBetaUpperRowDampedError
import IPRADerivations.Analysis.Integration.GaussianMonomialDecayQuadrature

/-!
# Exact scalar row majorants and the literal monomial-decay observation

The scalar radius from the unchanged beta/Euler row is separated into
its actual positive decay-reference term and explicit observation errors.
The reference term is compared with the literal original constant-times-
decay name at an independent query, preserving its actual product clock.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaRowMonomialReference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBetaKernelDecayDampedError (reference referenceScalar referenceNumerator referenceDenominator)
open GaussianBetaUpperRowDampedError (monomialNumerator monomialDenominator)
open GaussianDominantPairAlgebra (radiusPoint radiusNumerator radius_represents radius_numerator_norm radius_bounded radius_multiply radius_congr)
open GaussianMonomialDecayMajorant (monomial)
open GaussianRationalHorner (qmul ofGaussian positive_product canonical_unique represents_congr)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalGaussianEmbedding (embed)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def scalarMajorant (p v q R a b N : PTm n) : PTm n :=
  fraction (monomialNumerator p v q R a b N) (monomialDenominator p v q R a b N)
def referenceFraction (q d a b N : PTm n) : PTm n :=
  fraction (pw a d*referenceNumerator q a b) (N*pw b d*referenceDenominator q a b)
def scaledMonomial (r d a b N : PTm n) : PTm n :=
  qmul (radiusPoint one N) (GaussianMonomialDecayMajorant.sample r d a b)

/-- Exact positive fraction gap, interpreted in the original Gaussian metric. -/
theorem fraction_gap_distance (A B C D X Y : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (hY : Γ ⊢[PRAAx] le one Y)
    (gap : Γ ⊢[PRAAx] Y*(A*D) ≐ Y*(C*B)+X*B*D) : Γ ⊢[PRAAx]
    distanceBounded (embed (fraction A B)) (embed (fraction C D)) X Y := by
  have e := natEq gap
  have left : Γ ⊢[PRAAx] RationalValueBounds.upper (fraction A B) (fraction C D) X Y := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat A) (ZT.ofNat C) B D X Y hB hD
      (fraction_represents A B hB) (fraction_represents C D hD)
    apply zle_of_toZ zero
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    linear_combination e
  have right : Γ ⊢[PRAAx] RationalValueBounds.upper (fraction C D) (fraction A B) X Y := by
    apply RationalCubeInfimumIntervals.upper_of_representations _ _ (ZT.ofNat C) (ZT.ofNat A) D B X Y hD hB
      (fraction_represents C D hD) (fraction_represents A B hB)
    apply zle_of_toZ (two*X*B*D)
    simp only [ZT.toZ_mul,ZT.toZ_sub,ZT.toZ_ofNat]
    ipra_simps
    linear_combination -e
  exact RationalGaussianNameEmbedding.distance_from_radius _ _ X Y hY (RationalValueBounds.radius_of_upper _ _ X Y left right)

theorem scalar_denominator_positive (p v q R a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    le one (monomialDenominator p v q R a b N) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ (RationalNonnegativePowers.denominator_positive b (R+two) hb) hN)
      (GaussianBetaKernelDecayDampedError.reference_positive q a b)) (unit_positive q)) (unit_positive p)) (unit_positive v)

theorem row_majorized (p v q z R B a b N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianBetaUpperRowDampedError.source z R B a b N) : Γ ⊢[PRAAx]
    GaussianRationalSumMajorant.majorized
      (qsub (GaussianBetaKernelGridComparison.row p z B a b N) (GaussianEulerIntegrandName.sample v z B a b))
      (scalarMajorant p v q R a b N) := by
  have hd := scalar_denominator_positive p v q R a b N h.andE₂.andE₁ h.andE₂.andE₂.andE₁
  have rep := fraction_represents (Γ := Γ) (monomialNumerator p v q R a b N) (monomialDenominator p v q R a b N) hd
  exact GaussianRationalSumMajorant.from_representation _ _ _ _ hd
    (GaussianRationalL1.nonnegative_of_representation _ _ _ hd rep) rep
    (GaussianBetaUpperRowDampedError.original_high_row_exact_power_error p v q z R B a b N h)

def samplingNumerator (p v q d a b N : PTm n) : PTm n :=
  num 3*pw a d*unit p*unit v+N*pw b d*unit q*(unit p+unit v)
def samplingDenominator (p v q d b N : PTm n) : PTm n := N*pw b d*unit q*unit p*unit v

theorem scalar_reference_distance (p v q R a b N : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (embed (scalarMajorant p v q R a b N)) (embed (referenceFraction q (R+two) a b N))
      (samplingNumerator p v q (R+two) a b N) (samplingDenominator p v q (R+two) b N) := by
  have bp := RationalNonnegativePowers.denominator_positive (Γ := Γ) b (R+two) hb
  have rd := GaussianBetaKernelDecayDampedError.reference_positive (Γ := Γ) q a b
  exact fraction_gap_distance _ _ _ _ _ _ (scalar_denominator_positive p v q R a b N hb hN)
    (positive_product _ _ (positive_product _ _ hN bp) rd)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hN bp) (unit_positive q)) (unit_positive p)) (unit_positive v))
    (by dsimp only [monomialNumerator,monomialDenominator,GaussianBetaKernelDecayDampedError.referenceBudget,
        samplingNumerator,samplingDenominator]; ipra_ring)

theorem natural_power_bound (a b T d : PTm n) (h : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    le (pw a d) (pw T d*pw b d) :=
  le_congr (.eqRefl _) (AnalyticNumberTheory.LocalFactor.pw_mul_base T b d) (pw_le_pw d h)

theorem uniform_scalar_reference_distance (p v q R a b N T : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (embed (scalarMajorant p v q R a b N)) (embed (referenceFraction q (R+two) a b N))
      (num 3*pw T (R+two)*unit p*unit v+N*unit q*(unit p+unit v)) (N*unit q*unit p*unit v) := by
  have bp := RationalNonnegativePowers.denominator_positive (Γ := Γ) b (R+two) hb
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hN bp) (unit_positive q)) (unit_positive p)) (unit_positive v))
    (positive_product _ _ (positive_product _ _ (positive_product _ _ hN (unit_positive q)) (unit_positive p)) (unit_positive v)) _
    (scalar_reference_distance p v q R a b N hb hN)
  dsimp only [samplingNumerator,samplingDenominator]
  ipra_le (𝔞 (num 3*N*unit q*unit p*unit p*unit v*unit v))*sl (natural_power_bound a b T (R+two) ht)

theorem radial_embedding (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    embed (fraction A B) ≐ radiusPoint A B := by
  have left := RationalGaussianEmbedding.embed_from_representation _ _ _ (fraction_represents A B hB)
  apply canonical_unique _ _ (radiusNumerator A) B (RationalGaussianEmbedding.embed_canonical _) (GaussianRationalHorner.ofGaussian_canonical _ _ hB) hB
    (represents_congr (.eqRefl _) ?_ (.eqRefl _) left) (radius_represents A B hB)
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [RationalGaussianEmbedding.native,radiusNumerator,ComplexLogarithmRemainder.eval_re_code,
    ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]

theorem reference_radial (q a b : PTm n) : Γ ⊢[PRAAx]
    reference q a b ≐ radiusPoint (referenceNumerator q a b) (referenceDenominator q a b) := by
  have hd := GaussianBetaKernelDecayDampedError.reference_positive (Γ := Γ) q a b
  have embedding : Γ ⊢[PRAAx] reference q a b ≐ embed (referenceScalar q a b) :=
    (RationalGaussianEmbedding.canonical_axis_roundtrip _
      (GaussianRealExponentialPositiveRepresentative.sample_canonical (GaussianEulerDecayOrder.signedTime a b) q)
      (GaussianRealExponentialPositiveRepresentative.sample_nonnegative (GaussianEulerDecayOrder.signedTime a b) q).andE₁).eqSymm
  have rep := RationalGaussianEmbedding.embed_from_representation _ _ _ (GaussianBetaKernelDecayDampedError.reference_representation (Γ := Γ) q a b)
  apply canonical_unique _ _ (radiusNumerator (referenceNumerator q a b)) (referenceDenominator q a b)
    (GaussianRealExponentialPositiveRepresentative.sample_canonical _ q) (GaussianRationalHorner.ofGaussian_canonical _ _ hd) hd
    (represents_congr embedding.eqSymm ?_ (.eqRefl _) rep) (radius_represents _ _ hd)
  apply GaussianRootAlgebra.equal_of_values
  all_goals simp only [RationalGaussianEmbedding.native,radiusNumerator,ComplexLogarithmRemainder.eval_re_code,
    ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat]

theorem weighted_reference (q d a b N : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    qmul (radiusPoint one N) (qmul (monomial d a b) (reference q a b)) ≐ embed (referenceFraction q d a b N) := by
  have bp := RationalNonnegativePowers.denominator_positive (Γ := Γ) b d hb
  have rd := GaussianBetaKernelDecayDampedError.reference_positive (Γ := Γ) q a b
  have exactProduct := (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl (radiusPoint one N))
    ((GaussianRationalSyntheticDivision.qmul_congr (.eqRefl (monomial d a b)) (reference_radial q a b)).eqTrans
      (radius_multiply _ _ _ _ bp rd))).eqTrans (radius_multiply _ _ _ _ hN (positive_product _ _ bp rd))
  exact exactProduct.eqTrans ((radius_congr (one_mul _) (by ipra_ring)).eqTrans
    (radial_embedding _ _ (positive_product _ _ (positive_product _ _ hN bp) rd)).eqSymm)

theorem multiply_distance (c x y A B C D : PTm n)
    (hb : Γ ⊢[PRAAx] le one B) (hd : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] bounded c C D) (he : Γ ⊢[PRAAx] distanceBounded x y A B) : Γ ⊢[PRAAx]
    distanceBounded (qmul c x) (qmul c y) (C*A) (D*B) :=
  GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference c x y).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ hd hb hc he)

theorem monomial_bound (d a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    bounded (monomial d a b) (pw T d) one :=
  bounded_radius_mono _ _ _ _ _ (RationalNonnegativePowers.denominator_positive b d hb) (le_refl one)
    (le_congr (by ipra_ring : Γ ⊢[PRAAx] pw a d ≐ pw a d*one) (.eqRefl _) (natural_power_bound a b T d ht))
    (radius_bounded _ _ (RationalNonnegativePowers.denominator_positive b d hb))

theorem reference_monomial_distance (q r d a b N T : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (embed (referenceFraction q d a b N)) (scaledMonomial r d a b N)
      (pw T d*(unit q+unit r)) (N*unit q*unit r) := by
  let f := GaussianGammaCanonicalExponent.constantF
  let x := monomial d a b
  let y := GaussianEulerIntegrandName.decayData a b
  let k := GaussianNamedSmallPerturbationTransport.productClock f GaussianEulerIntegrandName.decayF x y r
  have read : Γ ⊢[PRAAx] GaussianMonomialDecayMajorant.sample r d a b ≐ qmul x (ap2 GaussianEulerIntegrandName.decayF k y) :=
    (GaussianNamedSmallPerturbationTransport.product_at f GaussianEulerIntegrandName.decayF x y r).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (GaussianGammaCanonicalExponent.constant_at k x) (.eqRefl _))
  have cross := GaussianNameEquivalence.cross_at GaussianRealExponentialPositiveRepresentative.positiveF GaussianEulerIntegrandName.decayF _ _ q k
    (GaussianEulerDecayOrder.original_decay_nonnegative_representative a b hb)
  have first := multiply_distance x _ _ _ _ (pw T d) one
    (positive_product _ _ (unit_positive q) (unit_positive k)) (le_refl one) (monomial_bound d a b T hb ht) cross
  have second := multiply_distance (radiusPoint one N) _ _ _ _ one N
    (positive_product _ _ (le_refl one) (positive_product _ _ (unit_positive q) (unit_positive k))) hN (radius_bounded one N hN) first
  have growth : Γ ⊢[PRAAx] le (unit r) (unit k) :=
    GaussianExponentialReference.unit_monotone (le_add_right r _)
  have compare : Γ ⊢[PRAAx]
      le ((one*(pw T d*(unit q+unit k)))*(N*unit q*unit r))
        ((pw T d*(unit q+unit r))*(N*(one*(unit q*unit k)))) := by
    ipra_le (𝔞 (pw T d*N*unit q*unit q))*sl growth
  exact distance_congr (weighted_reference q d a b N hb hN)
    (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _) read.eqSymm) (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _
      (positive_product _ _ hN (positive_product _ _ (le_refl one) (positive_product _ _ (unit_positive q) (unit_positive k))))
      (positive_product _ _ (positive_product _ _ hN (unit_positive q)) (unit_positive r)) compare second)

def comparisonNumerator (p v q r d T N : PTm n) : PTm n :=
  pw T d*(num 4*unit r+unit q)*unit p*unit v+N*unit q*unit r*(unit p+unit v)
def comparisonDenominator (p v q r N : PTm n) : PTm n := N*unit q*unit r*unit p*unit v

theorem original_majorant_monomial_comparison (p v q r R a b N T : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hN : Γ ⊢[PRAAx] le one N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (embed (scalarMajorant p v q R a b N)) (scaledMonomial r (R+two) a b N)
      (comparisonNumerator p v q r (R+two) T N) (comparisonDenominator p v q r N) := by
  have d1 := positive_product (Γ := Γ) _ _ (positive_product _ _ (positive_product _ _ hN (unit_positive q)) (unit_positive p)) (unit_positive v)
  have d2 := positive_product (Γ := Γ) _ _ (positive_product _ _ hN (unit_positive q)) (unit_positive r)
  have joined := GaussianReconstructionRoots.distance_triangle _ _ _ _ _ _ _ d1 d2
    (uniform_scalar_reference_distance p v q R a b N T hb hN ht)
    (reference_monomial_distance q r (R+two) a b N T hb hN ht)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ d1 d2)
    (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _ hN (unit_positive q)) (unit_positive r))
      (unit_positive p)) (unit_positive v)) _ joined
  exact le_of_eq_add (d := zero) (by dsimp only [comparisonNumerator,comparisonDenominator]; ipra_ring)

theorem actual_scalar_row_majorant_matches_literal_scaled_monomial_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((le one (var 6) ⋏ le one (var 7) ⋏ le (var 5) (var 8*var 6)) ⟶
        distanceBounded (embed (scalarMajorant (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7)))
          (scaledMonomial (var 3) (var 4+two) (var 5) (var 6) (var 7))
          (comparisonNumerator (var 0) (var 1) (var 2) (var 3) (var 4+two) (var 8) (var 7))
          (comparisonDenominator (var 0) (var 1) (var 2) (var 3) (var 7))) :=
  closeUniv 9 (.impI (original_majorant_monomial_comparison _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

@[simp] theorem subst_scalarMajorant {m : ℕ} (σ : Fin n → PTm m) (p v q R a b N : PTm n) :
    Syn.subst σ (scalarMajorant p v q R a b N) = scalarMajorant (Syn.subst σ p) (Syn.subst σ v) (Syn.subst σ q)
      (Syn.subst σ R) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [scalarMajorant,monomialNumerator,monomialDenominator,GaussianBetaKernelDecayDampedError.referenceBudget,
    referenceNumerator,referenceDenominator,referenceScalar,reference,GaussianPositiveRealArithmetic.numerator,
    RationalSupMetric.numeratorOf,GaussianEulerDecayOrder.signedTime]
@[simp] theorem subst_scaledMonomial {m : ℕ} (σ : Fin n → PTm m) (r d a b N : PTm n) :
    Syn.subst σ (scaledMonomial r d a b N) = scaledMonomial (Syn.subst σ r) (Syn.subst σ d) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ N) := by
  simp [scaledMonomial]
@[simp] theorem subst_comparisonNumerator {m : ℕ} (σ : Fin n → PTm m) (p v q r d T N : PTm n) :
    Syn.subst σ (comparisonNumerator p v q r d T N) = comparisonNumerator (Syn.subst σ p) (Syn.subst σ v) (Syn.subst σ q)
      (Syn.subst σ r) (Syn.subst σ d) (Syn.subst σ T) (Syn.subst σ N) := by simp [comparisonNumerator]
@[simp] theorem subst_comparisonDenominator {m : ℕ} (σ : Fin n → PTm m) (p v q r N : PTm n) :
    Syn.subst σ (comparisonDenominator p v q r N) = comparisonDenominator (Syn.subst σ p) (Syn.subst σ v) (Syn.subst σ q)
      (Syn.subst σ r) (Syn.subst σ N) := by simp [comparisonDenominator]

theorem original_beta_Euler_row_actual_scalar_majorant_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      (GaussianBetaUpperRowDampedError.source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) ⟶
        GaussianRationalSumMajorant.majorized
          (qsub (GaussianBetaKernelGridComparison.row (var 0) (var 3) (var 5) (var 6) (var 7) (var 8))
            (GaussianEulerIntegrandName.sample (var 1) (var 3) (var 5) (var 6) (var 7)))
          (scalarMajorant (var 0) (var 1) (var 2) (var 4) (var 6) (var 7) (var 8))) :=
  closeUniv 9 (.impI (row_majorized _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBetaRowMonomialReference
