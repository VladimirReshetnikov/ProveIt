import IPRADerivations.Analysis.Barnes.CanonicalProducts.FiniteProducts.GaussianBarnesCanonicalCorrection
import IPRADerivations.Analysis.Exponential.IntegerPowers.GaussianBoundedIntegerExponential
import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmExponentialIdentity
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.Folded.GaussianGammaFoldedApproximantBalance

/-!
# Exponentiating one original Barnes logarithm row

The canonical numerator scaling retains the rounded cubic evaluator.
The original full logarithm gives the actual factor base after
exponentiation. Its naturally scaled exponential gives the actual
rational power, and the exact correction cancels the first two terms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogFactor

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBarnesCanonicalLogRow (source local_source roundedValue roundedCubic)
open GaussianBarnesCanonicalFactor (correction powerValue exponentRadius exponentialData)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaFiniteApproximantName (exponential_input exponentialInputData)
open GaussianRationalNaturalScale (natScale)
open GaussianNameArithmetic (addF addData add_fast sum_distance multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal point_at)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian qadd qmul positive_product represents_congr ofGaussian_represents)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianLocalLogarithmName.pointF
local notation "C" => GaussianBarnesCanonicalCubicName.nameF
local notation "Scale" => GaussianNamedNaturalScale.nameF
local notation "sd" => GaussianNamedNaturalScale.data
local notation "ld" => GaussianLocalLogarithmName.data
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data

abbrev nameF : PR 2 := Scale C

def data (z R B k : PTm n) : PTm n := sd k k (ld z (R*B) (B*k))

abbrev fullF : PR 2 := Scale L
abbrev correctedF : PR 2 := addF fullF constantF

def correctedData (z R B k : PTm n) : PTm n := addData (data z R B k) (correction z B k)

def expData (z R B k : PTm n) : PTm n := exponentialInputData nameF (data z R B k)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (z R B k : PTm n) :
    Syn.subst σ (data z R B k) = data (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [data]

@[simp] theorem subst_correctedData {m : ℕ} (σ : Fin n → PTm m) (z R B k : PTm n) :
    Syn.subst σ (correctedData z R B k) =
      correctedData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by simp [correctedData]

@[simp] theorem subst_expData {m : ℕ} (σ : Fin n → PTm m) (z R B k : PTm n) :
    Syn.subst σ (expData z R B k) = expData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ k) := by
  simp [expData,exponentialInputData]

private theorem natural_is_radius (k : PTm n) :
    Γ ⊢[PRAAx] GaussianRationalNaturalScale.naturalPoint k ≐ GaussianDominantPairAlgebra.radiusPoint k one := by
  let a := ComplexLogarithmRemainder.scale k ComplexLogarithmRemainder.oneCode
  let b := GaussianDominantPairAlgebra.radiusNumerator k
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal b a := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [b,a,GaussianDominantPairAlgebra.radiusNumerator,GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one,ComplexLogarithmRemainder.eval_re_code,
        ComplexLogarithmRemainder.eval_im_code,ZT.toZ_ofNat] <;> (try ipra_simps) <;> ring
  exact GaussianRationalHorner.canonical_unique (ofGaussian a one) (ofGaussian b one) a one
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one))
    (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl one)) (le_refl one)
    (ofGaussian_represents _ _ (le_refl one)) (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ (le_refl one)))

theorem sample_at (p z R B k : PTm n) :
    Γ ⊢[PRAAx] ap2 nameF p (data z R B k) ≐ roundedValue (GaussianNamedNaturalScale.clock p k) z R B k := by
  let t := GaussianNamedNaturalScale.clock p k
  let x := ld z (R*B) (B*k)
  have e : Γ ⊢[PRAAx] natScale k (ap2 C t x) ≐ roundedValue t z R B k :=
    (GaussianRationalNaturalScale.natScale_as_product k (ap2 C t x)).eqTrans
      (qmul_congr (natural_is_radius k) (GaussianBarnesCanonicalCubicName.sample_at t z (R*B) (B*k)))
  exact (GaussianNamedNaturalScale.sample_at C p k k x).eqTrans e

theorem regular (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B k) :=
  GaussianNamedNaturalScale.name_regular C k k _ _
    (exponential_input C _ (GaussianBarnesCanonicalCubicName.regular _ _ _ (local_source z R B k h))) (le_refl _)

private theorem full_input (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input L one (ld z (R*B) (B*k)) :=
  GaussianExponentialRadiusIndependence.radius_one_input L _
    (GaussianLocalLogarithmName.original_exponential_input _ _ _ (local_source z R B k h))

private theorem full_regular (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] pointCN fullF (data z R B k) :=
  GaussianNamedNaturalScale.name_regular L k k one _ (full_input z R B k h) (le_refl _)

theorem corrected_observation (p z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] distanceBounded (ap2 correctedF p (correctedData z R B k)) (ap2 nameF p (data z R B k)) (num 3) (unit p) := by
  let s := GaussianFastValueCut.exponent two p
  let t := GaussianNamedNaturalScale.clock s k
  let N := B*k
  let x := ld z (R*B) N
  let a := GaussianBarnesCanonicalCubicName.base z N
  let b := ap2 L t x
  let c := roundedCubic t z (R*B) N
  let e := correction z B k
  let U := DyadicComplexLogarithm.unit t
  let V := data z R B k
  have hs : Γ ⊢[PRAAx] le p s := le_add_right _ _
  have hu := GaussianLocalLogarithmName.unit_positive (Γ := Γ) t
  have hl := local_source z R B k h
  have first := GaussianNamedNaturalScale.scaled_distance k (qadd c a) b (num 6) U one hu
    (GaussianBarnesCanonicalCubicName.raw_split_observation t z (R*B) N hl.andE₁)
    (GaussianRadiusExponentialName.bounded_samples_at L one x t (full_input z R B k h).andE₂)
  have combined := sum_distance (natScale k (qadd c a)) (natScale k b) e e (k*num 6) zero U hu first
    (GaussianRationalPowerDifference.distance_refl_zero e U hu)
  have readC : Γ ⊢[PRAAx] ap2 nameF s V ≐ natScale k c := by
    have direct : Γ ⊢[PRAAx] ap2 nameF s V ≐ natScale k (ap2 C t x) :=
      GaussianNamedNaturalScale.sample_at C s k k x
    exact direct.eqTrans (by
      ipra_congr (natScale (var 0) (var 1) : PTm 2) with
        [.eqRefl k, GaussianBarnesCanonicalCubicName.sample_at t z (R*B) N])
  have readF := (GaussianExponentialReference.add_sample (Γ := Γ) fullF constantF V e p).eqTrans
    (qadd_congr (GaussianNamedNaturalScale.sample_at L s k k x) (constant_at s e))
  have near : Γ ⊢[PRAAx] distanceBounded (ap2 correctedF p (correctedData z R B k)) (ap2 nameF s V) (k*num 6) U :=
    distance_congr readF.eqSymm
      ((GaussianBarnesCanonicalCorrection.cancel c z B k h.andE₁ h.andE₂.andE₁).eqTrans readC.eqSymm)
      (add_zero _)
      (.eqRefl _) (distance_symmetric _ _ _ _ hu combined)
  have hAmp := GaussianNamedNaturalScale.cap_budget (Γ := Γ) k k (le_refl _)
  have hC : Γ ⊢[PRAAx] le (num 6 : PTm n) (num 16) := le_of_eq_add (d := num 10) (by ipra_ring)
  have hd := GaussianExponentialReference.unit_monotone hs
  have reserved := le_mul_mono (le_mul_mono hAmp hC) hd
  have exactClock := (GaussianLocalLogarithmName.unit_factor (Γ := Γ) t).eqTrans
    (congrMul (GaussianNamedNaturalScale.clock_unit s k) (.eqRefl _))
  have widen : Γ ⊢[PRAAx] le ((k*num 6)*unit p) (one*U) :=
    le_congr (.eqRefl _) ((by ipra_ring : Γ ⊢[PRAAx]
      GaussianNamedNaturalScale.amplification k*num 16*unit s ≐
        unit s*GaussianNamedNaturalScale.amplification k*num 16).eqTrans
      (exactClock.eqSymm.eqTrans (one_mul U).eqSymm)) reserved
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) s
  have a₁ : Γ ⊢[PRAAx] distanceBounded (ap2 correctedF p (correctedData z R B k)) (ap2 nameF s V) one (unit p) :=
    distance_radius_mono _ _ _ _ _ _ hu hp widen near
  have a₂ : Γ ⊢[PRAAx] distanceBounded (ap2 nameF s V) (ap2 nameF p V) two (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hq hp) hp
      (by ipra_le (Groth.ι (LeanProofs.IPRA.Q.mk Γ (unit p)))*sl hd)
      (point_at nameF V s p (regular z R B k h))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp a₁ a₂)

theorem corrected_cross (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] crossEquivalent correctedF nameF (correctedData z R B k) (data z R B k) := by
  apply GaussianNameRingLaws.equivalent_of_envelope correctedF nameF (correctedData z R B k) (data z R B k) (num 3)
    (add_fast fullF constantF _ _ (full_regular z R B k h) (constant_regular _))
    (regular z R B k h)
  refine .allI ?_
  let sh (a : PTm n) := Syn.shift a
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (sh z) (sh R) (sh B) (sh k) := by
    simpa [Fm.shift,Syn.shift,sh] using h.shift
  simpa only [GaussianValueNormalizerExtensionality.rawDiagonal, Syn.shift, sh,
    subst_correctedData, subst_data, PTm.subst_num] using corrected_observation (var 0) (sh z) (sh R) (sh B) (sh k) hs

private theorem base_exponential (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] crossEquivalent (Exp L) constantF (ed one (ld z (R*B) (B*k))) (GaussianBarnesCanonicalFactor.base z B k) := by
  let w := ofGaussian z (B*k)
  let x := ld z (R*B) (B*k)
  let F := GaussianUnitDiskExponentialName.nameF L
  let G := GaussianFiniteLogarithmCompositionName.constantF
  let c := GaussianBarnesCanonicalFactor.base z B k
  have hs := local_source z R B k h
  have hE := GaussianLocalLogarithmName.original_exponential_input _ _ _ hs
  have link := GaussianLocalLogarithmExponentialIdentity.source_cross _ _ _ hs
  have ct : Γ ⊢[PRAAx] crossEquivalent G constantF w c := by
    apply GaussianNameConjugation.equal_samples_cross G constantF w c
      (GaussianFiniteLogarithmCompositionName.constant_regular _) (constant_regular _)
    refine .allI ?_
    exact (GaussianFiniteLogarithmCompositionName.constant_at (var 0) (Syn.shift w)).eqTrans
      (by simpa [w,c,GaussianBarnesCanonicalFactor.base,GaussianFiniteLogarithmCompositionTail.linearValue,Syn.shift]
        using (constant_at (var 0) (Syn.shift c)).eqSymm)
  exact cross_trans (Exp L) F constantF (ed one x) x c
    (cross_symm _ _ _ _ (GaussianExponentialRadiusIndependence.original_unit_cross L x hE))
    (cross_trans F G constantF x w c link ct)

theorem factor_cross (z R B k : PTm n) (h : Γ ⊢[PRAAx] source z R B k) :
    Γ ⊢[PRAAx] crossEquivalent (Exp nameF) GaussianBarnesCanonicalFactor.nameF
      (expData z R B k) (GaussianBarnesCanonicalFactor.data z R B k) := by
  let c := GaussianBarnesCanonicalFactor.base z B k
  let x := ld z (R*B) (B*k)
  let V := data z R B k
  let W := correction z B k
  let S := GaussianNamedNaturalScale.radius k one
  let F := Exp fullF
  let G := Exp constantF
  let A := ed S V
  let D := exponentialData z R B k
  let P := powerValue z B k
  have hc := local_source z R B k h
  have disk := GaussianFiniteLogarithmCompositionName.original_half_disk z (R*B) (B*k) hc.andE₁ hc.andE₂.andE₁ hc.andE₂.andE₂
  have b₂ : Γ ⊢[PRAAx] bounded c two one := by
    have old := GaussianRationalReciprocal.bounded_sum GaussianRationalSyntheticDivision.qone (ofGaussian z (B*k))
      one one one two (le_refl one) (le_succ_self one) GaussianRationalReciprocal.qone_bounded disk
    exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one) (le_succ_self one))
      (le_refl one) (le_of_eq_add (d := one) (by ipra_ring)) old
  have fInput := full_input z R B k h
  have hF := GaussianNamedNaturalScale.exponential_input L k k one x fInput (le_refl _)
  have hG := GaussianBarnesCanonicalFactor.exponential_input z R B k (.andI h.andE₁ (.andI h.andE₂.andE₁ h.andE₂.andE₂.andE₁))
  have hb := GaussianBoundedIntegerExponential.integer_power_cross L k one x c two
    (.andI fInput (.andI (base_exponential z R B k h) b₂))
  have expo := GaussianGammaFoldedApproximantBalance.exponential_product_equivalent fullF constantF nameF
    S (exponentRadius R) (GaussianNameBounds.U nameF V) V W V hF hG
    (exponential_input nameF V (regular z R B k h)) (corrected_cross z R B k h)
  have eG := GaussianRadiusExponentialName.name_regular constantF (exponentRadius R) W hG
  have product := GaussianNameArithmetic.multiply_equivalent F constantF G G A P D D
    (GaussianRadiusExponentialName.name_regular fullF S V hF) (constant_regular P) eG eG
    (cross_to_diagonal _ _ _ _ hb) (cross_to_diagonal _ _ _ _ (cross_refl G D eG))
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ expo) product

theorem actual_exponentiated_Barnes_row_is_original_factor_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (source (var 0) (var 1) (var 2) (var 3) ⟶ crossEquivalent (Exp nameF) GaussianBarnesCanonicalFactor.nameF
        (expData (var 0) (var 1) (var 2) (var 3)) (GaussianBarnesCanonicalFactor.data (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (factor_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalLogFactor
