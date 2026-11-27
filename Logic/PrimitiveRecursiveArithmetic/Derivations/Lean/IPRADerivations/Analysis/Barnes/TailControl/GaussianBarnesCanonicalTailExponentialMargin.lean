import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.Cofinal.GaussianBarnesCanonicalDerivativeTailBinding
import IPRADerivations.Analysis.Barnes.TailControl.GaussianBarnesCanonicalTailExponential
import IPRADerivations.Analysis.Geometry.DiskNames.GaussianExactDiskShrinking
import IPRADerivations.Analysis.Exponential.Names.LocalEstimates.GaussianNamedExponentialLinearRate

/-!
# A uniform small-increment source for the original Barnes tail exponential

The exact logarithmic increment has radius proportional to `H/B`.
Remove intrinsic sample slack by the original exact disk shrinker,
including at zero displacement. The sampler is equivalent to the
original difference and can enter the unit-disk exponential theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponentialMargin

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (add normSq)
open GaussianBarnesCanonicalDerivativeTailBinding
  (incrementF incrementData scaledDerivativeF scaledDerivativeData leadingDenominator base_source shifted_source)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianFastValueCut (rawEnvelope)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (multiply_at multiplyModulus)
open GaussianNameBounds (U)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalHorner (ofGaussian ofGaussian_represents positive_product qmul_canonical)
open GaussianRationalMetric (bounded bounded_of_cleared)
open GaussianRationalReciprocal (bound_congr bounded_product)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "L" => GaussianBarnesCanonicalLogCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalLogCofinal.data
local notation "T" => GaussianBarnesCanonicalTailExponential.nameF
local notation "td" => GaussianBarnesCanonicalTailExponential.data
local notation "D" => GaussianBarnesCanonicalDerivativeCofinal.nameF
local notation "slopeBound" => GaussianBarnesCanonicalDerivativeRow.boundNumerator
local notation "radius" => GaussianBarnesCanonicalFiniteLog.radius

def logarithmErrorGain (R : PTm n) : PTm n := num 3*R+num 342
def incrementGain (R : PTm n) : PTm n := slopeBound R+logarithmErrorGain R
def incrementNumerator (R H : PTm n) : PTm n := incrementGain R*H
def exponentialBound (R : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (radius R)
def exponentialUGain (R : PTm n) : PTm n := two*exponentialBound R+two

def input (z h R B H : PTm n) : Fm PTm n :=
  GaussianBarnesCanonicalDerivativeTailBinding.input z h R B H ⋏ le (incrementNumerator R H) B

abbrev smallF : PR 2 := GaussianExactDiskShrinking.nameF incrementF

def smallData (z h R B H : PTm n) : PTm n :=
  GaussianExactDiskShrinking.data (incrementData z h R B) (incrementNumerator R H) B two

@[simp] theorem subst_logarithmErrorGain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (logarithmErrorGain R) = logarithmErrorGain (Syn.subst σ R) := by simp [logarithmErrorGain]

@[simp] theorem subst_incrementGain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (incrementGain R) = incrementGain (Syn.subst σ R) := by simp [incrementGain]

@[simp] theorem subst_incrementNumerator {m : ℕ} (σ : Fin n → PTm m) (R H : PTm n) :
    Syn.subst σ (incrementNumerator R H) = incrementNumerator (Syn.subst σ R) (Syn.subst σ H) := by
  simp [incrementNumerator]

@[simp] theorem subst_exponentialBound {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (exponentialBound R) = exponentialBound (Syn.subst σ R) := by simp [exponentialBound]

@[simp] theorem subst_exponentialUGain {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (exponentialUGain R) = exponentialUGain (Syn.subst σ R) := by simp [exponentialUGain,two]

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z h R B H : PTm n) :
    (input z h R B H).subst σ = input (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) := by
  simp [input]

@[simp] theorem subst_smallData {m : ℕ} (σ : Fin n → PTm m) (z h R B H : PTm n) :
    Syn.subst σ (smallData z h R B H) =
      smallData (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ H) := by
  simp [smallData,two]

theorem derivative_sample_bound (p z R B : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 D p (ld z R B)) (slopeBound R) one := by
  let N := initial R
  let k := GaussianBarnesCanonicalDerivativeCofinal.length p R
  let A := slopeBound R
  have init := GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hs
  have w := GaussianBarnesCanonicalDerivativeTail.tail_bound z R B N k init
  have hN := initial_positive (Γ := Γ) R
  have fit : Γ ⊢[PRAAx] le (A*one) (A*N) :=
    mul_le_mul_left A hN
  exact bound_congr (GaussianBarnesCanonicalDerivativeCofinal.sample_at p z R B).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_radius_mono _ _ _ _ _ hN (le_refl one) fit w)

theorem scaled_sample_bound (p z h R B H : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeTailBinding.input z h R B H) :
    Γ ⊢[PRAAx] bounded (ap2 scaledDerivativeF p (scaledDerivativeData z h R B)) (H*slopeBound R) B := by
  let a := ofGaussian h B
  let x := ld z R B
  let t := GaussianFastValueCut.exponent (multiplyModulus constantF D a x) p
  have hz := base_source z h R B H hs
  have hB := hz.andE₁
  have hb : Γ ⊢[PRAAx] bounded a H B :=
    bounded_of_cleared _ _ _ _ _ hB hB (ofGaussian_represents h B hB)
      (le_congr (mul_comm _ _) (.eqRefl _) (mul_le_mul_right (B*B) hs.andE₂.andE₂.andE₁))
  have der := derivative_sample_bound t z R B hz
  have read := (multiply_at (Γ := Γ) constantF D a x p).eqTrans
    ((GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _)).eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr (constant_at t a) (.eqRefl _)))
  exact bound_congr read.eqSymm (.eqRefl _) (by ipra_ring)
    (bounded_product a (ap2 D t x) H B (slopeBound R) one hB (le_refl one) hb der)

theorem logarithm_increment_regular (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeTailBinding.input z h R B H) :
    Γ ⊢[PRAAx] pointCN incrementF (incrementData z h R B) :=
  GaussianNamedDifference.name_regular L L _ _
    (GaussianBarnesCanonicalLogCofinal.regular _ _ _ (shifted_source z h R B H hs))
    (GaussianBarnesCanonicalLogCofinal.regular _ _ _ (base_source z h R B H hs))

theorem increment_observation_bound (p z h R B H : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeTailBinding.input z h R B H) :
    Γ ⊢[PRAAx] bounded (ap2 incrementF p (incrementData z h R B))
      (incrementNumerator R H*unit p+two*B) (B*unit p) := by
  let A := logarithmErrorGain R
  let E := leadingDenominator R B
  let V := incrementNumerator R H
  let W := unit p
  let x := incrementData z h R B
  let y := scaledDerivativeData z h R B
  have h₀ := (base_source z h R B H hs).andE₁
  have hH := hs.andE₂.andE₂.andE₂.andE₂
  have hE := GaussianBarnesCanonicalDerivativeTailBinding.leading_denominator_positive R B h₀
  have hW := unit_positive (Γ := Γ) p
  have e : Γ ⊢[PRAAx] le (GaussianBarnesCanonicalDerivativeInterval.errorNumerator R H*B) ((A*H)*E) := by
    have left : Γ ⊢[PRAAx] le ((A*H)*(H*B)) ((A*H)*(B*B)) :=
      le_mul_mono (le_refl _) (mul_le_mul_right B hH)
    have right : Γ ⊢[PRAAx] le ((A*H)*(B*B)) ((A*H)*E) :=
      le_mul_mono (le_refl _) (le_congr (one_mul _) (mul_comm _ _)
        (mul_le_mul_right (B*B) (initial_positive R)))
    exact le_congr (by simp only [A,logarithmErrorGain,GaussianBarnesCanonicalDerivativeInterval.errorNumerator,
      GaussianBarnesCanonicalDerivativeBinding.boundNumerator]; ipra_ring) (.eqRefl _)
      (le_trans left right)
  have fitRate := GaussianNamedRateRadius.weaken incrementF scaledDerivativeF x y _ E (A*H) B hE h₀ e
    (GaussianBarnesCanonicalDerivativeTailBinding.rate z h R B H hs)
  have difference := GaussianNamedInverseRate.diagonal_rate incrementF scaledDerivativeF x y (A*H) B p h₀ fitRate
  have numeratorBound := GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _
    (positive_product _ _ h₀ hW) h₀ difference (scaled_sample_bound p z h R B H hs)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ h₀ hW) h₀)
    (positive_product _ _ h₀ hW) (le_of_eq_add (d := zero) (by dsimp only [V,W,A]; unfold incrementNumerator incrementGain; ipra_ring))
    numeratorBound

theorem increment_envelope (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeTailBinding.input z h R B H) :
    Γ ⊢[PRAAx] rawEnvelope incrementF (incrementData z h R B) (incrementNumerator R H) B two := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeTailBinding.input (sh z) (sh h) (sh R) (sh B) (sh H) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.shift
  simpa only [rawEnvelope,Syn.shift,sh,GaussianBarnesCanonicalDerivativeTailBinding.subst_incrementData,
    subst_incrementNumerator,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,two] using
    increment_observation_bound (var 0) (sh z) (sh h) (sh R) (sh B) (sh H) h'

theorem small_cross (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] crossEquivalent smallF incrementF (smallData z h R B H) (incrementData z h R B) :=
  GaussianExactDiskShrinking.cross_equivalent incrementF _ _ _ _ (base_source z h R B H hs.andE₁).andE₁
    (logarithm_increment_regular z h R B H hs.andE₁) (increment_envelope z h R B H hs.andE₁)

theorem small_source (z h R B H : PTm n) (hs : Γ ⊢[PRAAx] input z h R B H) :
    Γ ⊢[PRAAx] GaussianNamedExponentialLinearRate.source smallF (smallData z h R B H) (incrementNumerator R H) B := by
  have hb := (base_source z h R B H hs.andE₁).andE₁
  have hx := logarithm_increment_regular z h R B H hs.andE₁
  have env := increment_envelope z h R B H hs.andE₁
  refine .andI hb (.andI hs.andE₂ (.andI (GaussianExactDiskShrinking.name_regular _ _ _ _ _ hb hx env) (.allI ?_)))
  let sh (t : PTm n) := Syn.shift t
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  have hb' : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,sh,Fm.shift,Syn.shift,one] using hb.shift
  have h' : Δ ⊢[PRAAx] GaussianBarnesCanonicalDerivativeTailBinding.input (sh z) (sh h) (sh R) (sh B) (sh H) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hs.andE₁.shift
  have bounds := GaussianExactDiskShrinking.sample_bound incrementF p _ _ _ _ hb'
    (increment_envelope (sh z) (sh h) (sh R) (sh B) (sh H) h')
  have canonical := GaussianExactDiskShrinking.sample_canonical (Γ := Δ) incrementF p (incrementData (sh z) (sh h) (sh R) (sh B))
    (incrementNumerator (sh R) (sh H)) (sh B) two
  simpa only [GaussianNamedExponentialLinearRate.smallSamples,Syn.shift,sh,p,subst_smallData,subst_incrementNumerator,
    GaussianExactDiskShrinking.sample,smallData,GaussianExactDiskShrinking.subst_data,
    GaussianBarnesCanonicalDerivativeTailBinding.subst_incrementData,two,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using Prf.andI bounds canonical

theorem exponential_sample_bound (p z R B : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B) :
    Γ ⊢[PRAAx] bounded (ap2 T p (td z R B)) (exponentialBound R) one := by
  let r := radius R
  let x := ld z R B
  have h := GaussianBarnesCanonicalTailExponential.log_input z R B hs
  have b := GaussianPositiveExponentialMajorant.disk_bound (GaussianRadiusExponentialName.query L r p x) r
    (GaussianRadiusExponentialName.index r p) (GaussianRadiusExponentialName.query_bound L r x p h)
  exact bound_congr (GaussianRadiusExponentialName.sample_at L r p x).eqSymm (.eqRefl _) (.eqRefl _) b

theorem exponential_samples_bound (z R B : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B) :
    Γ ⊢[PRAAx] GaussianNamedMultiplyRate.sampleBound T (td z R B) (exponentialBound R) := by
  refine .allI ?_
  let sh (t : PTm n) := Syn.shift t
  have h' : Γ.map Fm.shift ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh] using hs.shift
  simpa only [GaussianNamedMultiplyRate.sampleBound,Syn.shift,sh,GaussianBarnesCanonicalTailExponential.subst_data,
    subst_exponentialBound] using exponential_sample_bound (var 0) (sh z) (sh R) (sh B) h'

theorem exponential_U_bound (z R B : PTm n) (hs : Γ ⊢[PRAAx] GaussianBarnesCanonicalLogCofinal.source z R B) :
    Γ ⊢[PRAAx] le (U T (td z R B)) (exponentialUGain R) := by
  let q := ap2 T zero (td z R B)
  let C := GaussianRationalL1.qL1 q
  let d := RationalSupMetric.denominatorOf C
  let a := RationalIntegerNormalization.positivePart (RationalSupMetric.numeratorOf C)
  let M := two*exponentialBound R
  have hd := RationalArgmin.denominator_positive (Γ := Γ) C
  have order := GaussianRationalL1Algebra.qL1_of_bounded q (exponentialBound R) one (le_refl one)
    (exponential_sample_bound zero z R B hs)
  have clear := GaussianRationalMetric.comparison_to_cleared C (GaussianEuclideanDistanceName.fraction M one) a M d one
    (GaussianGeneralFTAConstants.l1_natural_representation q) (GaussianEuclideanDistanceName.fraction_represents M one (le_refl _))
    order
  have numle : Γ ⊢[PRAAx] le a (d*M) := le_congr (one_mul _) (mul_comm _ _) clear
  have ceiling := GaussianDescentClockArithmetic.ceiling_least a d M hd numle
  exact add_le_add_right two ceiling

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalTailExponentialMargin
