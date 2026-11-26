import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianNamedEulerUnitKernelAtDecay
import IPRADerivations.Analysis.Names.RationalGaussianNameEmbedding

/-!
# Original Euler power versus the unit kernel at a nearby rational node

An original rounded decay observation anchors the comparison. The
leading error consists of its frozen-image error and the compact
Lipschitz constant times the actual scalar node distance. Both output
programs keep their own independently requested observation precisions.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionNearbyKernel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (powerF powerData decayF decayData decayPoint)
open GaussianEulerUnitDecayInput (compactDenominator clock)
open GaussianNamedEulerUnitKernelAtDecay (frozenKernelData original_frozen_image_observations)
open GaussianEulerUnitKernelCompactRate (lipschitz)
open GaussianUnitIntervalInputDecoding (numerator denominator)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def observation (k a b E T : PTm n) : PTm n := ap2 decayF (clock k E T) (decayData a b)
def source (k z R B a b E T c d J X Y : PTm n) : Fm PTm n :=
  GaussianEulerUnitDecayInput.source a b E T ⋏
    (GaussianEulerExponentCompactBounds.source z R B J ⋏
      (le (compactDenominator E T) J ⋏ (GaussianEulerUnitCompactTimeBounds.source c d J ⋏
        (le one Y ⋏ RationalValueBounds.radius (fstT (observation k a b E T))
          (GaussianEuclideanDistanceName.fraction c d) X Y))))
def leadingNumerator (k R E T J X Y : PTm n) : PTm n :=
  lipschitz R (compactDenominator E T)*Y+lipschitz R J*X*unit k
def leadingDenominator (k Y : PTm n) : PTm n := Y*unit k

@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (k a b E T : PTm n) :
    Syn.subst σ (observation k a b E T) =
      observation (Syn.subst σ k) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [observation]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (k z R B a b E T c d J X Y : PTm n) :
    (source k z R B a b E T c d J X Y).subst σ = source (Syn.subst σ k) (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ E) (Syn.subst σ T)
      (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ J) (Syn.subst σ X) (Syn.subst σ Y) := by simp [source]
@[simp] theorem subst_leadingNumerator {m : ℕ} (σ : Fin n → PTm m) (k R E T J X Y : PTm n) :
    Syn.subst σ (leadingNumerator k R E T J X Y) =
      leadingNumerator (Syn.subst σ k) (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T)
        (Syn.subst σ J) (Syn.subst σ X) (Syn.subst σ Y) := by simp [leadingNumerator]
@[simp] theorem subst_leadingDenominator {m : ℕ} (σ : Fin n → PTm m) (k Y : PTm n) :
    Syn.subst σ (leadingDenominator k Y) = leadingDenominator (Syn.subst σ k) (Syn.subst σ Y) := by
  simp [leadingDenominator]

private theorem decoding_source_congr (u v G : PTm n) (e : Γ ⊢[PRAAx] u ≐ v)
    (h : Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source u G) :
    Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source v G := by
  have out := Prf.eqSubst (GaussianUnitIntervalInputDecoding.source (var 0) (var 1) : Fm PTm 2)
    ![u,G] ![v,G]
    (fun i => by
      fin_cases i
      exact e
      exact .eqRefl _)
  simp only [GaussianUnitIntervalInputDecoding.subst_source,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] at out
  exact out h

theorem original_observation_source (k a b E T : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUnitDecayInput.source a b E T) :
    Γ ⊢[PRAAx] GaussianUnitIntervalInputDecoding.source (observation k a b E T) (compactDenominator E T) :=
  decoding_source_congr _ _ _ (GaussianEulerUnitDecayInput.sample_at k a b E T)
    (GaussianEulerUnitDecayInput.observation_source k a b E T h)

theorem widen_time_compact (u v G J : PTm n) (h : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source u v G)
    (hw : Γ ⊢[PRAAx] le G J) : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source u v J := by
  refine .andI h.andE₁ (.andI (le_trans h.andE₂.andE₁ hw)
    (.andI (le_trans h.andE₂.andE₂.andE₁ (mul_le_mul_right u hw)) ?_))
  have base := h.andE₂.andE₂.andE₂
  have order := le_of_lt h.andE₁.andE₂
  have gap := natEq (eq_add_of_le hw)
  ipra_le sl base + 𝔞(LeanProofs.IPRA.PTm.monus J G)*sl order with (𝔞 v-𝔞 u)*gap

private theorem canonical_observation (k a b E T : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (observation k a b E T) :=
  GaussianRadiusExponentialName.sample_canonical GaussianGammaCanonicalExponent.constantF
    (GaussianNameBounds.U GaussianGammaCanonicalExponent.constantF (decayPoint a b)) (clock k E T) (decayPoint a b)

private theorem rational_anchor_distance (k a b E T c d J X Y : PTm n)
    (ht : Γ ⊢[PRAAx] GaussianEulerUnitDecayInput.source a b E T)
    (hr : Γ ⊢[PRAAx] GaussianEulerUnitCompactTimeBounds.source c d J) (hY : Γ ⊢[PRAAx] le one Y)
    (h : Γ ⊢[PRAAx] RationalValueBounds.radius (fstT (observation k a b E T))
      (GaussianEuclideanDistanceName.fraction c d) X Y) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.fraction (numerator (observation k a b E T)) (denominator (observation k a b E T)))
      (GaussianPositiveRationalLogarithm.fraction c d) X Y := by
  let v := observation k a b E T
  let u := GaussianEuclideanDistanceName.fraction c d
  let G := compactDenominator E T
  have hs := original_observation_source k a b E T ht
  have hc := canonical_observation (Γ := Γ) k a b E T
  have read : Γ ⊢[PRAAx] RationalGaussianEmbedding.embed (fstT v) ≐ v :=
    RationalGaussianEmbedding.canonical_axis_roundtrip v hc hs.andE₁
  have decoded := (GaussianUnitIntervalInputDecoding.fraction_recode v G hs).eqTrans
    (GaussianExponentialReference.recode_fixed v hc)
  have hd := le_trans hr.andE₁.andE₁ (le_of_lt hr.andE₁.andE₂)
  exact distance_congr (read.eqTrans decoded.eqSymm) (GaussianEulerDecayOrder.fraction_embedding c d hd)
    (.eqRefl _) (.eqRefl _) (RationalGaussianNameEmbedding.distance_from_radius (fstT v) u X Y hY h)

theorem original_diagonal (p k z R B a b E T c d J X Y : PTm n)
    (h : Γ ⊢[PRAAx] source k z R B a b E T c d J X Y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 powerF p (powerData z B a b))
      (ap2 GaussianEulerUnitSubstitutionKernel.nameF p (GaussianEulerUnitSubstitutionKernel.data z B c d))
      (diagonalNumerator (leadingNumerator k R E T J X Y) (leadingDenominator k Y) (two+two) p)
      (diagonalDenominator (leadingDenominator k Y) p) := by
  let G := compactDenominator E T
  let v := observation k a b E T
  let Q := unit k
  let P := unit p
  let D := Y*Q*P
  let L := lipschitz R G
  let M := lipschitz R J
  have hy := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have ht := h.andE₂.andE₂.andE₂.andE₁
  have hz := h.andE₂.andE₁
  have hu := unit_positive (Γ := Γ) k
  have hp := unit_positive (Γ := Γ) p
  have hd : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product _ _ hy hu) hp
  have close := original_frozen_image_observations p p k z R B a b E T h.andE₁ hz.andE₁ hz.andE₂.andE₂
  have left := distance_radius_mono _ _ _ _ ((L*P+two*Q)*Y) D
    (GaussianNamedInverseRate.denominator_positive Q p p hu) hd
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,D,L,P,Q]; ipra_ring)) close
  have anchor := GaussianUnitIntervalInputDecoding.decoded_source v G (original_observation_source k a b E T h.andE₁)
  have wider := widen_time_compact _ _ G J anchor h.andE₂.andE₂.andE₁
  have interval : Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactRate.input z R B (numerator v) (denominator v) c d J X Y :=
    .andI (.andI hz wider) (.andI (.andI hz ht) (.andI hy
      (rational_anchor_distance k a b E T c d J X Y h.andE₁ ht hy h.andE₂.andE₂.andE₂.andE₂.andE₂)))
  have kernel := GaussianEulerUnitKernelCompactRate.original_rate _ _ _ _ _ _ _ _ _ _ interval
  have diagonal := GaussianNamedInverseRate.diagonal_rate _ _ _ _ (M*X) Y p hy kernel
  have right := distance_radius_mono _ _ _ _ ((M*X*P+two*Y)*Q) D (positive_product _ _ hy hp) hd
    (le_of_eq_add (d := zero) (by dsimp only [D,M,P,Q]; ipra_ring)) diagonal
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [diagonalNumerator,leadingNumerator,leadingDenominator,L,M,G,P,Q]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd left right)

theorem original_rate (k z R B a b E T c d J X Y : PTm n) (h : Γ ⊢[PRAAx] source k z R B a b E T c d J X Y) : Γ ⊢[PRAAx]
    independentRate powerF GaussianEulerUnitSubstitutionKernel.nameF (powerData z B a b)
      (GaussianEulerUnitSubstitutionKernel.data z B c d) (leadingNumerator k R E T J X Y) (leadingDenominator k Y) := by
  have hy := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hz := h.andE₂.andE₁
  have ht := h.andE₂.andE₂.andE₂.andE₁
  have ha := (GaussianNamedEulerUnitKernelAtDecay.compact_time_domain a b E T h.andE₁).andE₁
  refine GaussianNamedLipschitzRate.independent_rate powerF GaussianEulerUnitSubstitutionKernel.nameF (powerData z B a b)
    (GaussianEulerUnitSubstitutionKernel.data z B c d) (leadingNumerator k R E T J X Y) (leadingDenominator k Y) (two+two)
    (positive_product _ _ hy (unit_positive k)) (GaussianEulerIntegrandName.power_regular z B a b (.andI hz.andE₁ ha))
    (GaussianEulerUnitSubstitutionKernel.name_regular z B c d (.andI hz.andE₁ ht.andE₁)) (.allI ?_)
  let s (u : PTm n) := Syn.shift u
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s k) (s z) (s R) (s B) (s a) (s b) (s E) (s T) (s c) (s d) (s J) (s X) (s Y) :=
    by simpa [Fm.shift,Syn.shift,s] using h.shift
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianEulerIntegrandName.subst_powerData,
    GaussianEulerUnitSubstitutionKernel.subst_data,subst_leadingNumerator,subst_leadingDenominator,PTm.subst_add,
    ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,s] using
    original_diagonal (var 0) (s k) (s z) (s R) (s B) (s a) (s b) (s E) (s T) (s c) (s d) (s J) (s X) (s Y) hs

theorem original_observations (p q k z R B a b E T c d J X Y : PTm n)
    (h : Γ ⊢[PRAAx] source k z R B a b E T c d J X Y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 powerF p (powerData z B a b))
      (ap2 GaussianEulerUnitSubstitutionKernel.nameF q (GaussianEulerUnitSubstitutionKernel.data z B c d))
      (rateNumerator (leadingNumerator k R E T J X Y) (leadingDenominator k Y) p q)
      (rateDenominator (leadingDenominator k Y) p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate k z R B a b E T c d J X Y h)

theorem actual_original_Euler_power_nearby_unit_kernel_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      independentRate powerF GaussianEulerUnitSubstitutionKernel.nameF (powerData (var 1) (var 3) (var 4) (var 5))
        (GaussianEulerUnitSubstitutionKernel.data (var 1) (var 3) (var 8) (var 9))
        (leadingNumerator (var 0) (var 2) (var 6) (var 7) (var 10) (var 11) (var 12)) (leadingDenominator (var 0) (var 12))) :=
  closeUniv 13 (.impI (original_rate _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitSubstitutionNearbyKernel
