import IPRADerivations.Analysis.Logarithm.Local.GaussianLocalLogarithmLinearRemainder
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerIntegrandName
import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianExponentialRadiusIndependence

/-!
# The actual beta-kernel logarithm and its compact quadratic rate

The input is the literal native negative numerator -a over bN. The
actual original local logarithm is multiplied by N using the existing
capped name. Its unchanged observation differs from -a/b by at most
a²/(b²N)+eps_p. A genuine fixed-time bound gives a radius independent
of N. This is a magnitude estimate for the logarithm step, not a signed
inequality or the final kernel/exponential comparison.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaKernelLogarithm

open_ipra
open ComplexLogarithmRemainder (neg scale oneCode normSq)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical canonical_unique positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalNaturalScale (natScale natScale_canonical natScale_represents)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def negativeNumerator (a : PTm n) : PTm n := ComplexLogarithmRemainder.neg (scale a oneCode)
def target (a b : PTm n) : PTm n := ofGaussian (negativeNumerator a) b
def source (a b N : PTm n) : Fm PTm n := le one b ⋏ (le one N ⋏ le (two*a) (b*N))
def localData (a b N : PTm n) : PTm n := GaussianLocalLogarithmName.data (negativeNumerator a) a (b*N)
def data (a b N : PTm n) : PTm n := GaussianNamedNaturalScale.data N N (localData a b N)
def nameF : PR 2 := GaussianNamedNaturalScale.nameF GaussianLocalLogarithmName.pointF
def observation (p a b N : PTm n) : PTm n := ap2 nameF p (data a b N)
def radius (T : PTm n) : PTm n := two*T+one
ipra_subst negativeNumerator
ipra_subst target
ipra_subst source
ipra_subst localData
ipra_subst data
ipra_subst observation
ipra_subst radius

theorem negative_norm (a : PTm n) : Γ ⊢[PRAAx] normSq (negativeNumerator a) ≐ a*a :=
  (ComplexLogarithmRemainder.normSq_neg _).eqTrans ((ComplexLogarithmRemainder.normSq_scale _ _).eqTrans
    ((congrMul (.eqRefl _) ComplexLogarithmRemainder.normSq_one).eqTrans (by ipra_ring)))

theorem local_source (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    GaussianLocalLogarithmName.source (negativeNumerator a) a (b*N) :=
  .andI (positive_product _ _ h.andE₁ h.andE₂.andE₁)
    (.andI (le_congr (negative_norm a).eqSymm (.eqRefl _) (le_refl _)) h.andE₂.andE₂)

theorem target_is_original_decay (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    target a b ≐ GaussianEulerIntegrandName.decayPoint a b :=
  canonical_unique _ _ (negativeNumerator a) b (ofGaussian_canonical _ _ hb) (GaussianRationalMetric.qnegative_canonical _) hb
    (ofGaussian_represents _ _ hb) (GaussianRationalMetric.qnegative_represents _ _ _ (ofGaussian_represents _ _ hb))

theorem scaled_linear_target (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    natScale N (ofGaussian (negativeNumerator a) (b*N)) ≐ target a b := by
  have hd := positive_product (Γ := Γ) _ _ h.andE₁ h.andE₂.andE₁
  exact canonical_unique _ _ (scale N (negativeNumerator a)) (b*N) (natScale_canonical _ _) (ofGaussian_canonical _ _ h.andE₁) hd
    (natScale_represents _ _ _ _ hd (ofGaussian_represents _ _ hd))
    (GaussianRationalHorner.represents_rescale _ _ _ N (ofGaussian_represents _ _ h.andE₁))

theorem name_regular (a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN nameF (data a b N) := by
  exact GaussianNamedNaturalScale.name_regular _ N N one (localData a b N)
    (GaussianExponentialRadiusIndependence.radius_one_input _ _
      (GaussianLocalLogarithmName.original_exponential_input _ _ _ (local_source a b N h))) (le_refl N)

/-- Exact requested observation error; the scaled quadratic term has
its true source rate a²/(b²N), with no limit or output premise. -/
theorem original_logarithm_rate (p a b N : PTm n) (h : Γ ⊢[PRAAx] source a b N) : Γ ⊢[PRAAx]
    distanceBounded (observation p a b N) (target a b) (a*a*unit p+b*b*N) (b*b*N*unit p) := by
  have old := GaussianLocalLogarithmLinearRemainder.scaled_linear_remainder p N N (negativeNumerator a) a (b*N)
    (local_source a b N h) (le_refl N)
  have db := positive_product (Γ := Γ) _ _ h.andE₁ h.andE₂.andE₁
  exact distance_radius_mono _ _ _ _ (a*a*unit p+b*b*N) (b*b*N*unit p)
    (positive_product _ _ (positive_product _ _ db db) (unit_positive p))
    (positive_product _ _ (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁) (unit_positive p))
    (le_of_eq_add (d := zero) (by ipra_ring))
    (distance_congr (.eqRefl _) (scaled_linear_target a b N h) (.eqRefl _) (.eqRefl _) old)

theorem target_bound (a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    bounded (target a b) T one :=
  GaussianGammaEulerHead.fraction_disk (negativeNumerator a) T b hb
    (le_congr (negative_norm a).eqSymm (.eqRefl _) (sq_le_sq ht))

/-- A common fixed-compact radius independent of the beta cutoff N. -/
theorem compact_observation_bound (p a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    bounded (observation p a b N) (radius T) one := by
  let D := b*b*N*unit p
  have dp : Γ ⊢[PRAAx] le one D := positive_product _ _
    (positive_product _ _ (positive_product _ _ h.andE₁ h.andE₁) h.andE₂.andE₁) (unit_positive p)
  have aN : Γ ⊢[PRAAx] le a (b*N) := le_trans (le_of_eq_add (d := a) (by ipra_ring)) h.andE₂.andE₂
  have quadratic : Γ ⊢[PRAAx] le (a*a) (T*b*b*N) :=
    le_congr (.eqRefl _) (by ipra_ring) (AnalyticNumberTheory.PhiLower.le_mul_mono ht aN)
  have first := mul_le_mul_right (unit p) quadratic
  have second : Γ ⊢[PRAAx] le (b*b*N) D :=
    le_congr (one_mul _) (mul_comm _ _) (mul_le_mul_right (b*b*N) (unit_positive p))
  have bound := add_le_add_right (T*D) (add_le_add₂ first second)
  have old := GaussianReconstructionRoots.norm_from_distance _ _ _ _ T one dp (le_refl one)
    (original_logarithm_rate p a b N h) (target_bound a b T h.andE₁ ht)
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ dp (le_refl one)) (le_refl one)
    (le_congr (by dsimp only [D]; ipra_ring) (by dsimp only [D,radius]; ipra_ring) bound) old

theorem actual_sample (p a b N : PTm n) : Γ ⊢[PRAAx]
    observation p a b N ≐ natScale N (ap2 GaussianLocalLogarithmName.pointF
      (GaussianNamedNaturalScale.clock p N) (localData a b N)) :=
  GaussianNamedNaturalScale.sample_at _ p N N (localData a b N)

theorem compact_input (a b N T : PTm n) (h : Γ ⊢[PRAAx] source a b N) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input nameF (radius T) (data a b N) := by
  refine .andI (name_regular a b N h) (.allI ?_)
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift a) (Syn.shift b) (Syn.shift N) := by
    simpa [Fm.shift,Syn.shift] using h.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift T*Syn.shift b) := by simpa [Fm.shift,Syn.shift] using ht.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,observation,Syn.shift,subst_data,subst_radius] using
    compact_observation_bound (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift N) (Syn.shift T) hs ts

theorem actual_beta_negative_target_original_decay_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶ target (var 0) (var 1) ≐ GaussianEulerIntegrandName.decayPoint (var 0) (var 1)) :=
  closeUniv 2 (.impI (target_is_original_decay _ _ Prf.hyp0))
theorem actual_beta_logarithm_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ GaussianEuclideanDistanceName.pointCN nameF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular _ _ _ Prf.hyp0))
theorem actual_beta_scaled_logarithm_sample_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (observation (var 0) (var 1) (var 2) (var 3) ≐ natScale (var 3) (ap2 GaussianLocalLogarithmName.pointF
      (GaussianNamedNaturalScale.clock (var 0) (var 3)) (localData (var 1) (var 2) (var 3)))) :=
  closeUniv 4 (actual_sample _ _ _ _)
theorem original_beta_logarithm_quadratic_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ distanceBounded (observation (var 0) (var 1) (var 2) (var 3))
      (target (var 1) (var 2)) (var 1*var 1*unit (var 0)+var 2*var 2*var 3) (var 2*var 2*var 3*unit (var 0))) :=
  closeUniv 4 (.impI (original_logarithm_rate _ _ _ _ Prf.hyp0))
theorem original_beta_logarithm_compact_exponential_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    ((source (var 0) (var 1) (var 2) ⋏ le (var 0) (var 3*var 1)) ⟶
      GaussianRadiusExponentialName.input nameF (radius (var 3)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (compact_input _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaKernelLogarithm
