import IPRADerivations.Analysis.Exponential.Names.Evaluators.GaussianUnitDiskExponentialName
import IPRADerivations.Analysis.Logarithm.FiniteSeries.Composition.GaussianFiniteLogarithmCompositionName

/-!
# The ORIGINAL local logarithm observations as a Gaussian unit-disk name

The samples are exactly ofGaussian(ComplexLogarithmName.observation p,
2^(p+4)), with no replacement or precision shift. Finite source C3 gives
the original finite logarithm norm at most3/4. The actual observation
rounding error is at most4/2^(p+4), hence at most1/4. Their true Euclidean
triangle gives unit-disk samples, including precision zero and radius zero.
The original discrepancy certificate also yields genuine pointCN.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianLocalLogarithmName

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianRationalHorner (ofGaussian ofGaussian_represents represents positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_from_later_observations)
open GaussianEuclideanDistanceName (pointCN)
open ComplexLogarithmName (observation finiteNumerator finiteDenominator)
open DyadicComplexLogarithm (unit precision)
open GammaCanonicalFactors (factorNumerator factorDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (z R N : PTm n) : Fm PTm n := le one N ⋏
  (ComplexLogarithmRemainder.bounded z R ⋏ le (two*R) N)
def value (p z R N : PTm n) : PTm n := ofGaussian (observation p z R N) (unit p)
ipra_subst source
ipra_subst value

theorem unit_positive (p : PTm n) : Γ ⊢[PRAAx] le one (unit p) := GaussianFactorBudget.power_positive _ _ (le_succ_self one)
theorem four_positive : Γ ⊢[PRAAx] le one (num 4 : PTm n) := le_of_eq_add (d := num 3) (by ipra_ring)
theorem unit_factor (p : PTm n) : Γ ⊢[PRAAx] unit p ≐ GaussianCoefficientNameBounds.unit p*num 16 :=
  (pw_add two p (num 4)).eqTrans (congrMul (.eqRefl _) GaussianFiniteLogarithmDyadicTail.two_four)
theorem unit_lower (p : PTm n) : Γ ⊢[PRAAx] le (num 16) (unit p) :=
  le_congr (one_mul _) (unit_factor p).eqSymm
    (le_mul_mono (GaussianCoefficientNameBounds.unit_positive p) (le_refl _))

theorem local_factor_bound (z R N L : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    bounded (GammaLogarithmFactorBridge.localFactor z N L) one (num 4) := by
  have hn := h.andE₁
  have hd := GammaCanonicalFactors.factorDenominator_positive N L hn
  have native := GammaCanonicalFactors.finite_factor_bound z N R L h.andE₂.andE₁ hn h.andE₂.andE₂
  have cleared : Γ ⊢[PRAAx] le
      ((N*N)*(N*N)*ComplexLogarithmRemainder.normSq (factorNumerator z N L))
      (((R*R)*(R*R))*(factorDenominator N L*factorDenominator N L)) :=
    le_congr (ComplexLogarithmRemainder.normSq_scale _ _) (by ipra_ring) native
  have rational : Γ ⊢[PRAAx] bounded (GammaLogarithmFactorBridge.localFactor z N L) (R*R) (N*N) :=
    GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hd (positive_product _ _ hn hn)
    (ofGaussian_represents _ _ hd) cleared
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ hn hn) four_positive
    (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono h.andE₂.andE₂ h.andE₂.andE₂)) rational

theorem finite_sample_bound (z R N L : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    bounded (GaussianFiniteLogarithmSampler.sample z N L) (num 3) (num 4) := by
  have hw := GaussianFiniteLogarithmCompositionName.original_half_disk z R N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂
  have raw := bounded_sum _ _ _ _ _ _ (le_succ_self one) four_positive hw (local_factor_bound z R N L h)
  have changed := bound_congr (GammaLogarithmFactorBridge.sum_is_original_sample z N L h.andE₁) (.eqRefl _) (.eqRefl _) raw
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_succ_self one) four_positive) four_positive
    (le_of_eq_add (d := zero) (by ipra_ring)) changed

/-- The real original rounding certificate, interpreted in the original
Gaussian-rational metric at its computed positive common denominator. -/
theorem observation_distance (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (value p z R N) (GaussianFiniteLogarithmSampler.sample z N (precision p)) (num 4) (unit p) := by
  let D := finiteDenominator N (precision p)
  let U := unit p
  let O := observation p z R N
  let H := finiteNumerator z N (precision p)
  let E := U*D
  have d := ComplexLogarithmName.finite_positive N (precision p) hN
  have u := unit_positive (Γ := Γ) p
  have ep := positive_product (Γ := Γ) U D u d
  have left := GaussianRationalSyntheticDivision.rescale_to (value p z R N) O U D E (ofGaussian_represents O U u) (.eqRefl _)
  have right := GaussianRationalSyntheticDivision.rescale_to (GaussianFiniteLogarithmSampler.sample z N (precision p)) H D U E
    (ofGaussian_represents H D d) (mul_comm _ _)
  have rep : Γ ⊢[PRAAx] represents (qsub (value p z R N) (GaussianFiniteLogarithmSampler.sample z N (precision p)))
      (ComplexLogarithmName.observationError p z R N) E := by
    simpa only [ComplexLogarithmName.observationError,GaussianRootAlgebra.sub,D,U,O,H] using
      GaussianRationalMetric.qsub_represents _ _ _ _ _ ep left right
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ ep u rep
    (le_congr (.eqRefl _) (by dsimp [E,D,U]; ipra_ring)
      (le_mul_mono (le_refl (U*U)) (ComplexLogarithmName.observation_error_bound p z R N hN)))

/-- Actual unshifted old observations lie in the Euclidean unit disk;
the bound uses finite C3 plus true rounding distance, not an L1 disk. -/
theorem value_unit_disk (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    bounded (value p z R N) one one := by
  have err := distance_radius_mono _ _ _ _ _ _ (unit_positive p) four_positive
    (le_congr (by ipra_ring) (one_mul _).eqSymm (unit_lower p)) (observation_distance p z R N h.andE₁)
  have total := GaussianReconstructionRoots.norm_from_distance _ _ one (num 4) (num 3) (num 4)
    four_positive four_positive err (finite_sample_bound z R N (precision p) h)
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (positive_product _ _ four_positive four_positive) (le_refl _)
    (le_of_eq_add (d := zero) (by ipra_ring)) total

theorem ordered_distance (p k z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (value (p+k) z R N) (value p z R N) (num 9) (unit p) := by
  have up := unit_positive (Γ := Γ) p
  have uq := unit_positive (Γ := Γ) (p+k)
  have early := GaussianRationalSyntheticDivision.rescale_to (value p z R N) (observation p z R N) (unit p)
    (pw two k) (unit (p+k)) (ofGaussian_represents _ _ up) (DyadicComplexLogarithm.unit_add p k).eqSymm
  have later := ofGaussian_represents (Γ := Γ) (observation (p+k) z R N) (unit (p+k)) uq
  have rep : Γ ⊢[PRAAx] represents (qsub (value (p+k) z R N) (value p z R N))
      (ComplexLogarithmName.discrepancy p k z R N) (unit (p+k)) := by
    simpa only [value,ComplexLogarithmName.discrepancy,GaussianRootAlgebra.sub] using
      GaussianRationalMetric.qsub_represents _ _ _ _ _ uq later early
  have radius : Γ ⊢[PRAAx] (unit p*unit p)*((num 9*pw two k)*(num 9*pw two k)) ≐
      (num 9*num 9)*(unit (p+k)*unit (p+k)) := by
    have e := natEq (DyadicComplexLogarithm.unit_add (Γ := Γ) p k)
    apply deriveNat; ipra_simps; rw [e]; ring
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ uq up rep
    (le_congr (.eqRefl _) radius
      (le_mul_mono (le_refl (unit p*unit p))
        (ComplexLogarithmName.regular_bound p k z R N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)))

theorem ordered_unit_distance (p k z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (value (p+k) z R N) (value p z R N) one (GaussianCoefficientNameBounds.unit p) := by
  have radius : Γ ⊢[PRAAx] le (num 9*GaussianCoefficientNameBounds.unit p) (one*unit p) := by
    refine le_of_eq_add (d := num 7*GaussianCoefficientNameBounds.unit p) ?_
    have e := natEq (unit_factor (Γ := Γ) p)
    apply deriveNat; ipra_simps; rw [e]; ring
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (GaussianCoefficientNameBounds.unit_positive p)
    radius (ordered_distance p k z R N h)

theorem value_congr_precision {p q : PTm n} (z R N : PTm n) (h : Γ ⊢[PRAAx] p ≐ q) : Γ ⊢[PRAAx]
    value p z R N ≐ value q z R N := by
  ipra_congr (value (var 0) (var 1) (var 2) (var 3) : PTm 4) with [h, .eqRefl z, .eqRefl R, .eqRefl N]

theorem later_distance (s t z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) (hst : Γ ⊢[PRAAx] le s t) : Γ ⊢[PRAAx]
    distanceBounded (value t z R N) (value s z R N) one (GaussianCoefficientNameBounds.unit s) :=
  distance_congr (value_congr_precision z R N (eq_add_of_le hst).eqSymm) (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (ordered_unit_distance s (monus t s) z R N h)

theorem value_regularity (s t z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (value s z R N) (value t z R N)
      (GaussianCoefficientNameBounds.unit s+GaussianCoefficientNameBounds.unit t)
      (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t) :=
  distance_from_later_observations _ _ s t
    (later_distance s t z R N h.wk Prf.hyp0)
    (later_distance t s z R N h.wk Prf.hyp0)

/-! The original observation code remains literal inside the PR2 sampler.
Persistent data packs exactly(z,(R,N)); no alternate finite sampler. -/
def data (z R N : PTm n) : PTm n := pairT z (pairT R N)
def pointTerm (p x : PTm n) : PTm n := value p (fstT x) (fstT (sndT x)) (sndT (sndT x))
def pointF : PR 2 := PTm.toPR (pointTerm (var 0) (var 1))
def point (p z R N : PTm n) : PTm n := ap2 pointF p (data z R N)
ipra_subst data
ipra_subst pointTerm
ipra_subst point

theorem point_at (p z R N : PTm n) : Γ ⊢[PRAAx] point p z R N ≐ value p z R N := by
  have prog : Γ ⊢[PRAAx] point p z R N ≐ pointTerm p (data z R N) := by
    simpa [point,pointF,ap2] using toPR_eq (Γ := Γ) (pointTerm (var 0) (var 1) : PTm 2) ![p,data z R N]
  refine prog.eqTrans ?_
  simpa only [pointTerm,subst_value,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons] using
    Prf.eqCongr (value (var 0) (var 1) (var 2) (var 3) : PTm 4)
      (σ := ![p,fstT (data z R N),fstT (sndT (data z R N)),sndT (sndT (data z R N))]) (σ' := ![p,z,R,N])
      (fun i => by
        fin_cases i
        · exact .eqRefl _
        · exact fst_pair _ _
        · exact (snd_pair _ _).fstE
        · exact (snd_pair _ _).sndE)

theorem point_canonical (p z R N : PTm n) : Γ ⊢[PRAAx] GaussianRationalHorner.canonical (point p z R N) :=
  GaussianRationalHorner.canonical_congr (point_at p z R N) (GaussianRationalHorner.ofGaussian_canonical _ _ (unit_positive p))
theorem point_unit_disk (p z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx] bounded (point p z R N) one one :=
  bound_congr (point_at p z R N).eqSymm (.eqRefl _) (.eqRefl _) (value_unit_disk p z R N h)
theorem point_rounding_distance (p z R N : PTm n) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (point p z R N) (GaussianFiniteLogarithmSampler.sample z N (precision p)) (num 4) (unit p) :=
  distance_congr (point_at p z R N).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (observation_distance p z R N hN)
theorem point_regularity (s t z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    distanceBounded (point s z R N) (point t z R N)
      (GaussianCoefficientNameBounds.unit s+GaussianCoefficientNameBounds.unit t)
      (GaussianCoefficientNameBounds.unit s*GaussianCoefficientNameBounds.unit t) :=
  distance_congr (point_at s z R N).eqSymm (point_at t z R N).eqSymm (.eqRefl _) (.eqRefl _) (value_regularity s t z R N h)

theorem name_regular (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx] pointCN pointF (data z R N) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift N)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,point,Syn.shift,subst_data] using
    point_regularity (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift N)) hs

theorem name_unit_samples (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    GaussianUnitDiskExponentialName.unitSamples pointF (data z R N) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift N) := by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [GaussianUnitDiskExponentialName.unitSamples,point,Syn.shift,subst_data] using
    point_unit_disk (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift N) hs

theorem original_exponential_input (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    GaussianUnitDiskExponentialName.input pointF (data z R N) := .andI (name_regular z R N h) (name_unit_samples z R N h)
theorem original_exponential_name_regular (z R N : PTm n) (h : Γ ⊢[PRAAx] source z R N) : Γ ⊢[PRAAx]
    pointCN (GaussianUnitDiskExponentialName.nameF pointF) (data z R N) :=
  GaussianUnitDiskExponentialName.name_regular pointF _ (original_exponential_input z R N h)

theorem original_finite_local_factor_quarter_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ bounded (GammaLogarithmFactorBridge.localFactor (var 0) (var 2) (var 3)) one (num 4)) :=
  closeUniv 4 (.impI (local_factor_bound _ _ _ _ Prf.hyp0))
theorem original_finite_logarithm_three_quarters_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 0) (var 1) (var 2) ⟶ bounded (GaussianFiniteLogarithmSampler.sample (var 0) (var 2) (var 3)) (num 3) (num 4)) :=
  closeUniv 4 (.impI (finite_sample_bound _ _ _ _ Prf.hyp0))
theorem original_logarithm_observation_gaussian_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (point (var 0) (var 1) (var 2) (var 3) ≐ ofGaussian (observation (var 0) (var 1) (var 2) (var 3)) (unit (var 0))) :=
  closeUniv 4 (point_at _ _ _ _)
theorem original_logarithm_observation_canonical_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (GaussianRationalHorner.canonical (point (var 0) (var 1) (var 2) (var 3))) := closeUniv 4 (point_canonical _ _ _ _)
theorem original_logarithm_rounding_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 3) ⟶ distanceBounded (point (var 0) (var 1) (var 2) (var 3))
      (GaussianFiniteLogarithmSampler.sample (var 1) (var 3) (precision (var 0))) (num 4) (unit (var 0))) :=
  closeUniv 4 (.impI (point_rounding_distance _ _ _ _ Prf.hyp0))
theorem original_half_disk_logarithm_observation_unit_disk_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶ bounded (point (var 0) (var 1) (var 2) (var 3)) one one) :=
  closeUniv 4 (.impI (point_unit_disk _ _ _ _ Prf.hyp0))
theorem original_logarithm_ordered_gaussian_distance_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 2) (var 3) (var 4) ⟶ distanceBounded (value (var 0+var 1) (var 2) (var 3) (var 4))
      (value (var 0) (var 2) (var 3) (var 4)) (num 9) (unit (var 0))) :=
  closeUniv 5 (.impI (ordered_distance _ _ _ _ _ Prf.hyp0))
theorem original_half_disk_logarithm_gaussian_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ pointCN pointF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_regular _ _ _ Prf.hyp0))
theorem original_half_disk_logarithm_unit_samples_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ GaussianUnitDiskExponentialName.unitSamples pointF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (name_unit_samples _ _ _ Prf.hyp0))
theorem original_half_disk_logarithm_exponential_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ GaussianUnitDiskExponentialName.input pointF (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_exponential_input _ _ _ Prf.hyp0))
theorem original_half_disk_logarithm_exponential_regular_name_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ pointCN (GaussianUnitDiskExponentialName.nameF pointF) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (original_exponential_name_regular _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianLocalLogarithmName
