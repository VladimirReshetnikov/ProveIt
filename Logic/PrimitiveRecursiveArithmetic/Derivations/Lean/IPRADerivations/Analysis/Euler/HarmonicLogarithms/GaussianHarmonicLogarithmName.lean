import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianPositiveRationalLogarithmSign
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianSignedNameExponentialOrder
import IPRADerivations.Analysis.RationalArithmetic.OrderBounds.RationalClosure
import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianCompactLogarithmBounds

/-!
# A genuinely ordered representative of the original rational logarithm

Actual finite harmonic intervals are sampled at the original mesh after
a fixed numerical shift. Their proved original sample errors derive
pointCN and independent equivalence to the unchanged original logarithm.
The actual interval samples have exact real-coordinate order on either
side of one, rather than a sign assertion about rounded original samples.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianHarmonicLogarithmName

open_ipra
open GaussianPositiveRationalLogarithm (source logF name_regular)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalHorner (positive_product qzero)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def clock (p : PTm n) : PTm n := p+num 9
def scale : PTm n := pw two (num 9)
def observation (p a b : PTm n) : PTm n := RationalGaussianEmbedding.embed
  (RationalHarmonicInterval.interval a b (GammaEulerConstantName.mesh (clock p)))
def data (a b : PTm n) : PTm n := pairT a b
def nameF : PR 2 := PTm.toPR (observation (var 0) (fstT (var 1)) (sndT (var 1)))
def sample (p a b : PTm n) : PTm n := ap2 nameF p (data a b)

ipra_subst clock
ipra_subst observation [GammaEulerConstantName.mesh, GammaEulerConstantName.unit]
ipra_subst data
ipra_subst sample

theorem sample_at (p a b : PTm n) : Γ ⊢[PRAAx] sample p a b ≐ observation p a b := by
  simpa only [sample, nameF, data, subst_observation, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    (toPR_pair_eq (Γ := Γ) (observation (var 0) (var 1) (var 2)) p a b)

theorem clock_unit (p : PTm n) : Γ ⊢[PRAAx] unit (clock p) ≐ unit p*scale := pw_add two p (num 9)
theorem scale_nine : Γ ⊢[PRAAx] le (num 9) (scale : PTm n) :=
  le_trans (le_succ_self _) (RationalClosure.succ_le_two_pow (num 9))

theorem original_sample_error (p a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.sample (clock p) a b) (sample p a b) (num 8) (unit (clock p)) :=
  distance_congr (.eqRefl _) (sample_at p a b).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianPositiveRationalLogarithmProperness.sample_interval_error (clock p) a b hs)

theorem independent_original (p q a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (GaussianPositiveRationalLogarithm.sample p a b) (sample q a b)
      (unit p+unit q) (unit p*unit q) := by
  let V := unit (clock q)
  have old := GaussianNameEquivalence.point_at logF (GaussianPositiveRationalLogarithm.data a b) p (clock q) (name_regular a b hs)
  have err := distance_radius_mono _ _ _ _ (num 8*unit p) (unit p*V)
    (unit_positive (clock q)) (positive_product _ _ (unit_positive p) (unit_positive (clock q)))
    (le_of_eq_add (d := zero) (by dsimp [V]; ipra_ring)) (original_sample_error q a b hs)
  have joined := distance_triangle_same _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive (clock q))) old err
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive (clock q)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) _ joined
  have eq := natEq (clock_unit (Γ := Γ) q)
  refine le_of_eq_add (d := unit p*unit p*unit q*PTm.monus scale (num 9)) ?_
  have es := natEq (eq_add_of_le (scale_nine (Γ := Γ)))
  apply deriveNat
  try dsimp only [V]
  ipra_simps
  rw [eq]
  rw [es]
  ring

theorem cross_original (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    crossEquivalent logF nameF (GaussianPositiveRationalLogarithm.data a b) (data a b) := by
  refine .allI (.allI ?_)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) :=
    by simpa [Fm.shift,Syn.shift] using hs.shift.shift
  simpa only [crossEquivalent,Syn.shift,GaussianPositiveRationalLogarithm.subst_data,subst_data,sample,GaussianPositiveRationalLogarithm.sample] using
    independent_original (var 1) (var 0) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) ss

theorem regular_observations (p q a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p a b) (sample q a b) (unit p+unit q) (unit p*unit q) := by
  let U := unit (clock p)
  let V := unit (clock q)
  have positive := positive_product (Γ := Γ) _ _ (unit_positive (clock p)) (unit_positive (clock q))
  have left := distance_radius_mono _ _ _ _ (num 8*V) (U*V) (unit_positive (clock p)) positive
    (le_of_eq_add (d := zero) (by dsimp [U,V]; ipra_ring))
    (distance_symmetric _ _ _ _ (unit_positive (clock p)) (original_sample_error p a b hs))
  have right := distance_radius_mono _ _ _ _ (num 8*U) (U*V) (unit_positive (clock q)) positive
    (le_of_eq_add (d := zero) (by dsimp [U,V]; ipra_ring)) (original_sample_error q a b hs)
  have middle := GaussianNameEquivalence.point_at logF (GaussianPositiveRationalLogarithm.data a b)
    (clock p) (clock q) (name_regular a b hs)
  have joined := distance_triangle_same _ _ _ _ _ _ positive (distance_triangle_same _ _ _ _ _ _ positive left middle) right
  apply distance_radius_mono _ _ _ _ _ _ positive (positive_product _ _ (unit_positive p) (unit_positive q)) _ joined
  have ep := natEq (clock_unit (Γ := Γ) p)
  have eq := natEq (clock_unit (Γ := Γ) q)
  refine le_of_eq_add (d := scale*unit p*unit q*(unit p+unit q)*PTm.monus scale (num 9)) ?_
  have es := natEq (eq_add_of_le (scale_nine (Γ := Γ)))
  apply deriveNat
  dsimp only [U,V]
  ipra_simps
  rw [ep,eq]
  rw [es]
  ring

theorem name_regular (a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) : Γ ⊢[PRAAx] pointCN nameF (data a b) := by
  refine .allI (.allI ?_)
  have ss : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) :=
    by simpa [Fm.shift,Syn.shift] using hs.shift.shift
  simpa only [GaussianEuclideanDistanceName.pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,
    Syn.shift,subst_data,sample] using regular_observations (var 1) (var 0) (Syn.shift (Syn.shift a)) (Syn.shift (Syn.shift b)) ss

theorem sample_real (p a b : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (sample p a b) ⋏ RationalGaussianEmbedding.axis (sample p a b) :=
  .andI (GaussianRationalHorner.canonical_congr (sample_at p a b) (RationalGaussianEmbedding.embed_canonical _))
    (RationalGaussianEmbedding.axis_congr (sample_at p a b).eqSymm (RationalGaussianEmbedding.embed_axis _))

theorem real_samples (a b : PTm n) : Γ ⊢[PRAAx] GaussianSignedNameExponentialOrder.realSamples nameF (data a b) := by
  refine .allI ?_
  simpa only [GaussianSignedNameExponentialOrder.realSamples,Syn.shift,subst_data,sample] using
    sample_real (Γ := Γ.map Fm.shift) (var 0) (Syn.shift a) (Syn.shift b)

theorem below_one_samples (a b : PTm n) (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx]
    GaussianNamedPositiveExponentialOrder.sampleOrder nameF GaussianGammaCanonicalExponent.constantF (data a b) qzero := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) := by simpa [Fm.shift,Syn.shift] using h.shift
  have er := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ.map Fm.shift) (var 0) (qzero : PTm (n+1)))).eqTrans
    RationalGaussianRealPart.real_zero
  simpa only [GaussianNamedPositiveExponentialOrder.sampleOrder,Syn.shift,subst_data,GaussianRationalHorner.subst_qzero,sample] using
    RationalArgmin.rationalLE_congr (congrFst (sample_at (var 0) (Syn.shift a) (Syn.shift b))).eqSymm er.eqSymm
      (GaussianPositiveRationalLogarithmSign.embedded_interval_nonpositive _ _ _ hs)

theorem above_one_samples (a b : PTm n) (h : Γ ⊢[PRAAx] le b a) : Γ ⊢[PRAAx]
    GaussianNamedPositiveExponentialOrder.sampleOrder GaussianGammaCanonicalExponent.constantF nameF qzero (data a b) := by
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift b) (Syn.shift a) := by simpa [Fm.shift,Syn.shift] using h.shift
  have er := (congrFst (GaussianGammaCanonicalExponent.constant_at (Γ := Γ.map Fm.shift) (var 0) (qzero : PTm (n+1)))).eqTrans
    RationalGaussianRealPart.real_zero
  simpa only [GaussianNamedPositiveExponentialOrder.sampleOrder,Syn.shift,subst_data,GaussianRationalHorner.subst_qzero,sample] using
    RationalArgmin.rationalLE_congr er.eqSymm (congrFst (sample_at (var 0) (Syn.shift a) (Syn.shift b))).eqSymm
      (GaussianPositiveRationalLogarithmSign.embedded_interval_nonnegative _ _ _ hs)

def radius (E T : PTm n) : PTm n := GaussianCompactLogarithmBounds.radius E T+one
ipra_subst radius

theorem compact_sample_bound (p a b E T : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (sample p a b) (radius E T) one := by
  let J := GaussianCompactLogarithmBounds.radius E T
  let U := unit (clock p)
  let x := GaussianPositiveRationalLogarithm.sample (clock p) a b
  let y := sample p a b
  have old := GaussianCompactLogarithmBounds.sample_bound (clock p) a b E T hE ht
  have error := original_sample_error p a b ht.andE₁
  have sum := GaussianRationalReciprocal.bounded_sum x (GaussianRationalMetric.qsub y x) J one (num 8) U
    (le_refl one) (unit_positive (clock p)) old (distance_symmetric _ _ _ _ (unit_positive (clock p)) error)
  have exactPoint := GaussianRationalLinearProduct.add_sub_right (Γ := Γ) x y (sample_real p a b).andE₁
  have weak : Γ ⊢[PRAAx] le (num 8) U :=
    le_trans (le_succ_self (num 8)) (le_congr (one_mul (num 9)) (clock_unit p).eqSymm
      (AnalyticNumberTheory.PhiLower.le_mul_mono (unit_positive p) scale_nine))
  apply GaussianCoefficientNameBounds.bounded_radius_mono y (J*U+num 8) U (radius E T) one (unit_positive (clock p)) (le_refl one) _
    (GaussianRationalReciprocal.bound_congr exactPoint (by ipra_ring) (one_mul _) sum)
  exact le_congr (by ipra_ring) (by dsimp only [radius,J]; ipra_ring) (add_le_add_right (J*U) weak)

theorem common_input (a b E T : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input nameF (radius E T) (data a b) := by
  refine .andI (name_regular a b ht.andE₁) (.allI ?_)
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hE.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] GaussianCompactLogarithmBounds.domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) :=
    by simpa [Fm.shift,Syn.shift] using ht.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,Syn.shift,subst_data,subst_radius,sample] using
    compact_sample_bound (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) es ts

theorem original_exponential_fraction (a b E T : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (ht : Γ ⊢[PRAAx] GaussianCompactLogarithmBounds.domain a b E T) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianRadiusExponentialName.nameF nameF) GaussianGammaCanonicalExponent.constantF
      (GaussianRadiusExponentialName.data (radius E T) (data a b)) (GaussianPositiveRationalLogarithm.fraction a b) := by
  have proper := GaussianExponentialRadiusIndependence.independent_radii_proper logF nameF
    (GaussianPositiveRationalLogarithm.radius a b) (radius E T) (GaussianPositiveRationalLogarithm.data a b) (data a b)
    (GaussianPositiveRationalLogarithm.exponential_input a b ht.andE₁) (common_input a b E T hE ht) (cross_original a b ht.andE₁)
  exact GaussianNameEquivalence.cross_trans _ _ _ _ _ _ (GaussianNameEquivalence.cross_symm _ _ _ _ proper)
    (GaussianPositiveRationalLogarithm.exponential_fraction a b ht.andE₁)

theorem actual_harmonic_logarithm_regular_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ pointCN nameF (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (name_regular _ _ Prf.hyp0))

theorem original_logarithm_ordered_representative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (source (var 0) (var 1) ⟶ crossEquivalent logF nameF
      (GaussianPositiveRationalLogarithm.data (var 0) (var 1)) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (cross_original _ _ Prf.hyp0))

theorem actual_harmonic_logarithm_sign_orders_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    ((le (var 0) (var 1) ⟶ GaussianNamedPositiveExponentialOrder.sampleOrder nameF GaussianGammaCanonicalExponent.constantF
      (data (var 0) (var 1)) qzero) ⋏
     (le (var 1) (var 0) ⟶ GaussianNamedPositiveExponentialOrder.sampleOrder GaussianGammaCanonicalExponent.constantF nameF
      qzero (data (var 0) (var 1)))) :=
  closeUniv 2 (.andI (.impI (below_one_samples _ _ Prf.hyp0)) (.impI (above_one_samples _ _ Prf.hyp0)))

theorem original_ordered_logarithm_compact_input_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ GaussianCompactLogarithmBounds.domain (var 0) (var 1) (var 2) (var 3) ⟶
      GaussianRadiusExponentialName.input nameF (radius (var 2) (var 3)) (data (var 0) (var 1))) :=
  closeUniv 4 (.impI (.impI (common_input _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_ordered_logarithm_exponential_fraction_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ GaussianCompactLogarithmBounds.domain (var 0) (var 1) (var 2) (var 3) ⟶
      crossEquivalent (GaussianRadiusExponentialName.nameF nameF) GaussianGammaCanonicalExponent.constantF
        (GaussianRadiusExponentialName.data (radius (var 2) (var 3)) (data (var 0) (var 1)))
        (GaussianPositiveRationalLogarithm.fraction (var 0) (var 1))) :=
  closeUniv 4 (.impI (.impI (original_exponential_fraction _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianHarmonicLogarithmName
