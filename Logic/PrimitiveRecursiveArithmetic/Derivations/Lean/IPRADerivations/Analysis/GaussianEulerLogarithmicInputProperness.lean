import IPRADerivations.Analysis.GaussianEulerLogarithmicClientRate
import IPRADerivations.Analysis.GaussianEulerLogarithmicIntervalName
import IPRADerivations.Analysis.GaussianCompactClientIndependence

/-!
# Original logarithmic compact names at equal rational parameters

Equal normalized parameter fractions give exactly equal original Euler
exponent data, radii and raw logarithmic samples. Each compact client
keeps its own numerical radius and actual query. Comparison through an
unchanged raw sample removes only auxiliary observation slack. The
original compact inputs and the resulting local evaluator equivalence
then identify the two independently meshed compact programs.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicInputProperness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerLogarithmicCompactName (evaluatorF fixedData sample wrapped_at)
open GaussianEulerLogarithmicIntervalName (nameF data compact_input)
open GaussianEulerLogarithmicMultiplier (lipschitz observationCost)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianNameEquivalence (crossEquivalent cross_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem coefficient_equal (z w B D : PTm n) (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.coefficient z B ≐ GaussianEulerIntegrandName.coefficient w D :=
  GaussianRationalSyntheticDivision.qsub_congr he (.eqRefl _)

theorem power_exponent_data_equal (z w B D a b : PTm n)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.powerExponentData z B a b ≐ GaussianEulerIntegrandName.powerExponentData w D a b := by
  simpa only [GaussianEulerIntegrandName.powerExponentData,GaussianNameArithmetic.subst_multiplyData,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (GaussianNameArithmetic.multiplyData GaussianGammaCanonicalExponent.constantF
      GaussianPositiveRationalLogarithm.logF (var 0) (Syn.shift (GaussianPositiveRationalLogarithm.data a b)))
      (coefficient_equal z w B D he)

theorem exponent_data_equal (z w B D a b : PTm n)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.exponentData z B a b ≐ GaussianEulerIntegrandName.exponentData w D a b := by
  simpa only [GaussianEulerIntegrandName.exponentData,GaussianNameArithmetic.subst_addData,
    Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using
    Prf.eqCongr1 (GaussianNameArithmetic.addData (var 0) (Syn.shift (GaussianEulerIntegrandName.decayPoint a b)))
      (power_exponent_data_equal z w B D a b he)

theorem radius_equal (z w B D a b : PTm n)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.radius z B a b ≐ GaussianEulerIntegrandName.radius w D a b := by
  simpa only [GaussianEulerIntegrandName.radius,GaussianNameBounds.subst_U,Syn.subst_var,Syn.inst_zero] using
    Prf.eqCongr1 (GaussianNameBounds.U GaussianEulerIntegrandName.exponentF (var 0)) (exponent_data_equal z w B D a b he)

theorem integrand_data_equal (z w B D a b : PTm n)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.data z B a b ≐ GaussianEulerIntegrandName.data w D a b :=
  congrPairT (radius_equal z w B D a b he) (exponent_data_equal z w B D a b he)

theorem integrand_sample_equal (p z w B D a b : PTm n)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    GaussianEulerIntegrandName.sample p z B a b ≐ GaussianEulerIntegrandName.sample p w D a b :=
  (GaussianEulerIntegrandName.sample_at p z B a b).eqTrans
    ((congrAp2 GaussianEulerIntegrandName.nameF (.eqRefl _) (integrand_data_equal z w B D a b he)).eqTrans
      (GaussianEulerIntegrandName.sample_at p w D a b).eqSymm)

/-- The original raw logarithmic factor is independent of the parameter encoding. -/
theorem raw_sample_equal (p j z w B D a b : PTm n)
    (he : Γ ⊢[PRAAx] ofGaussian z B ≐ ofGaussian w D) : Γ ⊢[PRAAx]
    GaussianEulerLogarithmicMultiplier.sample p j z B a b ≐ GaussianEulerLogarithmicMultiplier.sample p j w D a b :=
  GaussianRationalSyntheticDivision.qmul_congr (integrand_sample_equal p z w B D a b he) (.eqRefl _)

def pointSource (z w R S B D E T a b : PTm n) : Fm PTm n :=
  GaussianEulerLogarithmicMultiplier.source z R B E T a b ⋏
    (GaussianEulerLogarithmicMultiplier.source w S D E T a b ⋏ ofGaussian z B ≐ ofGaussian w D)
def cost (j R S E T : PTm n) : PTm n := observationCost j R E T+observationCost j S E T
def source (z w R S B D a C E T : PTm n) : Fm PTm n :=
  GaussianEulerCompactAdditivity.intervalSource z R B a C E T ⋏
    (GaussianEulerCompactAdditivity.intervalSource w S D a C E T ⋏ ofGaussian z B ≐ ofGaussian w D)
@[simp] theorem subst_pointSource {m : ℕ} (σ : Fin n → PTm m) (z w R S B D E T a b : PTm n) :
    (pointSource z w R S B D E T a b).subst σ = pointSource (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ R)
      (Syn.subst σ S) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [pointSource]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z w R S B D a C E T : PTm n) :
    (source z w R S B D a C E T).subst σ = source (Syn.subst σ z) (Syn.subst σ w) (Syn.subst σ R)
      (Syn.subst σ S) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ a) (Syn.subst σ C) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [source]

theorem client_slack (p q s j z w R S B D E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] pointSource z w R S B D E T a b) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack (qsub (sample p j R E T z B a b) (sample q j S E T w D a b))
      (unit p+unit q) (unit p*unit q) (cost j R S E T) s := by
  let P := unit p
  let Q := unit q
  let V := unit s
  let DD := P*Q*V
  let H := observationCost j R E T
  let K := observationCost j S E T
  have up := unit_positive (Γ := Γ) p
  have uq := unit_positive (Γ := Γ) q
  have uv := unit_positive (Γ := Γ) s
  have dp := positive_product _ _ up uv
  have dq := positive_product _ _ uq uv
  have dd : Γ ⊢[PRAAx] le one DD := positive_product _ _ (positive_product _ _ up uq) uv
  have first : Γ ⊢[PRAAx] distanceBounded (sample p j R E T z B a b)
      (GaussianEulerLogarithmicMultiplier.sample s j w D a b) ((V+H*P)*Q) DD :=
    distance_congr (.eqRefl _) (raw_sample_equal s j z w B D a b hs.andE₂.andE₂) (.eqRefl _) (.eqRefl _)
      (distance_radius_mono _ _ _ _ _ _ dp dd
        (le_of_eq_add (d := zero) (by dsimp only [DD,P,Q,V,H]; ipra_ring))
        (GaussianEulerLogarithmicClientRate.original_to_raw p s j z R B E T a b hs.andE₁))
  have second : Γ ⊢[PRAAx] distanceBounded (GaussianEulerLogarithmicMultiplier.sample s j w D a b)
      (sample q j S E T w D a b) ((V+K*Q)*P) DD :=
    distance_symmetric _ _ _ _ dd
      (distance_radius_mono _ _ _ _ _ _ dq dd (le_of_eq_add (d := zero) (by dsimp only [DD,P,Q,V,K]; ipra_ring))
        (GaussianEulerLogarithmicClientRate.original_to_raw q s j w S D E T a b hs.andE₂.andE₁))
  exact GaussianRationalReciprocal.bound_congr (.eqRefl _)
    (by unfold cost; dsimp only [H,K,P,Q,V]; unfold unit; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ dd first second)

theorem client_observations (p q j z w R S B D E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] pointSource z w R S B D E T a b) : Γ ⊢[PRAAx]
    distanceBounded (sample p j R E T z B a b) (sample q j S E T w D a b)
      (unit p+unit q) (unit p*unit q) :=
  GaussianRationalSlackRemoval.slack_removal_at _ _ _ (cost j R S E T)
    (positive_product _ _ (unit_positive p) (unit_positive q)) (client_slack p q _ j z w R S B D E T a b hs)

theorem evaluator_proper (t j z w R S B D E T : PTm n)
    (hs : Γ ⊢[PRAAx] pointSource z w R S B D E T (fstT t) (sndT t)) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData j R E T z B))
      (GaussianCompactRiemannName.nameData t (fixedData j S E T w D)) := by
  have hshift : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
      pointSource (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift S))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T))
        (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t))) :=
    by simpa only [Fm.shift,subst_pointSource,Syn.shift,subst_fstT,subst_sndT] using hs.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianCompactRiemannName.subst_nameData,GaussianEulerLogarithmicCompactName.subst_fixedData,Syn.shift] using
    distance_congr (wrapped_at (var 1) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift R))
      (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift B))).eqSymm
      (wrapped_at (var 0) (Syn.shift (Syn.shift t)) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift S))
        (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (Syn.shift (Syn.shift w)) (Syn.shift (Syn.shift D))).eqSymm
      (.eqRefl _) (.eqRefl _)
      (client_observations (var 1) (var 0) (Syn.shift (Syn.shift j)) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift w))
        (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift S)) (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift D))
        (Syn.shift (Syn.shift E)) (Syn.shift (Syn.shift T)) (fstT (Syn.shift (Syn.shift t))) (sndT (Syn.shift (Syn.shift t))) hshift)

theorem agreement_at (t j z w R S B D a C E T : PTm n)
    (hs : Γ ⊢[PRAAx] source z w R S B D a C E T)
    (ht : Γ ⊢[PRAAx] GaussianCompactRiemannName.inside a C E t) : Γ ⊢[PRAAx]
    crossEquivalent (GaussianCompactRiemannName.evaluatorName evaluatorF) (GaussianCompactRiemannName.evaluatorName evaluatorF)
      (GaussianCompactRiemannName.nameData t (fixedData j R E T z B))
      (GaussianCompactRiemannName.nameData t (fixedData j S E T w D)) := by
  have left := GaussianEulerCompactAdditivity.domain_of_inside t a C E T hs.andE₁.andE₂.andE₁ hs.andE₁.andE₁.andE₂.andE₁ hs.andE₁.andE₂.andE₂ ht
  exact evaluator_proper t j z w R S B D E T
    (.andI (.andI hs.andE₁.andE₁ left) (.andI (.andI hs.andE₂.andE₁.andE₁ left) hs.andE₂.andE₂))

theorem local_agreement (j z w R S B D a C E T : PTm n)
    (hs : Γ ⊢[PRAAx] source z w R S B D a C E T) : Γ ⊢[PRAAx]
    GaussianCompactClientIndependence.localAgreement evaluatorF evaluatorF a C E
      (fixedData j R E T z B) (fixedData j S E T w D) := by
  have hh : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift S) (Syn.shift B)
      (Syn.shift D) (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) :=
    by simpa only [Fm.shift,subst_source,Syn.shift] using hs.shift
  refine .allI (.impI ?_)
  simpa only [GaussianCompactClientIndependence.localAgreement,GaussianEulerLogarithmicCompactName.subst_fixedData,Syn.shift] using
    agreement_at (var 0) (Syn.shift j) (Syn.shift z) (Syn.shift w) (Syn.shift R) (Syn.shift S) (Syn.shift B) (Syn.shift D)
      (Syn.shift a) (Syn.shift C) (Syn.shift E) (Syn.shift T) hh.wk Prf.hyp0

/-- Equal original rational parameters identify the actual independently
meshed compact programs at every runtime logarithmic order. -/
theorem original_compact_proper (j z w R S B D a C E T : PTm n)
    (hs : Γ ⊢[PRAAx] source z w R S B D a C E T) : Γ ⊢[PRAAx]
    crossEquivalent nameF nameF (data j z R B a C E T) (data j w S D a C E T) :=
  GaussianCompactClientIndependence.name_independence evaluatorF evaluatorF a C E (lipschitz j R E T) T
    (lipschitz j S E T) T (fixedData j R E T z B) (fixedData j S E T w D)
    (.andI (compact_input j z R B a C E T hs.andE₁)
      (.andI (compact_input j w S D a C E T hs.andE₂.andE₁) (local_agreement j z w R S B D a C E T hs)))

theorem original_observations (p q j z w R S B D a C E T : PTm n)
    (hs : Γ ⊢[PRAAx] source z w R S B D a C E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data j z R B a C E T)) (ap2 nameF q (data j w S D a C E T))
      (unit p+unit q) (unit p*unit q) := cross_at _ _ _ _ p q (original_compact_proper j z w R S B D a C E T hs)

theorem actual_original_all_order_logarithmic_compact_input_proper_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      crossEquivalent nameF nameF (data (var 0) (var 1) (var 3) (var 5) (var 7) (var 8) (var 9) (var 10))
        (data (var 0) (var 2) (var 4) (var 6) (var 7) (var 8) (var 9) (var 10))) :=
  closeUniv 11 (.impI (original_compact_proper _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

theorem actual_original_all_order_logarithmic_raw_parameter_sample_equal_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (ofGaussian (var 2) (var 4) ≐ ofGaussian (var 3) (var 5) ⟶
      GaussianEulerLogarithmicMultiplier.sample (var 0) (var 1) (var 2) (var 4) (var 6) (var 7) ≐
        GaussianEulerLogarithmicMultiplier.sample (var 0) (var 1) (var 3) (var 5) (var 6) (var 7)) :=
  closeUniv 8 (.impI (raw_sample_equal _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerLogarithmicInputProperness
