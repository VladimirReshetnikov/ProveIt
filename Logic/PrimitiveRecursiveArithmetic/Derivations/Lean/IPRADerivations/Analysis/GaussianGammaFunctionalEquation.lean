import IPRADerivations.Analysis.GaussianGammaEulerShiftLimit
import IPRADerivations.Analysis.GaussianGammaEulerApproximationName

/-!
# The C20 shift from the actual finite Euler identity

A common computed finite cutoff is used on both original disks. The
actual C10 rate and actual coefficient correction tend to zero through
native rational slack removal. The original mesh-log inversion remains
an explicit local provider until its independent supplier is combined.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaFunctionalEquation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaCanonicalExponent (source constantF constant_at constant_regular)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaEulerShiftLimit (correction correctedF correctedData logInverse shifted_source)
open GaussianGammaFiniteApproximantName (qF qData)
open GaussianGammaC7Name (nameF data sample)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent point_at cross_at)
open GaussianRationalHorner (qmul ofGaussian positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedSmallPerturbationTransport (budgetNumerator budgetDenominator)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def eulerRate (R : PTm n) : PTm n := GaussianGammaEulerApproximationName.rate R
def cost (R : PTm n) : PTm n :=
  R*eulerRate (R+one)+(R+two)*eulerRate R+GaussianGammaC9Bound.majorant R*(R+one)
def cutoff (t R : PTm n) : PTm n := one+t+two*R+two*(R+one)+GaussianGammaPerturbationExponent.numerator R+
  GaussianGammaPerturbationExponent.numerator (R+one)+cost R*unit t

def leftLimitF : PR 2 := multiplyF constantF nameF
def leftLimitData (z R B : PTm n) : PTm n := multiplyData constantF nameF
  (ofGaussian z B) (data (shifted z B) (R+one) B)
def allLogInverse : Fm PTm n := .all (le one (var 0) ⟶ logInverse (var 0))

@[simp] theorem subst_eulerRate {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (eulerRate R) = eulerRate (Syn.subst σ R) := by simp [eulerRate]
@[simp] theorem subst_cost {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (cost R) = cost (Syn.subst σ R) := by simp [cost]
@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (t R : PTm n) :
    Syn.subst σ (cutoff t R) = cutoff (Syn.subst σ t) (Syn.subst σ R) := by simp [cutoff,unit]
@[simp] theorem subst_leftLimitData {l : ℕ} (σ : Fin n → PTm l) (z R B : PTm n) :
    Syn.subst σ (leftLimitData z R B) = leftLimitData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by
  simp [leftLimitData]

theorem input_point_bound (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx] bounded (ofGaussian z B) R one := by
  apply GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ h.andE₂.andE₁ (le_refl one)
    (GaussianRationalHorner.ofGaussian_represents z B h.andE₂.andE₁)
  exact le_congr (by ipra_ring) (by ipra_ring) h.andE₂.andE₂

theorem left_limit_regular (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    pointCN leftLimitF (leftLimitData z R B) :=
  multiply_fast constantF nameF _ _ (constant_regular _) (GaussianGammaC7Name.name_regular _ _ _ (shifted_source z R B h))

theorem log_inverse_at (N : PTm n) (h : Γ ⊢[PRAAx] allLogInverse) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx] logInverse N := by
  have gate : Γ ⊢[PRAAx] le one N ⟶ logInverse N := by simpa [allLogInverse] using h.allE N
  exact .impE gate hN

theorem cutoff_positive (t R : PTm n) : Γ ⊢[PRAAx] le one (cutoff t R) := by
  unfold cutoff
  ipra_le 𝔞 t+2*𝔞 R+2*(𝔞 R+1)+𝔞(GaussianGammaPerturbationExponent.numerator R)+
    𝔞(GaussianGammaPerturbationExponent.numerator (R+one))+𝔞(cost R)*𝔞(unit t)
theorem cutoff_threshold (t R : PTm n) : Γ ⊢[PRAAx] le (cost R*unit t) (cutoff t R) := by
  unfold cutoff
  ipra_le 1+𝔞 t+2*𝔞 R+2*(𝔞 R+1)+𝔞(GaussianGammaPerturbationExponent.numerator R)+
    𝔞(GaussianGammaPerturbationExponent.numerator (R+one))
theorem cutoff_sources (t z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    GaussianGammaEulerConvergence.source z R B (cutoff t R) ⋏
      GaussianGammaEulerConvergence.source (shifted z B) (R+one) B (cutoff t R) := by
  refine .andI (.andI h (.andI ?_ ?_)) (.andI (shifted_source z R B h) (.andI ?_ ?_))
  all_goals unfold cutoff
  · ipra_le 1+𝔞 t+2*(𝔞 R+1)+𝔞(GaussianGammaPerturbationExponent.numerator R)+
      𝔞(GaussianGammaPerturbationExponent.numerator (R+one))+𝔞(cost R)*𝔞(unit t)
  · ipra_le 1+𝔞 t+2*𝔞 R+2*(𝔞 R+1)+𝔞(GaussianGammaPerturbationExponent.numerator (R+one))+𝔞(cost R)*𝔞(unit t)
  · ipra_le 1+𝔞 t+2*𝔞 R+𝔞(GaussianGammaPerturbationExponent.numerator R)+
      𝔞(GaussianGammaPerturbationExponent.numerator (R+one))+𝔞(cost R)*𝔞(unit t)
  · ipra_le 1+𝔞 t+2*𝔞 R+2*(𝔞 R+1)+𝔞(GaussianGammaPerturbationExponent.numerator R)+𝔞(cost R)*𝔞(unit t)

/-- The original finite Q observation can use any actual later operation
clock, while the target C7 observation stays at t. -/
theorem earlier_euler_error (t u z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R B N) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    distanceBounded (ap2 qF u (qData z B N)) (sample t z R B) (eulerRate R*unit t+two*N) (N*unit t) := by
  have hn := (GaussianGammaEulerConvergence.local_source z R B N h).andE₂.andE₁
  have grow : Γ ⊢[PRAAx] le (unit t) (unit u) :=
    GaussianFactorBudget.power_monotone_length two t u (le_succ_self one) htu
  have compare : Γ ⊢[PRAAx]
      le (budgetNumerator u t (GaussianGammaPerturbationExponent.numerator R) N (GaussianGammaC9Bound.majorant R)*(N*unit t))
        ((eulerRate R*unit t+two*N)*budgetDenominator u t N) := by
    ipra_le 𝔞(N*N)*𝔞(unit t)*sl grow using
      unfold eulerRate GaussianGammaEulerApproximationName.rate budgetNumerator budgetDenominator
      ipra_simps
      ring
  exact distance_radius_mono _ _ _ _ _ _ (GaussianNamedSmallPerturbationTransport.denominator_positive u t N hn)
    (positive_product _ _ hn (unit_positive t)) compare (GaussianGammaEulerConvergence.observation_error u t z R B N h)

def clock (f : PR 2) (c y t : PTm n) : PTm n := GaussianNamedSmallPerturbationTransport.productClock constantF f c y t
@[simp] theorem subst_clock {l : ℕ} (σ : Fin n → PTm l) (f : PR 2) (c y t : PTm n) :
    Syn.subst σ (clock f c y t) = clock f (Syn.subst σ c) (Syn.subst σ y) (Syn.subst σ t) := by simp [clock]
theorem clock_later (f : PR 2) (c y t : PTm n) : Γ ⊢[PRAAx] le t (clock f c y t) := le_add_right _ _
theorem constant_product_at (f : PR 2) (c y t : PTm n) : Γ ⊢[PRAAx]
    ap2 (multiplyF constantF f) t (multiplyData constantF f c y) ≐ qmul c (ap2 f (clock f c y t) y) :=
  (GaussianNamedSmallPerturbationTransport.product_at constantF f c y t).eqTrans
    (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))


theorem earlier_C7_error (t u z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) (htu : Γ ⊢[PRAAx] le t u) : Γ ⊢[PRAAx]
    distanceBounded (sample u z R B) (sample t z R B) two (unit t) := by
  have grow : Γ ⊢[PRAAx] le (unit t) (unit u) :=
    GaussianFactorBudget.power_monotone_length two t u (le_succ_self one) htu
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive u) (unit_positive t)) (unit_positive t) _
    (point_at nameF (data z R B) u t (GaussianGammaC7Name.name_regular z R B h))
  ipra_le 𝔞(unit t)*sl grow

theorem left_raw_error (t z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    distanceBounded (ap2 leftLimitF t (leftLimitData z R B))
      (qmul (ofGaussian z B) (sample t (shifted z B) (R+one) B)) (two*R) (unit t) := by
  let u := clock nameF (ofGaussian z B) (data (shifted z B) (R+one) B) t
  have hs := shifted_source z R B h
  have raw := GaussianNameRingLaws.product_left_error _ _ (ofGaussian z B) two (unit t) R
    (GaussianGammaC9Bound.majorant (R+one)) (unit_positive t)
    (earlier_C7_error t u (shifted z B) (R+one) B hs (clock_later _ _ _ _))
    (input_point_bound z R B h) (GaussianGammaC9Bound.reciprocal_sample_bound t _ _ _ hs)
  exact distance_congr
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (constant_product_at nameF _ _ t).eqSymm)
    (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _) (.eqRefl _) raw

theorem finite_left_error (t z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hs : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source (shifted z B) (R+one) B N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 GaussianGammaEulerShift.leftF t (GaussianGammaEulerShift.leftData z B N))
      (qmul (ofGaussian z B) (sample t (shifted z B) (R+one) B))
      (R*(eulerRate (R+one)*unit t+two*N)) (N*unit t) := by
  let u := clock qF (ofGaussian z B) (qData (shifted z B) B N) t
  have hn := (GaussianGammaEulerConvergence.local_source _ _ _ _ hs).andE₂.andE₁
  have raw := GaussianNameRingLaws.product_left_error _ _ (ofGaussian z B) _ _ R
    (GaussianGammaC9Bound.majorant (R+one)) (positive_product _ _ hn (unit_positive t))
    (earlier_euler_error t u (shifted z B) (R+one) B N hs (clock_later _ _ _ _))
    (input_point_bound z R B h) (GaussianGammaC9Bound.reciprocal_sample_bound t _ _ _ (shifted_source z R B h))
  exact distance_congr
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (constant_product_at qF _ _ t).eqSymm)
    (GaussianRationalPowerAlgebra.qmul_commutative _ _) (by ipra_ring) (.eqRefl _) raw

def rightRate (R : PTm n) : PTm n := (R+two)*eulerRate R+GaussianGammaC9Bound.majorant R*(R+one)

theorem finite_right_error (t z R B N : PTm n) (h : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 correctedF t (correctedData z B N)) (sample t z R B)
      (rightRate R*unit t+two*(R+two)*N) (N*unit t) := by
  let c := correction z B N
  let u := clock qF c (qData z B N) t
  have hn := (GaussianGammaEulerConvergence.local_source _ _ _ _ h).andE₂.andE₁
  have pairden := positive_product (Γ := Γ) _ _ hn (unit_positive t)
  have corr : Γ ⊢[PRAAx] distanceBounded c GaussianRationalSyntheticDivision.qone ((R+one)*unit t) (N*unit t) :=
    distance_radius_mono _ _ _ _ _ _ hn pairden (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianGammaEulerShiftLimit.correction_distance z R B N h.andE₁ hn)
  have raw := GaussianNameArithmetic.product_distance _ _ c GaussianRationalSyntheticDivision.qone _ _ _ (R+two)
    (GaussianGammaC9Bound.majorant R) pairden (earlier_euler_error t u z R B N h (clock_later _ _ _ _)) corr
    (GaussianGammaEulerShiftLimit.correction_bound z R B N h.andE₁ hn)
    (GaussianGammaC9Bound.reciprocal_sample_bound t z R B h.andE₁)
  exact distance_congr
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (constant_product_at qF _ _ t).eqSymm)
    (GaussianReciprocalHorner.qmul_one_right _ (GaussianGammaC7Name.sample_canonical t z R B))
    (by unfold rightRate; ipra_ring) (.eqRefl _) raw


def slackConstant (R : PTm n) : PTm n := num 6*R+num 9
@[simp] theorem subst_slackConstant {l : ℕ} (σ : Fin n → PTm l) (R : PTm n) :
    Syn.subst σ (slackConstant R) = slackConstant (Syn.subst σ R) := by simp [slackConstant]

/-- All approximants in this proof use ONE actual computed finite N.
Only its genuine C10 rate and the auxiliary observation errors vanish. -/
theorem observation_slack (p q t z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    GaussianRationalSlackRemoval.slack
      (qsub (ap2 leftLimitF p (leftLimitData z R B)) (sample q z R B))
      (unit p+unit q) (unit p*unit q) (slackConstant R) t := by
  let N := cutoff t R
  let Z := N*unit p*unit q*unit t
  let A₁ := (unit p+unit t)*N*unit q
  let A₂ := two*R*N*unit p*unit q
  let A₃ := R*(eulerRate (R+one)*unit t+two*N)*unit p*unit q
  let A₄ := two*N*unit p*unit q
  let A₅ := (rightRate R*unit t+two*(R+two)*N)*unit p*unit q
  let A₆ := (unit t+unit q)*N*unit p
  have hn : Γ ⊢[PRAAx] le one N := cutoff_positive t R
  have zpos : Γ ⊢[PRAAx] le one Z := positive_product _ _
    (positive_product _ _ (positive_product _ _ hn (unit_positive p)) (unit_positive q)) (unit_positive t)
  have hs := cutoff_sources t z R B h
  have lr := left_limit_regular z R B h
  have pr := GaussianGammaC7Name.name_regular z R B h
  have a : Γ ⊢[PRAAx] distanceBounded (ap2 leftLimitF p (leftLimitData z R B))
      (ap2 leftLimitF t (leftLimitData z R B)) A₁ Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive t)) zpos
      (le_of_eq_add (d := zero) (by dsimp only [A₁,Z]; ipra_ring)) (point_at _ _ p t lr)
  have b : Γ ⊢[PRAAx] distanceBounded (ap2 leftLimitF t (leftLimitData z R B))
      (qmul (ofGaussian z B) (sample t (shifted z B) (R+one) B)) A₂ Z :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive t) zpos
      (le_of_eq_add (d := zero) (by dsimp only [A₂,Z]; ipra_ring)) (left_raw_error t z R B h)
  have c : Γ ⊢[PRAAx] distanceBounded (qmul (ofGaussian z B) (sample t (shifted z B) (R+one) B))
      (ap2 GaussianGammaEulerShift.leftF t (GaussianGammaEulerShift.leftData z B N)) A₃ Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hn (unit_positive t)) zpos
      (le_of_eq_add (d := zero) (by dsimp only [A₃,Z]; ipra_ring))
      (distance_symmetric _ _ _ _ (positive_product _ _ hn (unit_positive t)) (finite_left_error t z R B N h hs.andE₂))
  have finite := GaussianGammaEulerShiftLimit.finite_shift_reciprocal z B N h.andE₂.andE₁ hn (log_inverse_at N hi hn)
  have d : Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianGammaEulerShift.leftF t (GaussianGammaEulerShift.leftData z B N))
      (ap2 correctedF t (correctedData z B N)) A₄ Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive t)) zpos
      (le_of_eq_add (d := zero) (by dsimp only [A₄,Z]; ipra_ring)) (cross_at _ _ _ _ t t finite)
  have e : Γ ⊢[PRAAx] distanceBounded (ap2 correctedF t (correctedData z B N)) (sample t z R B) A₅ Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hn (unit_positive t)) zpos
      (le_of_eq_add (d := zero) (by dsimp only [A₅,Z]; ipra_ring)) (finite_right_error t z R B N hs.andE₁)
  have f : Γ ⊢[PRAAx] distanceBounded (sample t z R B) (sample q z R B) A₆ Z :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive q)) zpos
      (le_of_eq_add (d := zero) (by dsimp only [A₆,Z]; ipra_ring)) (point_at _ _ t q pr)
  have chain := distance_triangle_same _ _ _ _ _ _ zpos
    (distance_triangle_same _ _ _ _ _ _ zpos
      (distance_triangle_same _ _ _ _ _ _ zpos
        (distance_triangle_same _ _ _ _ _ _ zpos (distance_triangle_same _ _ _ _ _ _ zpos a b) c) d) e) f
  change Γ ⊢[PRAAx] distanceBounded (ap2 leftLimitF p (leftLimitData z R B)) (sample q z R B)
    ((unit p+unit q)*unit t+slackConstant R*(unit p*unit q)) (unit p*unit q*unit t)
  apply distance_radius_mono _ _ _ _ _ _ zpos
    (positive_product _ _ (positive_product _ _ (unit_positive p) (unit_positive q)) (unit_positive t)) _ chain
  have threshold := cutoff_threshold (Γ := Γ) t R
  ipra_le 𝔞(unit p*unit q)*𝔞(unit p*unit q)*𝔞(unit t)*sl threshold using
    dsimp only [A₁,A₂,A₃,A₄,A₅,A₆,Z]
    unfold cost rightRate slackConstant
    ipra_simps
    ring

theorem observation_identity (p q z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    distanceBounded (ap2 leftLimitF p (leftLimitData z R B)) (sample q z R B)
      (unit p+unit q) (unit p*unit q) := by
  apply GaussianRationalSlackRemoval.slack_removal _ _ _ (slackConstant R)
    (positive_product _ _ (unit_positive p) (unit_positive q))
  refine .allI ?_
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) := by simpa [Fm.shift,Syn.shift] using h.shift
  have inv : Γ.map Fm.shift ⊢[PRAAx] allLogInverse := by simpa [allLogInverse,Fm.shift,Syn.shift] using hi.shift
  simpa only [GaussianRationalSlackRemoval.allSlack,GaussianRationalMetric.subst_qsub,subst_ap2,subst_leftLimitData,
    GaussianGammaC7Name.subst_sample,GaussianCoefficientNameBounds.subst_unit,subst_slackConstant,PTm.subst_add,PTm.subst_mul,Syn.shift] using
    observation_slack (Syn.shift p) (Syn.shift q) (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) hs inv

theorem original_C20_shift (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B)
    (hi : Γ ⊢[PRAAx] allLogInverse) : Γ ⊢[PRAAx]
    crossEquivalent leftLimitF nameF (leftLimitData z R B) (data z R B) := by
  refine .allI (.allI ?_)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) := by
    simpa [Fm.shift,Syn.shift] using h.shift.shift
  have inv : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] allLogInverse := by
    simpa [allLogInverse,Fm.shift,Syn.shift] using hi.shift.shift
  simpa only [crossEquivalent,sample,subst_leftLimitData,GaussianGammaC7Name.subst_data,Syn.shift,unit,GaussianEuclideanPointDistance.unit] using
    observation_identity (var 1) (var 0) (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift R)) (Syn.shift (Syn.shift B)) hs inv


theorem cutoff_cofinal (t R : PTm n) : Γ ⊢[PRAAx] le t (cutoff t R) := by
  unfold cutoff
  ipra_le 1+2*𝔞 R+2*(𝔞 R+1)+𝔞(GaussianGammaPerturbationExponent.numerator R)+
    𝔞(GaussianGammaPerturbationExponent.numerator (R+one))+𝔞(cost R)*𝔞(unit t)

theorem actual_C20_common_cutoff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (cutoff (var 0) (var 1)) ⋏
      (le (var 0) (cutoff (var 0) (var 1)) ⋏ le (cost (var 1)*unit (var 0)) (cutoff (var 0) (var 1)))) :=
  closeUniv 2 (.andI (cutoff_positive _ _) (.andI (cutoff_cofinal _ _) (cutoff_threshold _ _)))

theorem original_C20_two_disk_cutoff_guards_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (source (var 1) (var 2) (var 3) ⟶
      (GaussianGammaEulerConvergence.source (var 1) (var 2) (var 3) (cutoff (var 0) (var 2)) ⋏
        GaussianGammaEulerConvergence.source (shifted (var 1) (var 3)) (var 2+one) (var 3) (cutoff (var 0) (var 2)))) :=
  closeUniv 4 (.impI (cutoff_sources _ _ _ _ Prf.hyp0))

theorem original_C20_shift_independent_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source (var 2) (var 3) (var 4) ⟶ allLogInverse ⟶
      distanceBounded (ap2 leftLimitF (var 0) (leftLimitData (var 2) (var 3) (var 4)))
        (sample (var 1) (var 2) (var 3) (var 4))
        (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 5 (.impI (.impI (observation_identity _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

theorem original_C20_actual_named_shift_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) (var 2) ⟶ allLogInverse ⟶
      crossEquivalent leftLimitF nameF (leftLimitData (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (.impI (original_C20_shift _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaFunctionalEquation
