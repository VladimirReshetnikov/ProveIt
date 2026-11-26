import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerHeadContinuity
import IPRADerivations.Analysis.Gamma.EulerProducts.Exponents.GaussianGammaLogExponentContinuity
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianGammaEulerApproximationName
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialRadiusIndependence
import IPRADerivations.Analysis.Exponential.PositiveAxis.GaussianPositiveExponentialMajorant

/-!
# Fixed common finite references for the actual Euler Gamma approximants

A uniform input disk fixes the exponential radius, cutoff and query before
encoded inputs are compared. Actual original multiplication and exponential
normalization clocks are retained through checked independent-radius laws.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianGammaEulerContinuityReference

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianGammaFiniteApproximantName (logF logExponentF logExponentData qF qData log_exponent_regular)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianGammaLogExponentContinuity (logRadius exponentRadius exponent_input exponent_bound)
open GaussianRationalHorner (qmul positive_product ofGaussian)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalPolynomialExponential (scalarSum)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Exp" => GaussianRadiusExponentialName.nameF logExponentF

@[simp] theorem subst_old_head {l : ℕ} (σ : Fin n → PTm l) (z B N : PTm n) :
    Syn.subst σ (GaussianGammaEulerHead.run z B N) = GaussianGammaEulerHead.run (Syn.subst σ z) (Syn.subst σ B) (Syn.subst σ N) := by
  simp only [GaussianGammaEulerHead.run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext k
  fin_cases k <;> rfl

def headBound (R N : PTm n) : PTm n := R*pw (one+R) N
def uniformExpData (z R B N : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (exponentRadius R N) (logExponentData z B N)
def uniformData (z R B N : PTm n) : PTm n := GaussianNameArithmetic.multiplyData constantF Exp
  (GaussianGammaEulerHead.run z B N) (uniformExpData z R B N)
def cutoff (r R N : PTm n) : PTm n := GaussianRadiusExponentialName.index (exponentRadius R N) r
def query (r R N : PTm n) : PTm n := GaussianRadiusExponentialName.inputPrecision (exponentRadius R N) r
def reference (r z R B N : PTm n) : PTm n := qmul (GaussianGammaEulerHead.run z B N)
  (scalarSum (ap2 logExponentF (query r R N) (logExponentData z B N)) (cutoff r R N))
def input (z R B N : PTm n) : Fm PTm n := le one N ⋏ (le one B ⋏ ComplexLogarithmRemainder.bounded z (R*B))
@[simp] theorem subst_headBound {l : ℕ} (σ : Fin n → PTm l) (R N : PTm n) :
    Syn.subst σ (headBound R N) = headBound (Syn.subst σ R) (Syn.subst σ N) := by simp [headBound]
@[simp] theorem subst_uniformExpData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (uniformExpData z R B N) = uniformExpData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [uniformExpData,logExponentData]
@[simp] theorem subst_uniformData {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    Syn.subst σ (uniformData z R B N) = uniformData (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [uniformData]
@[simp] theorem subst_cutoff {l : ℕ} (σ : Fin n → PTm l) (r R N : PTm n) :
    Syn.subst σ (cutoff r R N) = cutoff (Syn.subst σ r) (Syn.subst σ R) (Syn.subst σ N) := by simp [cutoff]
@[simp] theorem subst_query {l : ℕ} (σ : Fin n → PTm l) (r R N : PTm n) :
    Syn.subst σ (query r R N) = query (Syn.subst σ r) (Syn.subst σ R) (Syn.subst σ N) := by simp [query]
@[simp] theorem subst_reference {l : ℕ} (σ : Fin n → PTm l) (r z R B N : PTm n) :
    Syn.subst σ (reference r z R B N) = reference (Syn.subst σ r) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [reference,logExponentData]
@[simp] theorem subst_input {l : ℕ} (σ : Fin n → PTm l) (z R B N : PTm n) :
    (input z R B N).subst σ = input (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp [input,ComplexLogarithmRemainder.bounded]

theorem head_bound (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    bounded (GaussianGammaEulerHead.run z B N) (headBound R N) one :=
  GaussianRationalReciprocal.bound_congr (GaussianGammaEulerHead.program_at z B N).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianGammaEulerHead.prefix_bound z R B N h.andE₂.andE₁ h.andE₂.andE₂)

theorem uniform_exp_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN Exp (uniformExpData z R B N) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (exponent_input z R B N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
theorem uniform_regular (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    GaussianEuclideanDistanceName.pointCN qF (uniformData z R B N) :=
  GaussianNameArithmetic.multiply_fast _ _ _ _ (constant_regular _) (uniform_exp_regular z R B N h)

theorem original_uniform (z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    GaussianNameEquivalence.crossEquivalent qF qF (qData z B N) (uniformData z R B N) := by
  have er := log_exponent_regular z B N h.andE₁
  have exp := GaussianExponentialRadiusIndependence.same_input_cross logExponentF
    (GaussianNameBounds.U logExponentF (logExponentData z B N)) (exponentRadius R N) (logExponentData z B N)
    (GaussianGammaFiniteApproximantName.exponential_input logExponentF _ er)
    (exponent_input z R B N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂)
  exact GaussianGammaAdjacentCutoff.multiply_cross constantF constantF Exp Exp _ _ _ _
    (constant_regular _) (constant_regular _)
    (GaussianRadiusExponentialName.name_regular _ _ _ (GaussianGammaFiniteApproximantName.exponential_input logExponentF _ er))
    (uniform_exp_regular z R B N h) (GaussianNameEquivalence.cross_refl _ _ (constant_regular _)) exp

def productQuery (r z R B N : PTm n) : PTm n := GaussianFastValueCut.exponent
  (GaussianNameArithmetic.multiplyModulus constantF Exp (GaussianGammaEulerHead.run z B N) (uniformExpData z R B N)) r
@[simp] theorem subst_productQuery {l : ℕ} (σ : Fin n → PTm l) (r z R B N : PTm n) :
    Syn.subst σ (productQuery r z R B N) = productQuery (Syn.subst σ r) (Syn.subst σ z)
      (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [productQuery]

theorem uniform_at (r z R B N : PTm n) : Γ ⊢[PRAAx] ap2 qF r (uniformData z R B N) ≐
    qmul (GaussianGammaEulerHead.run z B N) (ap2 Exp (productQuery r z R B N) (uniformExpData z R B N)) :=
  (GaussianNameArithmetic.multiply_at constantF Exp _ _ r).eqTrans
    ((GaussianNameArithmetic.recode_congr (GaussianRationalSyntheticDivision.qmul_congr (constant_at _ _) (.eqRefl _))).eqTrans
      (GaussianExponentialReference.recode_fixed _ (GaussianRationalHorner.qmul_canonical _ _)))

theorem uniform_sample_reference (r z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 qF r (uniformData z R B N)) (reference r z R B N) (LeanProofs.IPRA.PTm.num 3*headBound R N) (unit r) := by
  let t := productQuery r z R B N
  let H := GaussianGammaEulerHead.run z B N
  let e := uniformExpData z R B N
  have ep := uniform_exp_regular z R B N h
  have later : Γ ⊢[PRAAx] le r t := le_add_right _ _
  have gt := GaussianExponentialReference.unit_monotone later
  have raw := GaussianNameEquivalence.point_at Exp e t r ep
  have dist : Γ ⊢[PRAAx] distanceBounded (ap2 Exp t e) (ap2 Exp r e) two (unit r) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive t) (unit_positive r)) (unit_positive r)
      (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (unit t*unit r)) (mul_le_mul_right (unit r) gt))) raw
  have left := GaussianNameRingLaws.product_right_error H (ap2 Exp t e) (ap2 Exp r e) two (unit r)
    (GaussianNameBounds.U Exp e) (headBound R N) (unit_positive r) dist (GaussianNameBounds.sample_bound Exp e t ep) (head_bound z R B N h)
  have common := GaussianExponentialReference.finite_reference logExponentF (exponentRadius R N) (logExponentData z B N)
    r (query r R N) (cutoff r R N) (exponent_input z R B N h.andE₁ h.andE₂.andE₁ h.andE₂.andE₂) (le_refl _) (le_refl _)
  have right := GaussianNameRingLaws.product_right_error H (ap2 Exp r e)
    (scalarSum (ap2 logExponentF (query r R N) (logExponentData z B N)) (cutoff r R N)) one (unit r)
    (GaussianNameBounds.U Exp e) (headBound R N) (unit_positive r)
    (distance_symmetric _ _ _ _ (unit_positive r) common) (GaussianNameBounds.sample_bound Exp e r ep) (head_bound z R B N h)
  exact distance_congr (uniform_at r z R B N).eqSymm (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive r) left right)

theorem original_sample_reference (p r z R B N : PTm n) (h : Γ ⊢[PRAAx] input z R B N) : Γ ⊢[PRAAx]
    distanceBounded (ap2 qF p (qData z B N)) (reference r z R B N)
      (unit r+(one+LeanProofs.IPRA.PTm.num 3*headBound R N)*unit p) (unit p*unit r) := by
  have den := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive r)
  have first := GaussianNameEquivalence.cross_at _ _ _ _ p r (original_uniform z R B N h)
  have second := distance_radius_mono _ _ _ _ (LeanProofs.IPRA.PTm.num 3*headBound R N*unit p) (unit p*unit r)
    (unit_positive r) den (le_of_eq_add (d := zero) (by ipra_ring)) (uniform_sample_reference r z R B N h)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den first second)

def finiteGain (r R N : PTm n) : PTm n := GaussianRationalRadiusExponentialLipschitz.factor (exponentRadius R N) (cutoff r R N)
def finiteBound (R N : PTm n) : PTm n := pw (LeanProofs.IPRA.PTm.num 3) (exponentRadius R N)
def inputGain (r R N : PTm n) : PTm n :=
  GaussianGammaEulerHeadContinuity.gain R N*finiteBound R N+headBound R N*finiteGain r R N*logRadius N

theorem reference_distance (r z w R B A D N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded w (R*B))
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w B) A D) : Γ ⊢[PRAAx]
    distanceBounded (reference r z R B N) (reference r w R B N)
      (inputGain r R N*A*unit (query r R N)+two*headBound R N*finiteGain r R N*D*R) (D*unit (query r R N)) := by
  let j := query r R N
  have den := positive_product _ _ hD (unit_positive j)
  have heads := GaussianGammaEulerHeadContinuity.returned_head_distance z w R B A D N (.andI hB (.andI hD (.andI hz (.andI hw hd))))
  have first := distance_radius_mono _ _ _ _ (GaussianGammaEulerHeadContinuity.gain R N*A*unit j) (D*unit j) hD den
    (le_of_eq_add (d := zero) (by ipra_ring)) heads
  have ez := exponent_bound j z R B N hN hB hz
  have ew := exponent_bound j w R B N hN hB hw
  have second := GaussianRationalRadiusExponentialLipschitz.scalar_sum_lipschitz _ _ (exponentRadius R N)
    (GaussianGammaLogExponentContinuity.distanceBudget j R A D N) (D*unit j) (cutoff r R N) den ez ew
    (GaussianGammaLogExponentContinuity.exponent_distance j z w R B A D N hN hB hD hz hd)
  have raw := GaussianNameArithmetic.product_distance _ _ _ _ (GaussianGammaEulerHeadContinuity.gain R N*A*unit j)
    (finiteGain r R N*GaussianGammaLogExponentContinuity.distanceBudget j R A D N) (D*unit j)
    (finiteBound R N) (headBound R N) den first second (GaussianPositiveExponentialMajorant.disk_bound _ _ _ ez)
    (head_bound w R B N (.andI hN (.andI hB hw)))
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold inputGain finiteGain GaussianGammaLogExponentContinuity.distanceBudget; ipra_ring) (.eqRefl _) raw

theorem finite_gain_budget (r R N : PTm n) : Γ ⊢[PRAAx] le (finiteGain r R N*unit r) (unit (query r R N)) := by
  have old := GaussianRadiusExponentialName.precision_budget (Γ := Γ) (exponentRadius R N) r
  have four : Γ ⊢[PRAAx] le one (LeanProofs.IPRA.PTm.num 4) := le_of_eq_add (d := LeanProofs.IPRA.PTm.num 3) (by ipra_ring)
  have small := mul_le_mul_right (finiteGain r R N*unit r) four
  exact le_trans (le_congr (one_mul _) (by unfold finiteGain cutoff; ipra_ring) small) old

theorem reference_distance_wide (r z w R B A D N : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D)
    (hz : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded z (R*B))
    (hw : Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded w (R*B))
    (hd : Γ ⊢[PRAAx] distanceBounded (ofGaussian z B) (ofGaussian w B) A D) : Γ ⊢[PRAAx]
    distanceBounded (reference r z R B N) (reference r w R B N)
      (inputGain r R N*A*unit r+two*headBound R N*D*R) (D*unit r) := by
  have small := mul_le_mul_right (two*headBound R N*D*D*R) (finite_gain_budget (Γ := Γ) r R N)
  have both := add_le_add₂ (le_refl (Γ := Γ) (inputGain r R N*A*unit (query r R N)*D*unit r)) small
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hD (unit_positive _))
    (positive_product _ _ hD (unit_positive _)) _ (reference_distance r z w R B A D N hN hB hD hz hw hd)
  exact le_congr (by ipra_ring) (by ipra_ring) both

def reciprocalBudget (p r R N : PTm n) : PTm n := GaussianGammaEulerApproximationName.rate R*unit p*unit r+
  N*(unit r+(LeanProofs.IPRA.PTm.num 3+LeanProofs.IPRA.PTm.num 3*headBound R N)*unit p)
@[simp] theorem subst_reciprocalBudget {l : ℕ} (σ : Fin n → PTm l) (p r R N : PTm n) :
    Syn.subst σ (reciprocalBudget p r R N) = reciprocalBudget (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ R) (Syn.subst σ N) := by
  simp [reciprocalBudget]

/-- The SAME original C7 observation is compared to the actual fixed
finite reference using the genuine C10 rate and both observation errors. -/
theorem original_C7_reference (p r z R B N : PTm n)
    (h : Γ ⊢[PRAAx] GaussianGammaEulerConvergence.source z R B N) : Γ ⊢[PRAAx]
    distanceBounded (GaussianGammaC7Name.sample p z R B) (reference r z R B N)
      (reciprocalBudget p r R N) (N*unit p*unit r) := by
  have hn := (GaussianGammaEulerConvergence.local_source z R B N h).andE₂.andE₁
  have hi : Γ ⊢[PRAAx] input z R B N := .andI hn h.andE₁.andE₂
  have den := positive_product _ _ (positive_product _ _ hn (unit_positive p)) (unit_positive r)
  have old := GaussianGammaEulerConvergence.observation_error r p z R B N h
  have first : Γ ⊢[PRAAx] distanceBounded (GaussianGammaC7Name.sample p z R B) (ap2 qF r (qData z B N))
      (GaussianGammaEulerApproximationName.rate R*unit p*unit r+N*(unit r+unit p)) (N*unit p*unit r) :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold GaussianNamedSmallPerturbationTransport.budgetNumerator GaussianGammaEulerApproximationName.rate; ipra_ring)
      (by ipra_ring)
      (distance_symmetric _ _ _ _ (positive_product _ _ (positive_product _ _ hn (unit_positive r)) (unit_positive p)) old)
  have short := distance_radius_mono _ _ _ _ (two+LeanProofs.IPRA.PTm.num 3*headBound R N) (unit r)
    (positive_product _ _ (unit_positive r) (unit_positive r)) (unit_positive r)
    (le_of_eq_add (d := zero) (by ipra_ring)) (original_sample_reference r r z R B N hi)
  have second := distance_radius_mono _ _ _ _ ((two+LeanProofs.IPRA.PTm.num 3*headBound R N)*N*unit p)
    (N*unit p*unit r) (unit_positive r) den (le_of_eq_add (d := zero) (by ipra_ring)) short
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold reciprocalBudget; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ den first second)

/-- Actual finite reference, exponential cutoff, input query and head disk. -/
def output (r z R B N : PTm n) : PTm n := pairT (reference r z R B N)
  (pairT (cutoff r R N) (pairT (query r R N) (headBound R N)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (r z R B N : PTm n) : PTm n := PTm.app outputF ![r,z,R,B,N]
@[simp] theorem subst_output {l : ℕ} (σ : Fin n → PTm l) (r z R B N : PTm n) :
    Syn.subst σ (output r z R B N) = output (Syn.subst σ r) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by simp [output]
@[simp] theorem subst_run {l : ℕ} (σ : Fin n → PTm l) (r z R B N : PTm n) :
    Syn.subst σ (run r z R B N) = run (Syn.subst σ r) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ N) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem program_at (r z R B N : PTm n) : Γ ⊢[PRAAx] run r z R B N ≐ output r z R B N := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![r,z,R,B,N]
theorem returned_reference (r z R B N : PTm n) : Γ ⊢[PRAAx] fstT (run r z R B N) ≐ reference r z R B N :=
  (congrFst (program_at r z R B N)).eqTrans (fst_pair _ _)
theorem returned_cutoff (r z R B N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run r z R B N)) ≐ cutoff r R N :=
  ((congrFst (congrSnd (program_at r z R B N))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_query (r z R B N : PTm n) : Γ ⊢[PRAAx] fstT (sndT (sndT (run r z R B N))) ≐ query r R N :=
  (((congrFst (congrSnd (congrSnd (program_at r z R B N)))).eqTrans (congrFst (congrSnd (snd_pair _ _)))).eqTrans
    (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_head_bound (r z R B N : PTm n) : Γ ⊢[PRAAx] sndT (sndT (sndT (run r z R B N))) ≐ headBound R N :=
  (((congrSnd (congrSnd (congrSnd (program_at r z R B N)))).eqTrans (congrSnd (congrSnd (snd_pair _ _)))).eqTrans
    (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_original_Euler_fixed_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (input (var 2) (var 3) (var 4) (var 5) ⟶ distanceBounded (ap2 qF (var 0) (qData (var 2) (var 4) (var 5)))
      (reference (var 1) (var 2) (var 3) (var 4) (var 5))
      (unit (var 1)+(one+LeanProofs.IPRA.PTm.num 3*headBound (var 3) (var 5))*unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (original_sample_reference _ _ _ _ _ _ Prf.hyp0))
theorem actual_original_C7_fixed_reference_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (GaussianGammaEulerConvergence.source (var 2) (var 3) (var 4) (var 5) ⟶
      distanceBounded (GaussianGammaC7Name.sample (var 0) (var 2) (var 3) (var 4)) (reference (var 1) (var 2) (var 3) (var 4) (var 5))
        (reciprocalBudget (var 0) (var 1) (var 3) (var 5)) (var 5*unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (original_C7_reference _ _ _ _ _ _ Prf.hyp0))
theorem actual_fixed_reference_finite_gain_budget_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le (finiteGain (var 0) (var 1) (var 2)*unit (var 0)) (unit (query (var 0) (var 1) (var 2)))) := closeUniv 3 (finite_gain_budget _ _ _)
theorem actual_fixed_reference_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) := closeUniv 5 (program_at _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaEulerContinuityReference
