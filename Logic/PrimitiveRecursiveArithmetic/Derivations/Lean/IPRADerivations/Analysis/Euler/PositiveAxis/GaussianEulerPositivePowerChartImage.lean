import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerPositivePowerChartLower
import IPRADerivations.Analysis.Names.GaussianPositiveCompactInputDecoding

/-!
# Literal rational image nodes from the actual positive power chart

The query is uniform over the source time compact. Its original chart
sample is canonical, real and bounded below by a true reciprocal margin.
The original scalar decoder therefore returns positive numerical a'/b'
whose actual Gaussian fraction is CODE-EQUAL to that same chart sample.
Independent original chart observations retain their own two dyadic
errors. No rounded-node or image-coordinate premise is supplied.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImage

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPositivePowerChart (source nameF data majorant)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianPositiveRationalLogarithm (fraction)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def reciprocalMargin (h Q E T : PTm n) : PTm n := two*GaussianEulerPositivePowerChartLower.denominator h Q E T
def query (p h Q E T : PTm n) : PTm n := GaussianFastValueCut.exponent (reciprocalMargin h Q E T) p
def sample (p e f d h Q S E T a b : PTm n) : PTm n := ap2 nameF (query p h Q E T) (data e f d h S a b)
def numerator (p e f d h Q S E T a b : PTm n) : PTm n := GaussianUnitIntervalInputDecoding.numerator (sample p e f d h Q S E T a b)
def denominator (p e f d h Q S E T a b : PTm n) : PTm n := GaussianUnitIntervalInputDecoding.denominator (sample p e f d h Q S E T a b)
def imageData (p e f d h Q S E T a b : PTm n) : PTm n :=
  pairT (numerator p e f d h Q S E T a b) (denominator p e f d h Q S E T a b)
@[simp] theorem subst_reciprocalMargin {m : ℕ} (σ : Fin n → PTm m) (h Q E T : PTm n) :
    Syn.subst σ (reciprocalMargin h Q E T) = reciprocalMargin (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ E) (Syn.subst σ T) := by simp [reciprocalMargin]
@[simp] theorem subst_query {m : ℕ} (σ : Fin n → PTm m) (p h Q E T : PTm n) :
    Syn.subst σ (query p h Q E T) = query (Syn.subst σ p) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ E) (Syn.subst σ T) := by simp [query]
@[simp] theorem subst_sample {m : ℕ} (σ : Fin n → PTm m) (p e f d h Q S E T a b : PTm n) :
    Syn.subst σ (sample p e f d h Q S E T a b) = sample (Syn.subst σ p) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by simp [sample]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p e f d h Q S E T a b : PTm n) :
    Syn.subst σ (numerator p e f d h Q S E T a b) = numerator (Syn.subst σ p) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by simp [numerator]
@[simp] theorem subst_denominator {m : ℕ} (σ : Fin n → PTm m) (p e f d h Q S E T a b : PTm n) :
    Syn.subst σ (denominator p e f d h Q S E T a b) = denominator (Syn.subst σ p) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by simp [denominator]
@[simp] theorem subst_imageData {m : ℕ} (σ : Fin n → PTm m) (p e f d h Q S E T a b : PTm n) :
    Syn.subst σ (imageData p e f d h Q S E T a b) = imageData (Syn.subst σ p) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by simp [imageData]

theorem margin_positive (h Q E T : PTm n) (hh : Γ ⊢[PRAAx] le one h) : Γ ⊢[PRAAx] le one (reciprocalMargin h Q E T) :=
  positive_product _ _ (le_succ_self one) (positive_product _ _ hh (GaussianEulerPositivePowerChartLower.power_denominator_positive Q E T))

theorem query_later (p h Q E T : PTm n) : Γ ⊢[PRAAx] le p (query p h Q E T) := le_add_right _ _

theorem query_budget (p h Q E T : PTm n) : Γ ⊢[PRAAx] le (reciprocalMargin h Q E T) (unit (query p h Q E T)) :=
  le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (reciprocalMargin h Q E T) (unit_positive p)))
    (GaussianFastValueCut.query_budget (reciprocalMargin h Q E T) p)

theorem original_sample_source (p e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    GaussianPositiveCompactInputDecoding.source (sample p e f d h Q S E T a b) (reciprocalMargin h Q E T) (majorant Q S E T) :=
  .andI (GaussianEulerPositivePowerChartLower.original_sample_real (query p h Q E T) e f d h S a b hs.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₁.andE₂).andE₂
    (.andI (margin_positive h Q E T hs.andE₁.andE₂.andE₁.andE₂)
      (.andI (GaussianEulerPositivePowerChartLower.original_positive_sample (query p h Q E T) e f d h Q S E T a b hs (query_budget p h Q E T))
        (GaussianEulerPositivePowerChart.original_bound (query p h Q E T) e f d h Q S E T a b hs)))

/-- The original image fraction is literal, with no extra observation error. -/
theorem fraction_exact (p e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    fraction (numerator p e f d h Q S E T a b) (denominator p e f d h Q S E T a b) ≐ sample p e f d h Q S E T a b :=
  GaussianPositiveCompactInputDecoding.fraction_exact _ _ _ (original_sample_source p e f d h Q S E T a b hs)
    (GaussianEulerPositivePowerChartLower.original_sample_real (query p h Q E T) e f d h S a b hs.andE₁.andE₁.andE₂ hs.andE₁.andE₂.andE₁.andE₂).andE₁

theorem image_domain (p e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    GaussianCompactLogarithmBounds.domain (numerator p e f d h Q S E T a b) (denominator p e f d h Q S E T a b)
      (reciprocalMargin h Q E T) (majorant Q S E T) :=
  GaussianPositiveCompactInputDecoding.decoded_source _ _ _ (original_sample_source p e f d h Q S E T a b hs)

/-- Independent original chart observations are compared with the literal
decoded image node at a uniformly retimed query. -/
theorem original_observations (p q e f d h Q S E T a b : PTm n)
    (hs : Γ ⊢[PRAAx] source e f d h Q S E T a b) : Γ ⊢[PRAAx]
    distanceBounded (fraction (numerator p e f d h Q S E T a b) (denominator p e f d h Q S E T a b))
      (ap2 nameF q (data e f d h S a b)) (unit p+unit q) (unit p*unit q) := by
  let t := query p h Q E T
  have near := GaussianNameEquivalence.point_at nameF (data e f d h S a b) t q
    (GaussianEulerPositivePowerChart.name_regular e f d h Q S E T a b hs)
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) (query_later p h Q E T)
  have coarse := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ (unit p+unit q) (unit p*unit q)
    (positive_product _ _ (unit_positive t) (unit_positive q)) (positive_product _ _ (unit_positive p) (unit_positive q))
    (by ipra_le (𝔞 (unit q))^2*sl grow) near
  exact GaussianRationalDistanceOrder.distance_congr (fraction_exact p e f d h Q S E T a b hs).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) coarse

/-- One actual PR program returns the literal positive rational image node. -/
def imageF : PR 11 := PTm.toPR (imageData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
def run (p e f d h Q S E T a b : PTm n) : PTm n := PTm.app imageF ![p,e,f,d,h,Q,S,E,T,a,b]

@[simp] theorem subst_run {m : ℕ} (σ : Fin n → PTm m) (p e f d h Q S E T a b : PTm n) :
    Syn.subst σ (run p e f d h Q S E T a b) = run (Syn.subst σ p) (Syn.subst σ e) (Syn.subst σ f)
      (Syn.subst σ d) (Syn.subst σ h) (Syn.subst σ Q) (Syn.subst σ S) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [run,ConciseIPRA.PTm.subst_app]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem program_at (p e f d h Q S E T a b : PTm n) : Γ ⊢[PRAAx]
    run p e f d h Q S E T a b ≐ imageData p e f d h Q S E T a b := by
  have decoded : Syn.subst ![p,e,f,d,h,Q,S,E,T,a,b]
      (imageData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) : PTm 11) = imageData p e f d h Q S E T a b := by
    simp only [subst_imageData,Syn.subst_var]
    rfl
  simpa only [run,imageF,decoded] using toPR_eq (Γ := Γ)
    (imageData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) : PTm 11) ![p,e,f,d,h,Q,S,E,T,a,b]

theorem returned_numerator (p e f d h Q S E T a b : PTm n) : Γ ⊢[PRAAx]
    fstT (run p e f d h Q S E T a b) ≐ numerator p e f d h Q S E T a b :=
  (congrFst (program_at p e f d h Q S E T a b)).eqTrans (fst_pair _ _)
theorem returned_denominator (p e f d h Q S E T a b : PTm n) : Γ ⊢[PRAAx]
    sndT (run p e f d h Q S E T a b) ≐ denominator p e f d h Q S E T a b :=
  (congrSnd (program_at p e f d h Q S E T a b)).eqTrans (snd_pair _ _)

theorem actual_literal_positive_power_chart_image_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ⟶
      (GaussianCompactLogarithmBounds.domain
        (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
        (denominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
        (reciprocalMargin (var 4) (var 5) (var 7) (var 8)) (majorant (var 5) (var 6) (var 7) (var 8)) ⋏
      fraction (numerator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
        (denominator (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)) ≐
        sample (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))) :=
  closeUniv 11 (.impI (.andI (image_domain _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0) (fraction_exact _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0)))

theorem actual_positive_power_chart_image_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    (run (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) ≐
      imageData (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10)) :=
  closeUniv 11 (program_at _ _ _ _ _ _ _ _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerPositivePowerChartImage
