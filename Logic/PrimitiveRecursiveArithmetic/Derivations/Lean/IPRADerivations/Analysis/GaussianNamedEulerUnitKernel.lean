import IPRADerivations.Analysis.GaussianUnitIntervalInputDecoding
import IPRADerivations.Analysis.GaussianEulerUnitKernelCompactRate
import IPRADerivations.Analysis.GaussianCompactRiemannName

/-!
# The actual unit-interval Euler kernel on a regular real input

Every actual input observation is assumed real and between 1/E and
1-1/E by ordinary scalar order. Its original raw denominator and signed
numerator are decoded by the proved positive-fraction bridge. The
unchanged rational unit kernel is sampled at that actual fraction.
Fast(L,p+1) pays the inner input error and the outer query p+1 pays
the other half. Properness retains independent input and output clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitKernel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianCompactRiemannName (field0 field1 field2 field3 field4)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev lipschitz := @GaussianEulerUnitKernelCompactRate.lipschitz
def clock (p R E : PTm n) : PTm n := GaussianFastValueCut.exponent (lipschitz R E) (succ p)
def admissibleSamples (f : PR 2) (x E : PTm n) : Fm PTm n := .all
  (GaussianUnitIntervalInputDecoding.source (ap2 f (var 0) (Syn.shift x)) (Syn.shift E))
def source (f : PR 2) (x z R B E : PTm n) : Fm PTm n :=
  GaussianEulerExponentCompactBounds.source z R B E ⋏ (pointCN f x ⋏ admissibleSamples f x E)
def encodedData (f : PR 2) (r x z B : PTm n) : PTm n := GaussianEulerUnitSubstitutionKernel.data z B
  (GaussianUnitIntervalInputDecoding.numerator (ap2 f r x)) (GaussianUnitIntervalInputDecoding.denominator (ap2 f r x))
def observation (f : PR 2) (p x z R B E : PTm n) : PTm n :=
  ap2 GaussianEulerUnitSubstitutionKernel.nameF (succ p) (encodedData f (clock p R E) x z B)
def data (x z R B E : PTm n) : PTm n := GaussianCompactRiemannName.sampleData x z R B E zero
def nameF (f : PR 2) : PR 2 := PTm.toPR
  (observation f (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1)))

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p R E : PTm n) :
    Syn.subst σ (clock p R E) = clock (Syn.subst σ p) (Syn.subst σ R) (Syn.subst σ E) := by simp [clock]
@[simp] theorem subst_admissibleSamples {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x E : PTm n) :
    (admissibleSamples f x E).subst σ = admissibleSamples f (Syn.subst σ x) (Syn.subst σ E) := by
  simp [admissibleSamples,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (x z R B E : PTm n) :
    (source f x z R B E).subst σ = source f (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) := by simp [source]
@[simp] theorem subst_encodedData {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (r x z B : PTm n) :
    Syn.subst σ (encodedData f r x z B) = encodedData f (Syn.subst σ r) (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ B) := by simp [encodedData]
@[simp] theorem subst_observation {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (p x z R B E : PTm n) :
    Syn.subst σ (observation f p x z R B E) = observation f (Syn.subst σ p) (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) := by simp [observation]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (x z R B E : PTm n) :
    Syn.subst σ (data x z R B E) = data (Syn.subst σ x) (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ E) := by simp [data]

/-- Literal readback of the original rational kernel and both real queries. -/
theorem sample_at (f : PR 2) (p x z R B E : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF f) p (data x z R B E) ≐ observation f p x z R B E := by
  have raw : Γ ⊢[PRAAx] ap2 (nameF f) p (data x z R B E) ≐ observation f p
      (field0 (data x z R B E)) (field1 (data x z R B E)) (field2 (data x z R B E))
      (field3 (data x z R B E)) (field4 (data x z R B E)) := by
    simpa [nameF,ap2] using toPR_eq (Γ := Γ)
      (observation f (var 0) (field0 (var 1)) (field1 (var 1)) (field2 (var 1)) (field3 (var 1)) (field4 (var 1)) : PTm 2) ![p,data x z R B E]
  have fields := Prf.eqCongr (Ax := PRAAx) (Γ := Γ)
    (observation f (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) : PTm 6)
    (σ := ![p,field0 (data x z R B E),field1 (data x z R B E),field2 (data x z R B E),field3 (data x z R B E),field4 (data x z R B E)])
    (σ' := ![p,x,z,R,B,E]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact GaussianCompactRiemannName.field0_at _ _ _ _ _ _
      exact GaussianCompactRiemannName.field1_at _ _ _ _ _ _
      exact GaussianCompactRiemannName.field2_at _ _ _ _ _ _
      exact GaussianCompactRiemannName.field3_at _ _ _ _ _ _
      exact GaussianCompactRiemannName.field4_at _ _ _ _ _ _)
  exact raw.eqTrans (by simpa using fields)

theorem sample_canonical (f : PR 2) (p x z R B E : PTm n) : Γ ⊢[PRAAx]
    GaussianRationalHorner.canonical (ap2 (nameF f) p (data x z R B E)) := by
  let a := GaussianUnitIntervalInputDecoding.numerator (ap2 f (clock p R E) x)
  let b := GaussianUnitIntervalInputDecoding.denominator (ap2 f (clock p R E) x)
  exact GaussianRationalHorner.canonical_congr (sample_at f p x z R B E)
    (GaussianRadiusExponentialName.sample_canonical GaussianEulerUnitSubstitutionKernel.exponentF
      (GaussianEulerUnitSubstitutionKernel.radius z B a b) (succ p)
      (GaussianEulerUnitSubstitutionKernel.exponentData z B a b))

theorem source_at (f : PR 2) (r x z R B E : PTm n) (h : Γ ⊢[PRAAx] source f x z R B E) : Γ ⊢[PRAAx]
    GaussianUnitIntervalInputDecoding.source (ap2 f r x) E := by
  simpa [admissibleSamples] using h.andE₂.andE₂.allE r

theorem encoded_source (f : PR 2) (r x z R B E : PTm n) (h : Γ ⊢[PRAAx] source f x z R B E) : Γ ⊢[PRAAx]
    GaussianEulerUnitKernelCompactRate.source z R B (GaussianUnitIntervalInputDecoding.numerator (ap2 f r x))
      (GaussianUnitIntervalInputDecoding.denominator (ap2 f r x)) E :=
  .andI h.andE₁ (GaussianUnitIntervalInputDecoding.decoded_source _ E (source_at f r x z R B E h))

theorem original_bound (f : PR 2) (p x z R B E : PTm n) (h : Γ ⊢[PRAAx] source f x z R B E) : Γ ⊢[PRAAx]
    GaussianRationalMetric.bounded (ap2 (nameF f) p (data x z R B E)) (GaussianEulerUnitKernelCompactRate.majorant R E) one :=
  GaussianRationalReciprocal.bound_congr (sample_at f p x z R B E).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerUnitKernelCompactRate.original_bound (succ p) z R B _ _ E (encoded_source f (clock p R E) x z R B E h))

private theorem decoded_input_distance (f g : PR 2) (r s x y z R B E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x z R B E) (hg : Γ ⊢[PRAAx] source g y z R B E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded
      (GaussianPositiveRationalLogarithm.fraction (GaussianUnitIntervalInputDecoding.numerator (ap2 f r x)) (GaussianUnitIntervalInputDecoding.denominator (ap2 f r x)))
      (GaussianPositiveRationalLogarithm.fraction (GaussianUnitIntervalInputDecoding.numerator (ap2 g s y)) (GaussianUnitIntervalInputDecoding.denominator (ap2 g s y)))
      (unit r+unit s) (unit r*unit s) :=
  distance_congr (GaussianUnitIntervalInputDecoding.fraction_recode _ E (source_at f r x z R B E hf)).eqSymm
    (GaussianUnitIntervalInputDecoding.fraction_recode _ E (source_at g s y z R B E hg)).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianFastValueCut.recode_distance_bound _ _ _ _ (positive_product _ _ (unit_positive r) (unit_positive s))
      (GaussianNameEquivalence.cross_at f g x y r s he))

theorem observation_regularity (f g : PR 2) (p q x y z R B E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x z R B E) (hg : Γ ⊢[PRAAx] source g y z R B E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (observation f p x z R B E) (observation g q y z R B E) (unit p+unit q) (unit p*unit q) := by
  let r := clock p R E
  let s := clock q R E
  let A := unit r+unit s
  let D := unit r*unit s
  let L := lipschitz R E
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (unit_positive r) (unit_positive s)
  have hi : Γ ⊢[PRAAx] GaussianEulerUnitKernelCompactRate.input z R B
      (GaussianUnitIntervalInputDecoding.numerator (ap2 f r x)) (GaussianUnitIntervalInputDecoding.denominator (ap2 f r x))
      (GaussianUnitIntervalInputDecoding.numerator (ap2 g s y)) (GaussianUnitIntervalInputDecoding.denominator (ap2 g s y)) E A D :=
    .andI (encoded_source f r x z R B E hf) (.andI (encoded_source g s y z R B E hg)
      (.andI hD (decoded_input_distance f g r s x y z R B E hf hg he)))
  have raw := GaussianEulerUnitKernelCompactRate.original_observations (succ p) (succ q) z R B
    (GaussianUnitIntervalInputDecoding.numerator (ap2 f r x)) (GaussianUnitIntervalInputDecoding.denominator (ap2 f r x))
    (GaussianUnitIntervalInputDecoding.numerator (ap2 g s y)) (GaussianUnitIntervalInputDecoding.denominator (ap2 g s y)) E A D hi
  have up : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p := (pw_succ two p).eqTrans (mul_comm _ _)
  have uq : Γ ⊢[PRAAx] unit (succ q) ≐ two*unit q := (pw_succ two q).eqTrans (mul_comm _ _)
  have bp : Γ ⊢[PRAAx] le (two*L*unit p) (unit r) :=
    le_congr ((congrMul (.eqRefl L) up).eqTrans (by ipra_ring)) (.eqRefl _) (GaussianFastValueCut.query_budget L (succ p))
  have bq : Γ ⊢[PRAAx] le (two*L*unit q) (unit s) :=
    le_congr ((congrMul (.eqRefl L) uq).eqTrans (by ipra_ring)) (.eqRefl _) (GaussianFastValueCut.query_budget L (succ q))
  have eN : Γ ⊢[PRAAx] rateNumerator (L*A) D (succ p) (succ q) ≐
      (L*A)*(two*unit p)*(two*unit q)+D*(two*unit p+two*unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) uq) (congrMul (.eqRefl _) (congrAdd up uq))
  have eD : Γ ⊢[PRAAx] rateDenominator D (succ p) (succ q) ≐ D*(two*unit p)*(two*unit q) :=
    congrMul (congrMul (.eqRefl _) up) uq
  have adjusted := distance_congr (.eqRefl _) (.eqRefl _) eN eD raw
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hD (positive_product _ _ (zero_lt_succ one) (unit_positive p)))
      (positive_product _ _ (zero_lt_succ one) (unit_positive q)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (by
      dsimp only [A,D]
      ipra_le (2*𝔞(unit p)*𝔞(unit q)*𝔞(unit s)*𝔞(unit q))*sl bp+
        (2*𝔞(unit p)*𝔞(unit q)*𝔞(unit r)*𝔞(unit p))*sl bq) adjusted

theorem original_observations (f g : PR 2) (p q x y z R B E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x z R B E) (hg : Γ ⊢[PRAAx] source g y z R B E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data x z R B E)) (ap2 (nameF g) q (data y z R B E)) (unit p+unit q) (unit p*unit q) :=
  distance_congr (sample_at f p x z R B E).eqSymm (sample_at g q y z R B E).eqSymm (.eqRefl _) (.eqRefl _)
    (observation_regularity f g p q x y z R B E hf hg he)

theorem proper (f g : PR 2) (x y z R B E : PTm n)
    (hf : Γ ⊢[PRAAx] source f x z R B E) (hg : Γ ⊢[PRAAx] source g y z R B E)
    (he : Γ ⊢[PRAAx] crossEquivalent f g x y) : Γ ⊢[PRAAx]
    crossEquivalent (nameF f) (nameF g) (data x z R B E) (data y z R B E) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have hhf : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source f (sh x) (sh z) (sh R) (sh B) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using hf.shift.shift
  have hhg : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] source g (sh y) (sh z) (sh R) (sh B) (sh E) :=
    by simpa [Fm.shift,Syn.shift,sh] using hg.shift.shift
  have hhe : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] crossEquivalent f g (sh x) (sh y) :=
    by simpa [Fm.shift,Syn.shift,sh] using he.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,subst_data,Syn.shift,sh] using
    original_observations f g (var 1) (var 0) (sh x) (sh y) (sh z) (sh R) (sh B) (sh E) hhf hhg hhe

theorem name_regular (f : PR 2) (x z R B E : PTm n) (h : Γ ⊢[PRAAx] source f x z R B E) : Γ ⊢[PRAAx]
    pointCN (nameF f) (data x z R B E) := by
  simpa only [pointCN,GaussianEuclideanPointDistance.unit,GaussianCoefficientNameBounds.unit,crossEquivalent] using
    proper f f x x z R B E h h (GaussianNameEquivalence.cross_refl f x h.andE₂.andE₁)

theorem actual_regular_unit_kernel_on_named_input_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (source f (var 0) (var 1) (var 2) (var 3) (var 4) ⟶ pointCN (nameF f) (data (var 0) (var 1) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (.impI (name_regular f _ _ _ _ _ Prf.hyp0))

theorem actual_named_unit_kernel_proper_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (source f (var 0) (var 2) (var 3) (var 4) (var 5) ⟶ (source g (var 1) (var 2) (var 3) (var 4) (var 5) ⟶
      (crossEquivalent f g (var 0) (var 1) ⟶ crossEquivalent (nameF f) (nameF g)
        (data (var 0) (var 2) (var 3) (var 4) (var 5)) (data (var 1) (var 2) (var 3) (var 4) (var 5))))) :=
  closeUniv 6 (.impI (.impI (.impI (proper f g _ _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp0.wk Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianNamedEulerUnitKernel
