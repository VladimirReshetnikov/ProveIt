import IPRADerivations.Analysis.Euler.Integration.GaussianEulerPowerScalingCompactRate
import IPRADerivations.Analysis.Logarithm.GaussianNamedPositiveLogarithm

/-!
# Compact power chart with named positive damping and exponent

For fixed primitive-recursive names c and r, the chart is the literal
product of c with the original exponential of r times the original
logarithm of the positive rational time. The time interval and both
parameter upper bounds give a single modulus for independent name,
time, and observation changes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerChart

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianPositiveRationalLogarithm (logF fraction)
open GaussianCompactLogarithmBounds (domain radius)
open GaussianNamedMultiplyRate (sampleBound sample_bound_at)
open GaussianEulerExponentialSubstitutionNamedKernel (innerF innerData)
open GaussianEulerExponentialNamedKernelRate (innerBound)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_fast)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedInverseRate (independentRate)
open GaussianRationalHorner (qmul positive_product qmul_canonical)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def source (F G : PR 2) (x y C₀ C R₀ R E T a b : PTm n) : Fm PTm n :=
  GaussianNamedPositiveLogarithm.source F x C₀ C ⋏
    (GaussianNamedPositiveLogarithm.source G y R₀ R ⋏ (le one E ⋏ domain a b E T))

abbrev exponentF (G : PR 2) : PR 2 := multiplyF G logF
def exponentData (G : PR 2) (y a b : PTm n) : PTm n :=
  multiplyData G logF y (GaussianPositiveRationalLogarithm.data a b)
abbrev powerF (G : PR 2) : PR 2 := innerF (exponentF G)
def powerData (G : PR 2) (y a b : PTm n) : PTm n := innerData (exponentF G) (exponentData G y a b)
abbrev nameF (F G : PR 2) : PR 2 := multiplyF F (powerF G)
def data (F G : PR 2) (x y a b : PTm n) : PTm n := multiplyData F (powerF G) x (powerData G y a b)
def exponentRadius (R E T : PTm n) : PTm n := R*radius E T
def majorant (C R E T : PTm n) : PTm n := C*innerBound (exponentRadius R E T)
def gain (C R E T D₀ D₁ D₂ : PTm n) : PTm n :=
  innerBound (exponentRadius R E T)*(D₀+C*(radius E T*D₁+R*(E*D₂)))

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (x y C₀ C R₀ R E T a b : PTm n) :
    (source F G x y C₀ C R₀ R E T a b).subst σ =
      source F G (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ C₀) (Syn.subst σ C) (Syn.subst σ R₀)
        (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ a) (Syn.subst σ b) := by simp [source,domain]

@[simp] theorem subst_exponentData {m : ℕ} (σ : Fin n → PTm m) (G : PR 2) (y a b : PTm n) :
    Syn.subst σ (exponentData G y a b) = exponentData G (Syn.subst σ y) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [exponentData]
@[simp] theorem subst_powerData {m : ℕ} (σ : Fin n → PTm m) (G : PR 2) (y a b : PTm n) :
    Syn.subst σ (powerData G y a b) = powerData G (Syn.subst σ y) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [powerData,innerData,GaussianGammaFiniteApproximantName.exponentialInputData]
@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (F G : PR 2) (x y a b : PTm n) :
    Syn.subst σ (data F G x y a b) = data F G (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ a) (Syn.subst σ b) := by simp [data]
@[simp] theorem subst_exponentRadius {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (exponentRadius R E T) = exponentRadius (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [exponentRadius,radius,one]

theorem positive_observation_bound (F : PR 2) (p x E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x E T) :
    Γ ⊢[PRAAx] bounded (ap2 F p x) T one := by
  have d := GaussianNamedPositiveLogarithm.decoded_domain F p x E T h
  have eq := GaussianNamedPositiveLogarithm.decoded_value F p x E T h
  exact bound_congr eq (.eqRefl _) (.eqRefl _)
    (GaussianEulerExponentCompactBounds.fraction_bound _ _ T d.andE₁.andE₂ d.andE₂.andE₂)

theorem positive_samples (F : PR 2) (x E T : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F x E T) :
    Γ ⊢[PRAAx] sampleBound F x T := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianNamedPositiveLogarithm.source F (Syn.shift x) (Syn.shift E) (Syn.shift T) :=
    by simpa only [Fm.shift,GaussianNamedPositiveLogarithm.subst_source,Syn.shift] using h.shift
  exact .allI (positive_observation_bound F (var 0) (Syn.shift x) (Syn.shift E) (Syn.shift T) hs)

theorem log_samples (a b E T : PTm n) (hE : Γ ⊢[PRAAx] le one E) (h : Γ ⊢[PRAAx] domain a b E T) :
    Γ ⊢[PRAAx] sampleBound logF (GaussianPositiveRationalLogarithm.data a b) (radius E T) := by
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift E) := by simpa [Fm.shift,Syn.shift,one] using hE.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) :=
    by simpa [Fm.shift,Syn.shift,domain] using h.shift
  refine .allI ?_
  simpa [sampleBound,radius,Syn.shift,GaussianPositiveRationalLogarithm.sample] using
    GaussianCompactLogarithmBounds.sample_bound (var 0) (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) es hs

theorem product_observation_bound (F G : PR 2) (p x y M N : PTm n)
    (hM : Γ ⊢[PRAAx] sampleBound F x M) (hN : Γ ⊢[PRAAx] sampleBound G y N) : Γ ⊢[PRAAx]
    bounded (ap2 (multiplyF F G) p (multiplyData F G x y)) (M*N) one := by
  let k := GaussianFastValueCut.exponent (multiplyModulus F G x y) p
  have read := (GaussianNameArithmetic.multiply_at (Γ := Γ) F G x y p).eqTrans
    (GaussianExponentialReference.recode_fixed (qmul (ap2 F k x) (ap2 G k y)) (qmul_canonical _ _))
  exact bound_congr read.eqSymm (.eqRefl _) (one_mul _)
    (bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one) (sample_bound_at F x M k hM) (sample_bound_at G y N k hN))

theorem exponent_input (G : PR 2) (y R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] domain a b E T) :
    Γ ⊢[PRAAx] GaussianRadiusExponentialName.input (exponentF G) (exponentRadius R E T) (exponentData G y a b) := by
  refine .andI (multiply_fast G logF _ _ h.andE₁ (GaussianPositiveRationalLogarithm.name_regular a b ht.andE₁)) (.allI ?_)
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G (sh y) (sh R₀) (sh R) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (sh E) := by simpa [Fm.shift,Syn.shift,one,sh] using hE.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] domain (sh a) (sh b) (sh E) (sh T) :=
    by simpa [Fm.shift,Syn.shift,domain,sh] using ht.shift
  have bound : Γ.map Fm.shift ⊢[PRAAx]
      bounded (ap2 (exponentF G) (var 0) (exponentData G (sh y) (sh a) (sh b))) (exponentRadius (sh R) (sh E) (sh T)) one :=
    product_observation_bound G logF (var 0) (sh y) (GaussianPositiveRationalLogarithm.data (sh a) (sh b))
      (sh R) (radius (sh E) (sh T)) (positive_samples G (sh y) (sh R₀) (sh R) hs)
      (log_samples (sh a) (sh b) (sh E) (sh T) es ts)
  simpa only [GaussianRadiusExponentialName.boundedSamples,subst_exponentData,subst_exponentRadius,Syn.shift,sh] using bound

theorem power_regular (G : PR 2) (y R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] domain a b E T) :
    Γ ⊢[PRAAx] pointCN (powerF G) (powerData G y a b) :=
  GaussianRadiusExponentialName.name_regular _ _ _ (GaussianGammaFiniteApproximantName.exponential_input _ _
    (exponent_input G y R₀ R E T a b h hE ht).andE₁)

theorem power_samples (G : PR 2) (y R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G y R₀ R)
    (hE : Γ ⊢[PRAAx] le one E) (ht : Γ ⊢[PRAAx] domain a b E T) :
    Γ ⊢[PRAAx] sampleBound (powerF G) (powerData G y a b) (innerBound (exponentRadius R E T)) := by
  let sh (t : PTm n) := Syn.shift t
  have hs : Γ.map Fm.shift ⊢[PRAAx] GaussianNamedPositiveLogarithm.source G (sh y) (sh R₀) (sh R) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift
  have es : Γ.map Fm.shift ⊢[PRAAx] le one (sh E) := by simpa [Fm.shift,Syn.shift,one,sh] using hE.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] domain (sh a) (sh b) (sh E) (sh T) :=
    by simpa [Fm.shift,Syn.shift,domain,sh] using ht.shift
  refine .allI ?_
  have bound : Γ.map Fm.shift ⊢[PRAAx]
      bounded (ap2 (powerF G) (var 0) (powerData G (sh y) (sh a) (sh b))) (innerBound (exponentRadius (sh R) (sh E) (sh T))) one :=
    GaussianEulerExponentialNamedKernelRate.inner_observation_bound (exponentF G) (var 0) (exponentRadius (sh R) (sh E) (sh T))
      (exponentData G (sh y) (sh a) (sh b)) (exponent_input G (sh y) (sh R₀) (sh R) (sh E) (sh T) (sh a) (sh b) hs es ts)
  simpa only [sampleBound,subst_powerData,GaussianEulerExponentialNamedKernelRate.subst_innerBound,
    subst_exponentRadius,Syn.shift,sh] using bound

theorem name_regular (F G : PR 2) (x y C₀ C R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source F G x y C₀ C R₀ R E T a b) : Γ ⊢[PRAAx] pointCN (nameF F G) (data F G x y a b) :=
  multiply_fast F (powerF G) x _ h.andE₁.andE₁
    (power_regular G y R₀ R E T a b h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂)

theorem original_observation_bound (F G : PR 2) (p x y C₀ C R₀ R E T a b : PTm n)
    (h : Γ ⊢[PRAAx] source F G x y C₀ C R₀ R E T a b) : Γ ⊢[PRAAx]
    bounded (ap2 (nameF F G) p (data F G x y a b)) (majorant C R E T) one :=
  product_observation_bound F (powerF G) p x _ C _ (positive_samples F x C₀ C h.andE₁)
    (power_samples G y R₀ R E T a b h.andE₂.andE₁ h.andE₂.andE₂.andE₁ h.andE₂.andE₂.andE₂)

theorem product_same_denominator (F G F' G' : PR 2) (x y u v A C D M R : PTm n)
    (hD : Γ ⊢[PRAAx] le one D)
    (hf : Γ ⊢[PRAAx] pointCN F x) (hg : Γ ⊢[PRAAx] pointCN G y)
    (hfp : Γ ⊢[PRAAx] pointCN F' u) (hgp : Γ ⊢[PRAAx] pointCN G' v)
    (hM : Γ ⊢[PRAAx] sampleBound G y M) (hR : Γ ⊢[PRAAx] sampleBound F' u R)
    (ha : Γ ⊢[PRAAx] independentRate F F' x u A D)
    (hc : Γ ⊢[PRAAx] independentRate G G' y v C D) :
    Γ ⊢[PRAAx] independentRate (multiplyF F G) (multiplyF F' G') (multiplyData F G x y) (multiplyData F' G' u v)
      (M*A+R*C) D := by
  have raw := GaussianNamedMultiplyRate.independent_rate F G F' G' x y u v A D C D M R hD hD hf hg hfp hgp hM hR ha hc
  have same : Γ ⊢[PRAAx] ((M*A+R*C)*(D*D)) ≐ GaussianNamedMultiplyRate.leadingNumerator A D C D M R*D := by
    unfold GaussianNamedMultiplyRate.leadingNumerator
    ipra_ring
  exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _
    (positive_product _ _ hD hD) hD
    (le_congr same (.eqRefl _) (le_refl _)) raw

theorem original_rate (F G F' G' : PR 2) (x y u v C₀ C R₀ R E T a b a' b' A₀ A₁ A₂ D : PTm n)
    (h : Γ ⊢[PRAAx] source F G x y C₀ C R₀ R E T a b)
    (h' : Γ ⊢[PRAAx] source F' G' u v C₀ C R₀ R E T a' b')
    (hD : Γ ⊢[PRAAx] le one D)
    (h₀ : Γ ⊢[PRAAx] independentRate F F' x u A₀ D)
    (h₁ : Γ ⊢[PRAAx] independentRate G G' y v A₁ D)
    (h₂ : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction a' b') A₂ D) :
    Γ ⊢[PRAAx] independentRate (nameF F G) (nameF F' G') (data F G x y a b) (data F' G' u v a' b')
      (gain C R E T A₀ A₁ A₂) D := by
  let M := innerBound (exponentRadius R E T)
  let L := radius E T
  let K := L*A₁+R*(E*A₂)
  have hz := h.andE₂.andE₁
  have hw := h'.andE₂.andE₁
  have ht := h.andE₂.andE₂.andE₂
  have ht' := h'.andE₂.andE₂.andE₂
  have hE := h.andE₂.andE₂.andE₁
  have lg := GaussianPositiveRationalLogarithm.name_regular a b ht.andE₁
  have lg' := GaussianPositiveRationalLogarithm.name_regular a' b' ht'.andE₁
  have dt := GaussianCompactLogarithmBounds.original_log_rate a b a' b' E A₂ D ht.andE₁ ht'.andE₁ hD
    ht.andE₂.andE₁ ht'.andE₂.andE₁ h₂
  have rate : Γ ⊢[PRAAx] independentRate (exponentF G) (exponentF G') (exponentData G y a b) (exponentData G' v a' b') K D :=
    product_same_denominator G logF G' logF y _ v _ A₁ (E*A₂) D L R hD hz.andE₁ lg hw.andE₁ lg'
      (log_samples a b E T hE ht) (positive_samples G' v R₀ R hw) h₁ dt
  have e := GaussianEulerExponentialNamedKernelRate.inner_rate (exponentF G) (exponentF G') (exponentRadius R E T)
    (exponentData G y a b) (exponentData G' v a' b') K D
    (exponent_input G y R₀ R E T a b hz hE ht) (exponent_input G' v R₀ R E T a' b' hw hE ht') hD rate
  have r := product_same_denominator F (powerF G) F' (powerF G') x _ u _ A₀ (M*K) D M C hD
    h.andE₁.andE₁ (power_regular G y R₀ R E T a b hz hE ht)
    h'.andE₁.andE₁ (power_regular G' v R₀ R E T a' b' hw hE ht')
    (power_samples G y R₀ R E T a b hz hE ht) (positive_samples F' u C₀ C h'.andE₁) h₀ e
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _
    (by unfold gain; dsimp only [M,K,L]; ipra_ring) r

theorem actual_original_named_power_chart_compact_rate_closed (F G F' G' : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18
      ((source F G (var 0) (var 1) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⋏
        source F' G' (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 12) (var 13)) ⟶
      ((le one (var 17) ⋏ independentRate F F' (var 0) (var 2) (var 14) (var 17)) ⋏
        (independentRate G G' (var 1) (var 3) (var 15) (var 17) ⋏
          distanceBounded (fraction (var 10) (var 11)) (fraction (var 12) (var 13)) (var 16) (var 17))) ⟶
      independentRate (nameF F G) (nameF F' G') (data F G (var 0) (var 1) (var 10) (var 11))
        (data F' G' (var 2) (var 3) (var 12) (var 13))
        (gain (var 5) (var 7) (var 8) (var 9) (var 14) (var 15) (var 16)) (var 17)) :=
  closeUniv 18 (.impI (.impI (original_rate F G F' G' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedDampingPowerChart
