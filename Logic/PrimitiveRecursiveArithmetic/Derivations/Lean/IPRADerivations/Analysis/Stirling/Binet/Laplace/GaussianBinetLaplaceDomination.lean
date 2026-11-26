import IPRADerivations.Analysis.Stirling.Binet.Laplace.GaussianBinetLaplaceDecay
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetKernelUpper
import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetKernelPositive
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayOrder

/-!
# Pointwise domination of the actual Binet Laplace integrand

The actual complex product obeys the sharp limiting majorant
(e^{-Xt/D}/12). Its two factors are sampled at the existing multiplication
clock. The real exponential may be observed independently in its original
nonnegative representative, with all finite observation errors explicit.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetLaplaceDomination

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ComplexLogarithmRemainder (normSq normSq_code)
open GaussianBinetKernelRows (inputData)
open GaussianBinetLaplaceIntegrand (input factorClock cofinalF cofinalData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerDecayOrder (signedTime original_decay_nonnegative_representative)
open GaussianEulerIntegrandName (decayF decayData)
open GaussianPositiveRealArithmetic (positive numerator natural_representation)
open GaussianRationalHorner (canonical positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData sample_canonical sample_nonnegative)
open RationalGaussianEmbedding (native canonical_axis_roundtrip embed_from_representation)
open RationalSupMetric (denominatorOf)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "ExpF" => GaussianBinetLaplaceExponential.nameF
local notation "expData" => GaussianBinetLaplaceExponential.data
local notation "K" => GaussianBinetKernelCofinal.nameF
local notation "twelve" => num 12

def realNumerator (z : PTm n) : PTm n := numerator (fstT z)
def realDenominator (z : PTm n) : PTm n := denominatorOf (fstT z)

theorem nonnegative_real_radius (z A B : PTm n) (h : Γ ⊢[PRAAx] positive z)
    (hc : Γ ⊢[PRAAx] canonical z) (hB : Γ ⊢[PRAAx] le one B)
    (hbound : Γ ⊢[PRAAx] le (B*realNumerator z) (A*realDenominator z)) : Γ ⊢[PRAAx] bounded z A B := by
  let e := realDenominator z
  let a := realNumerator z
  let c := native (ZT.ofNat a)
  have hE : Γ ⊢[PRAAx] le one e := RationalArgmin.denominator_positive _
  have value := embed_from_representation (fstT z) (ZT.ofNat a) e (natural_representation _ h.andE₂)
  have rep := GaussianRationalHorner.represents_congr (canonical_axis_roundtrip z hc h.andE₁)
    (GaussianRootAlgebra.equal_refl c) (.eqRefl e) value
  have cnorm : Γ ⊢[PRAAx] normSq c ≐ a*a := by
    apply deriveNat
    simp only [c,native,normSq_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  exact GaussianRationalMetric.bounded_of_cleared _ _ _ _ _ hE hB rep
    (le_congr ((by ipra_ring : Γ ⊢[PRAAx] (B*a)*(B*a) ≐ (B*B)*(a*a)).eqTrans
      (congrMul (.eqRefl _) cnorm.eqSymm)) (by ipra_ring)
      (le_mul_mono hbound hbound))

/-- The cofinal kernel observation itself has norm at most (1/12+2^{-p}). -/
theorem kernel_observation_bound (p A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] bounded (ap2 K p (inputData A B)) (unit p+twelve) (twelve*unit p) := by
  let z := ap2 K p (inputData A B)
  let N := GaussianBinetKernelCofinal.cutoff p
  have hz := (GaussianBinetKernelPositive.named_finite_at (succ p) N A B A hB (unit_positive p)
    (le_congr (by ipra_ring : Γ ⊢[PRAAx] A*one ≐ A) (.eqRefl _) (le_mul_mono (le_refl A) hB))).andE₁
  have read := GaussianBinetKernelCofinal.sample_at (Γ := Γ) p A B
  have hpos := GaussianPositiveRealArithmetic.positive_congr read.eqSymm hz
  let f := GaussianBinetKernelRows.rowF
  let t := GaussianBinetKernelRows.rowBody
  let e := GaussianNamedFiniteSumFamily.sample_at (Γ := Γ) f t (succ p) N (inputData A B)
  have hc := GaussianRationalHorner.canonical_congr (read.eqTrans e)
    (GaussianRationalFiniteSum.sum_canonical (GaussianNamedFiniteSumFamily.body f t) N
      (pairT (GaussianFastValueCut.exponent N (succ p)) (inputData A B)))
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have raw := GaussianLinearDistanceName.upper_to_cleared (fstT z)
    (fstT GaussianBinetKernelZero.endpoint) (realNumerator z) (realDenominator z) one twelve one (unit p)
    (natural_representation _ hpos.andE₂) (GaussianGammaHalfSqrtBrackets.fraction_first_represents _ _ h12)
    (GaussianBinetKernelUpper.sample_upper p A B hB)
  exact nonnegative_real_radius z _ _ hpos hc (positive_product _ _ h12 (unit_positive p))
    (le_congr (by ipra_ring) (by ipra_ring) raw)

def realDecay (q a b : PTm n) : PTm n := ap2 positiveF q (positiveData (signedTime a b))

/-- An independent read of the nonnegative representative of the original
real decay at the same exponent gives the leading radius. -/
theorem exp_observation_bound (p q X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) : Γ ⊢[PRAAx]
    bounded (ap2 ExpF p (expData X Y D sign R T A B))
      (realNumerator (realDecay q (X*A) (D*B))*(unit p*unit q)+
        (num 3*unit q+unit p)*realDenominator (realDecay q (X*A) (D*B)))
      (realDenominator (realDecay q (X*A) (D*B))*(unit p*unit q)) := by
  let a := X*A
  let b := D*B
  let c := signedTime a b
  let z := realDecay q a b
  let M := realNumerator z
  let E := realDenominator z
  let U := unit p
  let V := unit q
  have hE : Γ ⊢[PRAAx] le one E := RationalArgmin.denominator_positive _
  have hU := unit_positive (Γ := Γ) p
  have hV := unit_positive (Γ := Γ) q
  have hUV := positive_product _ _ hU hV
  have hb := positive_product _ _ h.andE₁.andE₁.andE₂ h.andE₂.andE₁
  have positiveRadius := nonnegative_real_radius z M E (sample_nonnegative c q)
    (sample_canonical c q) hE (le_congr (mul_comm M E) (.eqRefl _) (le_refl (M*E)))
  have near := GaussianNameEquivalence.cross_at decayF positiveF (decayData a b) (positiveData c) p q
    (GaussianNameEquivalence.cross_symm _ _ _ _ (original_decay_nonnegative_representative a b hb))
  have realRadius := GaussianReconstructionRoots.norm_from_distance _ z _ _ M E hUV hE near positiveRadius
  have out := GaussianBinetLaplaceDecay.observation_bound p X Y D sign R T A B _ _ h
    (positive_product _ _ hUV hE) realRadius
  apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ (positive_product _ _ hUV hE) hU)
    (positive_product _ _ hE hUV) ?_ out
  exact le_of_eq_add (d := zero) (by dsimp only [M,E,U,V,a,b,z]; ipra_ring)

def complexClock (p X Y D sign R T A B : PTm n) : PTm n :=
  factorClock K p (expData X Y D sign R T A B) (inputData A B)

theorem clock_later (p X Y D sign R T A B : PTm n) :
    Γ ⊢[PRAAx] le p (complexClock p X Y D sign R T A B) := by
  unfold complexClock factorClock GaussianFastValueCut.exponent
  exact le_add_right _ _

/-- At the product's actual factor clock (j), the witnessed majorant is
((e_q+3·2^{-j}+2^{-q})(1/12+2^{-j})), where (e_q) is the displayed
sample of the original real decay at ((X A)/(D B)). -/
theorem cofinal_observation_bound (p q X Y D sign R T A B : PTm n)
    (h : Γ ⊢[PRAAx] input X Y D sign R T A B) :
    let U := unit (complexClock p X Y D sign R T A B)
    let V := unit q
    let z := realDecay q (X*A) (D*B)
    Γ ⊢[PRAAx] bounded (ap2 cofinalF p (cofinalData X Y D sign R T A B))
      ((realNumerator z*(U*V)+(num 3*V+U)*realDenominator z)*(U+twelve))
      ((realDenominator z*(U*V))*(twelve*U)) := by
  dsimp only
  let j := complexClock p X Y D sign R T A B
  let z := realDecay q (X*A) (D*B)
  have hE : Γ ⊢[PRAAx] le one (realDenominator z) := RationalArgmin.denominator_positive _
  have hU := unit_positive (Γ := Γ) j
  have hV := unit_positive (Γ := Γ) q
  have h12 : Γ ⊢[PRAAx] le one (twelve : PTm n) := by ipra_le 11
  have hb := bounded_product _ _ _ _ _ _ (positive_product _ _ hE (positive_product _ _ hU hV))
    (positive_product _ _ h12 hU) (exp_observation_bound j q X Y D sign R T A B h)
    (kernel_observation_bound j A B h.andE₂.andE₁)
  exact bound_congr (GaussianBinetLaplaceIntegrand.product_at K p _ _).eqSymm (.eqRefl _) (.eqRefl _) hb

theorem actual_Binet_Laplace_integrand_domination_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (input (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      (let U := unit (complexClock (var 0) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9))
       let V := unit (var 1)
       let z := realDecay (var 1) (var 2*var 8) (var 4*var 9)
       bounded (ap2 cofinalF (var 0) (cofinalData (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9)))
         ((realNumerator z*(U*V)+(num 3*V+U)*realDenominator z)*(U+twelve))
         ((realDenominator z*(U*V))*(twelve*U)))) :=
  closeUniv 10 (.impI (cofinal_observation_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBinetLaplaceDomination
