import IPRADerivations.Analysis.Beta.CompactKernels.GaussianBetaKernelCompactUpperTail
import IPRADerivations.Analysis.Beta.EulerProducts.GaussianBetaFiniteEulerComparison

/-!
# A dyadic upper beta tail on the shared-step grid

The finite upper tail uses mesh count (CS) for width (C/E),
so its physical mesh step is (1/(ES)). The existing half-decay
bound gives a degree-independent cutoff term and computable lower
bounds on the common mesh multiplier and observation precision.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBetaUpperTailDyadic

open_ipra
open GaussianRationalMetric (bounded)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianGammaIntegralCutoffs (top height tailCoefficient)
open GaussianEulerWeightedHalfDecay (majorant)
open GaussianBetaKernelUpperTail (referenceBudget)
open GaussianBetaKernelGridComparison (evaluatorF sampleDataBeta)
open GaussianEulerHalfDecayTailBound (tailNumerator tailDenominator)
open GaussianCompactRiemannName (quadrature)
open GaussianBetaFiniteEulerComparison (slack)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def observation (p k A R C E z B N S : PTm n) : PTm n :=
  quadrature evaluatorF p (C*S) (top k A R*E) C E (sampleDataBeta z B N)
def meshCost (R N : PTm n) : PTm n := two*majorant R*N
def precisionCost (R N : PTm n) : PTm n := (referenceBudget R+majorant R)*N+num 20*majorant R
def cutoffCost (R : PTm n) : PTm n := two*majorant R
def counterDenominator (p k A R S : PTm n) : PTm n := S*unit p*unit (height k A R)
def counterNumerator (p k A R N S : PTm n) : PTm n :=
  meshCost R N*unit p*unit (height k A R)+precisionCost R N*S*unit (height k A R)+cutoffCost R*S*unit p
def minimumMesh (t R N : PTm n) : PTm n := meshCost R N*unit (slack t)+one
def minimumPrecision (t R N : PTm n) : PTm n := GaussianFastValueCut.exponent (precisionCost R N) (slack t)
def source (z R B k A C E N S : PTm n) : Fm PTm n :=
  GaussianEulerUpperPowerCoefficients.source z R B ⋏
    (le one N ⋏ le one C ⋏ le one E ⋏ le one S ⋏ le (top k A R*E+C) (E*N))

theorem coarse_upper_bound (p k A R C E z B N S : PTm n)
    (h : Γ ⊢[PRAAx] source z R B k A C E N S) : Γ ⊢[PRAAx]
    bounded (observation p k A R C E z B N S)
      (counterNumerator p k A R N S) (counterDenominator p k A R S) := by
  let L := height k A R
  let H := unit L
  let U := unit p
  let M := C*S
  let V := counterDenominator p k A R S
  let J := tailDenominator p p M L E
  let D := (E*U)*J
  let B0 := C*referenceBudget R*J+(majorant R*tailNumerator p p M L C E)*(E*U)
  let K := majorant R
  let Q := referenceBudget R
  have hn := h.andE₂.andE₁
  have hc := h.andE₂.andE₂.andE₁
  have he := h.andE₂.andE₂.andE₂.andE₁
  have hs := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hRight := h.andE₂.andE₂.andE₂.andE₂.andE₂
  have hm : Γ ⊢[PRAAx] le one M := positive_product _ _ hc hs
  have hu : Γ ⊢[PRAAx] le one U := unit_positive p
  have hh : Γ ⊢[PRAAx] le one H := unit_positive L
  have htwo : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have d : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (positive_product _ _ he hu)
      (positive_product _ _ (positive_product _ _ (positive_product _ _ (positive_product _ _
        (positive_product _ _ (positive_product _ _ htwo he) he) hm) hu) hu) hh)
  have v : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ hs hu) hh
  have mul := positive_product (two*E) S (positive_product _ _ htwo he) hs
  have step : Γ ⊢[PRAAx] le C ((two*E)*M) :=
    le_congr (one_mul C) (by dsimp only [M]; ipra_ring) (mul_le_mul_right C mul)
  have hcn : Γ ⊢[PRAAx] le C (E*N) := le_trans (le_add_left C (top k A R*E)) hRight
  have orderE : Γ ⊢[PRAAx] le E (E*E) := le_congr (one_mul E) (.eqRefl _) (mul_le_mul_right E he)
  have hcn2 : Γ ⊢[PRAAx] le C (E*E*N) := le_trans hcn (mul_le_mul_right N orderE)
  have raw := GaussianBetaKernelCompactUpperTail.original_upper_cutoff_bound p p M k A C E z R B N
    hm hc he step h.andE₁ hn hRight
  have compare : Γ ⊢[PRAAx] le (B0*V) (counterNumerator p k A R N S*D) := by
    change Γ ⊢[PRAAx] le
      ((C*Q*(two*E*E*(C*S)*U*U*H)+K*
        ((two+one)*C*C*U*U*H+two*C*E*(C*S)*U*H+num 40*E*E*(C*S)*U*H+num 4*E*E*(C*S)*U*U)*(E*U))*(S*U*H))
      ((two*K*N*U*H+((Q+K)*N+num 20*K)*S*H+two*K*S*U)*((E*U)*(two*E*E*(C*S)*U*U*H)))
    ipra_le
      (3*𝔞 E*𝔞 C*𝔞 U*𝔞 U*𝔞 K*𝔞 U*𝔞 H*𝔞 S*𝔞 U*𝔞 H)*sl hcn2+
      (2*𝔞 E*𝔞 C*𝔞 U*𝔞 U*𝔞 E*𝔞 S*𝔞 H*(𝔞 Q+𝔞 K)*𝔞 S*𝔞 U*𝔞 H)*sl hcn+
      (𝔞 E*𝔞 C*𝔞 U*𝔞 U*𝔞 E*𝔞 E*𝔞 N*𝔞 K*𝔞 U*𝔞 H*𝔞 S*𝔞 U*𝔞 H)
  exact bounded_radius_mono _ _ _ _ _ d v compare raw

theorem cutoff_budget (t k A R : PTm n) (hk : Γ ⊢[PRAAx] le t k) : Γ ⊢[PRAAx]
    le (cutoffCost R*unit (slack t)) (unit (height k A R)) := by
  have step : Γ ⊢[PRAAx] le (slack t) (k+num 6) :=
    le_trans (le_congr (by unfold slack; ipra_ring) (.eqRefl _) (add_le_add_right (num 2) hk))
      (le_of_eq_add (d := num 4) (by ipra_ring))
  have cost : Γ ⊢[PRAAx] cutoffCost R ≐ tailCoefficient R := by
    unfold cutoffCost majorant tailCoefficient
    exact (show Γ ⊢[PRAAx] two*(unit R*Products.fact R) ≐ (unit R*two)*Products.fact R from by ipra_ring).eqTrans
      (congrMul (pw_succ two R).eqSymm (.eqRefl _))
  have ordered : Γ ⊢[PRAAx] le (cutoffCost R) (A+tailCoefficient R) :=
    le_congr cost.eqSymm (.eqRefl _) (le_add_left (tailCoefficient R) A)
  exact le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono ordered
    (GaussianExponentialReference.unit_monotone step))
    (le_of_lt (GaussianGammaIntegralCutoffs.omitted_tail_budget k A R))

theorem dyadic_upper_bound (t p k A R C E z B N S : PTm n)
    (h : Γ ⊢[PRAAx] source z R B k A C E N S)
    (hk : Γ ⊢[PRAAx] le t k) (hm : Γ ⊢[PRAAx] le (minimumMesh t R N) S)
    (hp : Γ ⊢[PRAAx] le (minimumPrecision t R N) p) : Γ ⊢[PRAAx]
    bounded (observation p k A R C E z B N S) one (unit t) := by
  let U := unit p
  let H := unit (height k A R)
  let W := unit (slack t)
  let D := counterDenominator p k A R S
  let Z := counterNumerator p k A R N S
  have d : Γ ⊢[PRAAx] le one D :=
    positive_product _ _ (positive_product _ _ h.andE₂.andE₂.andE₂.andE₂.andE₁ (unit_positive p)) (unit_positive _)
  have hMesh : Γ ⊢[PRAAx] le (meshCost R N*W) S := le_trans (le_add_right _ _) hm
  have hPrec : Γ ⊢[PRAAx] le (precisionCost R N*W) U :=
    le_trans (GaussianFastValueCut.query_budget _ _) (GaussianExponentialReference.unit_monotone hp)
  have hCut := cutoff_budget t k A R hk
  have sum : Γ ⊢[PRAAx] le (Z*W) ((num 3)*D) :=
    le_congr (by dsimp only [Z,counterNumerator]; ipra_ring) (by dsimp only [D,counterDenominator]; ipra_ring)
      (add_le_add₂ (add_le_add₂ (mul_le_mul_right (U*H) hMesh) (mul_le_mul_right (S*H) hPrec))
        (mul_le_mul_right (S*U) hCut))
  have intermediate := bounded_radius_mono _ _ _ _ _ d (unit_positive (slack t)) sum
    (coarse_upper_bound p k A R C E z B N S h)
  have four : Γ ⊢[PRAAx] W ≐ num 4*unit t := by
    change Γ ⊢[PRAAx] pw two (succ (succ t)) ≐ num 4*pw two t
    exact (pw_succ two (succ t)).eqTrans ((congrMul (pw_succ two t) (.eqRefl _)).eqTrans (by ipra_ring))
  have cmp : Γ ⊢[PRAAx] le (num 3*unit t) (one*W) :=
    le_congr (.eqRefl _) (congrMul (.eqRefl _) four).eqSymm (le_of_eq_add (d := unit t) (by ipra_ring))
  exact bounded_radius_mono _ _ _ _ _ (unit_positive (slack t)) (unit_positive t) cmp intermediate

theorem original_beta_upper_tail_dyadic_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((source (var 7) (var 4) (var 8) (var 2) (var 3) (var 5) (var 6) (var 9) (var 10) ⋏
      le (var 0) (var 2) ⋏ le (minimumMesh (var 0) (var 4) (var 9)) (var 10) ⋏
      le (minimumPrecision (var 0) (var 4) (var 9)) (var 1)) ⟶
      bounded (observation (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10))
        one (unit (var 0))) :=
  closeUniv 11 (.impI (dyadic_upper_bound _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBetaUpperTailDyadic
