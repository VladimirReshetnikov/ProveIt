import IPRADerivations.Analysis.GaussianBarnesCanonicalCenteredExponentialShift
import IPRADerivations.Analysis.GaussianBarnesCanonicalHeadPolynomialDerivative
import IPRADerivations.Analysis.GaussianNamedMultiplyRate

/-!
# Transport an exponential increment estimate to the original Barnes value

The exact centered polynomial and the fixed exponential at the center
multiply the error for the exponential of the displacement. The
polynomial uses a bound uniform on the certified disk.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredProductRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalCenteredExponentialShift (baseData valueData head base_regular value_regular shifted_value)
open GaussianBarnesCanonicalSingleExponential (exponentF)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameBounds (U all_samples_bounded)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedDifferenceRate (self_rate rate_parameters_congr)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedMultiplyRate (sampleBound leadingNumerator leadingDenominator)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "C" => constantF
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "Y" => E exponentF
local notation "I" => E GaussianBarnesCanonicalCenteredExponentialShift.incrementF
local notation "V" => GaussianBarnesCanonicalValue.nameF
local notation "vd" => GaussianBarnesCanonicalValue.data

def nameF (g : PR 2) : PR 2 := multiplyF C (multiplyF Y g)

def data (g : PR 2) (z h R B v : PTm n) : PTm n :=
  multiplyData C (multiplyF Y g) (head z h R B) (multiplyData Y g (baseData z R B) v)

def headCap (R : PTm n) : PTm n := GaussianBarnesCanonicalHeadPolynomialDerivative.valueCap R (initial R)

def gain (z R B : PTm n) : PTm n := headCap R*U Y (baseData z R B)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (g : PR 2) (z h R B v : PTm n) :
    Syn.subst σ (data g z h R B v) =
      data g (Syn.subst σ z) (Syn.subst σ h) (Syn.subst σ R) (Syn.subst σ B) (Syn.subst σ v) := by simp [data]

@[simp] theorem subst_headCap {m : ℕ} (σ : Fin n → PTm m) (R : PTm n) :
    Syn.subst σ (headCap R) = headCap (Syn.subst σ R) := by simp [headCap]

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (z R B : PTm n) :
    Syn.subst σ (gain z R B) = gain (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B) := by simp [gain]

theorem head_bound (z h R B : PTm n) (hw : Γ ⊢[PRAAx] source (add z h) R B) :
    Γ ⊢[PRAAx] bounded (head z h R B) (headCap R) one :=
  bound_congr (GaussianBarnesCanonicalCenteredHead.original_evaluation z h B (initial R) hw.andE₁).eqSymm
    (.eqRefl _) (.eqRefl _)
    (GaussianBarnesCanonicalHeadPolynomialDerivative.value_bound (add z h) R B (initial R) hw.andE₁ hw.andE₂)

private theorem constant_bound (v M : PTm n) (h : Γ ⊢[PRAAx] bounded v M one) :
    Γ ⊢[PRAAx] sampleBound C v M := by
  refine .allI ?_
  have s : Γ.map Fm.shift ⊢[PRAAx] bounded (Syn.shift v) (Syn.shift M) one :=
    by simpa [Fm.shift,Syn.shift] using h.shift
  simpa only [sampleBound,Syn.shift] using
    bound_congr (constant_at (var 0) (Syn.shift v)).eqSymm (.eqRefl _) (.eqRefl _) s

private theorem multiply_left_rate (f g k : PR 2) (x y u M A D : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hk : Γ ⊢[PRAAx] pointCN k u)
    (hm : Γ ⊢[PRAAx] sampleBound f x M) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] independentRate g k y u A D) :
    Γ ⊢[PRAAx] independentRate (multiplyF f g) (multiplyF f k)
      (multiplyData f g x y) (multiplyData f k x u) (M*A) D := by
  have mul := GaussianNamedMultiplyRate.independent_rate f g f k x y x u zero one A D (U g y) M
    (le_refl one) hd hf hg hf hk (all_samples_bounded g y hg) hm (self_rate f x hf) hr
  exact rate_parameters_congr _ _ _ _ _ _ _ _
    (by unfold leadingNumerator; ipra_ring) (by unfold leadingDenominator; ipra_ring) mul

theorem regular (g : PR 2) (z h R B v : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hr : Γ ⊢[PRAAx] pointCN g v) :
    Γ ⊢[PRAAx] pointCN (nameF g) (data g z h R B v) :=
  multiply_fast _ _ _ _ (constant_regular _) (multiply_fast _ _ _ _ (base_regular z R B hz) hr)

theorem rate (g : PR 2) (z h R B v A D : PTm n)
    (hz : Γ ⊢[PRAAx] source z R B) (hw : Γ ⊢[PRAAx] source (add z h) R B)
    (hg : Γ ⊢[PRAAx] pointCN g v) (hd : Γ ⊢[PRAAx] le one D)
    (hr : Γ ⊢[PRAAx] independentRate I g (valueData z h R B) v A D) :
    Γ ⊢[PRAAx] independentRate V (nameF g) (vd (add z h) R B) (data g z h R B v) (gain z R B*A) D := by
  let x := baseData z R B
  let y := valueData z h R B
  let u := head z h R B
  have hx := base_regular z R B hz
  have hy := value_regular z h R B hz hw
  have hu := constant_regular (Γ := Γ) u
  have mid := multiply_left_rate Y I g x y v (U Y x) A D hx hy hg (all_samples_bounded _ _ hx) hd hr
  have outer := multiply_left_rate C (multiplyF Y I) (multiplyF Y g) u
    (multiplyData Y I x y) (multiplyData Y g x v) (headCap R) (U Y x*A) D hu
    (multiply_fast _ _ _ _ hx hy) (multiply_fast _ _ _ _ hx hg) (constant_bound u _ (head_bound z h R B hw)) hd mid
  have combined : Γ ⊢[PRAAx] independentRate (nameF I) (nameF g) (data I z h R B y)
      (data g z h R B v) (gain z R B*A) D :=
    rate_parameters_congr _ _ _ _ _ _ _ _
      (by change Γ ⊢[PRAAx] headCap R*(U Y x*A) ≐ (headCap R*U Y x)*A; ipra_ring) (.eqRefl _) outer
  exact GaussianNamedRateTransport.transport _ _ _ _ _ _ _ _ _ _ hd combined (shifted_value z h R B hz hw)
    (cross_refl _ _ (regular g z h R B v hz hg))

theorem actual_Barnes_centered_product_rate_closed (g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let z := var 0
     let h := var 1
     let R := var 2
     let B := var 3
     let v := var 4
     let A := var 5
     let D := var 6
     source z R B ⟶ source (add z h) R B ⟶ pointCN g v ⟶ le one D ⟶
       independentRate I g (valueData z h R B) v A D ⟶
       independentRate V (nameF g) (vd (add z h) R B) (data g z h R B v) (gain z R B*A) D) :=
  closeUniv 7 (.impI (.impI (.impI (.impI (.impI
    (rate g _ _ _ _ _ _ _ Prf.hyp1.wk.wk.wk Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCenteredProductRate
