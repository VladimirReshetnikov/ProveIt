import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalDyadicCentralBound
import IPRADerivations.Analysis.Polynomials.RootFinding.BalancedRadius.GaussianBalancedRadiusArithmetic

/-!
# A quadratic dyadic exponent for the Barnes central scalar

Bound the original prefactor radii using their two fixed named
constants. The retained correction and the cofinal logarithmic tail
then fit a quadratic expression linear in the dyadic index.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicCentralExponent

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalCenteredExponentialShift (baseData)
open GaussianBarnesCanonicalDyadicCentralBound (centralCap centralExponent central_samples)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalLogSchedule (initial)
open GaussianBarnesCanonicalSingleExponential (exponentF)
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianNameBounds (U)
open GaussianNamedMultiplyRate (sample_bound_at)
open GaussianRationalMetric (bounded)
open ConciseIPRA.PTm (succ zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "E" => GaussianRadiusExponentialName.nameF

def stirlingGain : PTm n := U GaussianStirlingConstant.nameF (GaussianStirlingConstant.nameData zero)
def eulerGain : PTm n := U GaussianGammaCanonicalExponent.gammaF zero
def growthConstant : PTm n := num 44+num 8*(stirlingGain+eulerGain)

def quadraticExponent (R j : PTm n) : PTm n :=
  (growthConstant+two*j)*((R+one)*(R+one))

def dyadicExponent (R j : PTm n) : PTm n := two*quadraticExponent R j

theorem exponent_bound (R j : PTm n) : Γ ⊢[PRAAx] le (centralExponent R j) (quadraticExponent R j) := by
  let A := (R+one)*(R+one)
  let N := initial R
  let S : PTm n := stirlingGain
  let G : PTm n := eulerGain
  let P := (two*(R*S)+two)+(two*(R+R*R*(one+G))+two)
  have h₀ : Γ ⊢[PRAAx] le one A := le_of_eq_add (d := R*R+two*R) (by dsimp only [A]; ipra_ring)
  have h₁ : Γ ⊢[PRAAx] le R A := le_of_eq_add (d := R*R+R+one) (by dsimp only [A]; ipra_ring)
  have h₂ : Γ ⊢[PRAAx] le (R*R) A := le_of_eq_add (d := two*R+one) (by dsimp only [A]; ipra_ring)
  have hN : Γ ⊢[PRAAx] le N (two*(R+one)) :=
    BarnesCutoff.maximum_least (le_of_eq_add (d := two*R+one) (by ipra_ring)) (le_of_eq_add (d := two) (by ipra_ring))
  have head : Γ ⊢[PRAAx] le (N*R) (two*A) :=
    le_trans (mul_le_mul_right R hN) (le_of_eq_add (d := two*(R+one)) (by dsimp only [A]; ipra_ring))
  change Γ ⊢[PRAAx] le (two*((P+P+(R*R*(one+j)+N*R))+(one+R*R))+two)
    ((num 44+num 8*(S+G)+two*j)*A)
  ipra_le (8*𝔞(S)+8)*sl h₁+(12+2*𝔞(j)+8*𝔞(G))*sl h₂+2*sl head+20*sl h₀ using
    dsimp only [P]
    ipra_simps
    ring

theorem cap_bound (R j : PTm n) : Γ ⊢[PRAAx] le (centralCap R j) (unit (dyadicExponent R j)) := by
  let A := quadraticExponent R j
  have order : Γ ⊢[PRAAx] le (pw (num 3) (centralExponent R j)) (pw (num 3) A) :=
    GaussianFactorBudget.power_monotone_length (num 3) _ _ (zero_lt_succ _) (exponent_bound R j)
  have bases : Γ ⊢[PRAAx] le (num 3) (two*two) := le_of_eq_add (d := one) (by ipra_ring)
  exact le_trans order (le_congr (.eqRefl _) (GaussianBalancedRadiusArithmetic.unit_four_power A).eqSymm (pw_le_pw A bases))

def dyadicGrowthConstant : PTm n := num 8*(growthConstant+two)

theorem dyadic_unit_cap_bound (j : PTm n) : Γ ⊢[PRAAx]
    le (centralCap (unit j) (succ j)) (unit (dyadicGrowthConstant*succ j*(unit j*unit j))) := by
  let R := unit j
  let k := succ j
  let C : PTm n := growthConstant
  have hR : Γ ⊢[PRAAx] le (R+one) (R+R) := Common.add_le_add (le_refl R) (unit_positive j)
  have square : Γ ⊢[PRAAx] le ((R+one)*(R+one)) (num 4*(R*R)) :=
    le_congr (.eqRefl _) (by ipra_ring) (Common.mul_le_mul hR hR)
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have cost : Γ ⊢[PRAAx] le (C+two*k) ((C+two)*k) := by ipra_le 𝔞(C)*sl hk
  have budget : Γ ⊢[PRAAx] le (dyadicExponent R k) (dyadicGrowthConstant*k*(R*R)) :=
    le_congr (.eqRefl _) (by dsimp only [dyadicGrowthConstant,C]; ipra_ring)
      (Common.mul_le_mul (le_refl two) (Common.mul_le_mul cost square))
  exact le_trans (cap_bound R k) (GaussianExponentialReference.unit_monotone budget)

theorem observation (p z R B j : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hj : Γ ⊢[PRAAx] le (initial R) (pw two j)) :
    Γ ⊢[PRAAx] bounded (ap2 (E exponentF) p (baseData z R B)) (unit (dyadicExponent R j)) one :=
  bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one) (mul_le_mul_right one (cap_bound R j))
    (sample_bound_at _ _ _ p (central_samples z R B j hz hj))

theorem actual_Barnes_central_scalar_quadratic_dyadic_growth_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let p := var 0
       let z := var 1
       let R := var 2
       let B := var 3
       let j := var 4
       (source z R B ⋏ le (initial R) (pw two j)) ⟶
         bounded (ap2 (E exponentF) p (baseData z R B)) (unit (dyadicExponent R j)) one) :=
  closeUniv 5 (.impI (observation _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDyadicCentralExponent
