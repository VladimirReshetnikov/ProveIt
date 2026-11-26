import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteTaylorGridLimit
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence

/-!
# Cofinal Barnes forward-difference convergence

The normalized observations of the literal finite partial products
converge jointly as the step shrinks and the cutoff increases. The
tail cutoff is uniform on the disk. The step and observation clocks
are those of the finite comparison at a common stronger precision.
-/

set_option autoImplicit false
set_option maxHeartbeats 1100000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded_mono normSq)
open GaussianBarnesCanonicalFiniteTaylorGridComparison (value)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "F" => GaussianBarnesCanonicalFixedTaylorDerivativeName.nameF
local notation "fd" => GaussianBarnesCanonicalFixedTaylorDerivativeName.data
local notation "G" => GaussianBarnesCanonicalTaylorProductDerivativeName.nameF
local notation "gd" => GaussianBarnesCanonicalTaylorProductDerivativeName.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def precision (p : PTm n) : PTm n := exponent (num 4) p

def cutoff (p R M : PTm n) : PTm n :=
  GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff (precision p) (R+one) M (previous M)

def stepClock (p z R B M : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteTaylorGridLimit.stepClock (precision p) z R B M

def observationClock (p z h R B r M : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteTaylorGridLimit.observationClock (precision p) z h R B r M

theorem rate (p z h R B r M t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h)) (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p z R B M)) B)
    (hr : Γ ⊢[PRAAx] le (cutoff p R M) r) (ht : Γ ⊢[PRAAx] le (observationClock p z h R B r M) t) :
    Γ ⊢[PRAAx] distanceBounded (value t z h R B r M) (ap2 G u (gd z (R+one) B M (previous M)))
      (unit p+unit u) (unit p*unit u) := by
  let k := precision p
  let U := unit p
  let V := unit u
  let Q := unit k
  let x := value t z h R B r M
  let y := ap2 F k (fd z (R+one) B r M (previous M))
  let w := ap2 G u (gd z (R+one) B M (previous M))
  have disk : Γ ⊢[PRAAx] source z (R+one) B :=
    .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))
  have hq := unit_positive (Γ := Γ) k
  have hv := unit_positive (Γ := Γ) u
  have hd := positive_product Q V hq hv
  have first : Γ ⊢[PRAAx] distanceBounded x y (two*V) (Q*V) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product Q Q hq hq) hd (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianBarnesCanonicalFiniteTaylorGridLimit.rate k z h R B r M t k hz hn hs ht)
  have raw := GaussianNamedInverseRate.rate_at G F (gd z (R+one) B M (previous M)) (fd z (R+one) B r M (previous M))
    one Q u k (GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.late_rate k z (R+one) B r M
      (previous M) disk (le_refl _) hr)
  have he := GaussianNamedInverseRate.denominator_positive Q u k hq
  have next : Γ ⊢[PRAAx] distanceBounded y w (two*V+Q) (Q*V) :=
    distance_radius_mono _ _ _ _ _ _ he hd
      (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,V,Q]; ipra_ring))
      (distance_symmetric _ _ _ _ he raw)
  have pay : Γ ⊢[PRAAx] le (num 4*U) Q := query_budget _ _
  have fit : Γ ⊢[PRAAx] le ((two*V+(two*V+Q))*(U*V)) ((U+V)*(Q*V)) := by
    ipra_le 𝔞(V)*𝔞(V)*sl pay
  exact distance_radius_mono _ _ _ _ _ _ hd (positive_product _ _ (unit_positive p) hv) fit
    (distance_triangle_same _ _ _ _ _ _ hd first next)

theorem actual_Barnes_cofinal_normalized_grid_small_step_limit_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    (let p := var 0
     let z := var 1
     let h := var 2
     let R := var 3
     let B := var 4
     let r := var 5
     let M := var 6
     let t := var 7
     let u := var 8
     (source z R B ⋏ le one (normSq h)) ⟶
       (le (norm1 h*unit (stepClock p z R B M)) B ⋏ (le (cutoff p R M) r ⋏ le (observationClock p z h R B r M) t)) ⟶
       distanceBounded (value t z h R B r M) (ap2 G u (gd z (R+one) B M (previous M)))
         (unit p+unit u) (unit p*unit u)) :=
  closeUniv 9 (.impI (.impI (rate _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalCofinalTaylorGridLimit
