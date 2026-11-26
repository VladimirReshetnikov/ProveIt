import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalCofinalTaylorGridObservations
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFiniteTaylorDiskGridLimit
import IPRADerivations.Analysis.Barnes.Taylor.GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence

/-!
# Disk-uniform step threshold for the actual cofinal Barnes grid

One finite partial product serves the entire cofinal observation grid.
The disk-uniform finite step margin and coefficient cutoff control
the comparison to the original cofinal Taylor name.
-/

set_option autoImplicit false
set_option maxHeartbeats 1450000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalActualTaylorDiskGridLimit

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (bounded_mono normSq)
open GaussianBarnesCanonicalCofinalTaylorGridObservations (cofinalGrid deadline tailCutoff)
open GaussianBarnesCanonicalHigherRows (previous)
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalWeightedTaylorBallSource (stepDivisor stepDivisor_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianL1 (norm1 normSq_le_norm1_square)
open GaussianNamedInverseRate (rateNumerator rateDenominator)
open GaussianPolynomialForwardDifferenceNormalization (normalized)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (ofGaussian positive_product)
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

def precision (p : PTm n) : PTm n := exponent (num 5) p

def stepClock (p R M : PTm n) : PTm n :=
  GaussianBarnesCanonicalFiniteTaylorDiskGridLimit.stepClock (precision p) R M

def observationClock (p B M : PTm n) : PTm n := deadline (precision p) B (previous M)

def cutoff (p R B M : PTm n) : PTm n :=
  tailCutoff (observationClock p B M) R+
    GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff (precision p) (R+one) M (previous M)

def literalClock (p z h R B M : PTm n) : PTm n :=
  observationClock p B M+
    GaussianBarnesCanonicalFiniteTaylorDiskGridLimit.observationClock (precision p) z h R B (cutoff p R B M) M

def value (t z h R B M : PTm n) : PTm n :=
  normalized (cofinalGrid t z h R B (previous M)) (previous M) (ofGaussian h B)

private theorem grid_admission (p h R B M : PTm n)
    (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R M)) B) :
    Γ ⊢[PRAAx] le (previous M*norm1 h) B := by
  let e := previous M
  let k := precision p
  let A := GaussianBarnesCanonicalFiniteTaylorGridLimit.stepCostWithGain R M
    (GaussianBarnesCanonicalFiniteTaylorDiskGridLimit.analyticGain R M)
  have fit : Γ ⊢[PRAAx] le e (e*stepDivisor R) :=
    le_congr (one_mul e) (mul_comm _ _) (mul_le_mul_right e (stepDivisor_positive R))
  have hA : Γ ⊢[PRAAx] le e A := le_trans fit (le_add_right _ _)
  have pay : Γ ⊢[PRAAx] le (A*unit k) (unit (stepClock p R M)) := query_budget _ _
  have grow : Γ ⊢[PRAAx] le A (A*unit k) :=
    le_congr (one_mul A) (mul_comm _ _) (mul_le_mul_right A (unit_positive k))
  exact le_trans (le_congr (.eqRefl _) (mul_comm _ _)
    (mul_le_mul_right (norm1 h) (le_trans hA (le_trans grow pay)))) hs

theorem rate (p z h R B M t u : PTm n) (hz : Γ ⊢[PRAAx] source z R B)
    (hn : Γ ⊢[PRAAx] le one (normSq h))
    (hs : Γ ⊢[PRAAx] le (norm1 h*unit (stepClock p R M)) B)
    (ht : Γ ⊢[PRAAx] le (observationClock p B M) t) :
    Γ ⊢[PRAAx] distanceBounded (value t z h R B M) (ap2 G u (gd z (R+one) B M (previous M)))
      (unit p+unit u) (unit p*unit u) := by
  let e := previous M
  let k := precision p
  let r := cutoff p R B M
  let s := literalClock p z h R B M
  let O := observationClock p B M
  let A := tailCutoff O R
  let C := GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.cutoff k (R+one) M e
  let T := GaussianBarnesCanonicalFiniteTaylorDiskGridLimit.observationClock k z h R B r M
  let U := unit p
  let V := unit u
  let Q := unit k
  let x := value t z h R B M
  let y := GaussianBarnesCanonicalFiniteTaylorGridComparison.value s z h R B r M
  let f := ap2 F k (fd z (R+one) B r M e)
  let w := ap2 G u (gd z (R+one) B M e)
  have disk : Γ ⊢[PRAAx] source z (R+one) B :=
    .andI hz.andE₁ (bounded_mono hz.andE₂ (le_of_eq_add (d := B) (by ipra_ring)))
  have hq := unit_positive (Γ := Γ) k
  have hv := unit_positive (Γ := Γ) u
  have hd := positive_product Q V hq hv
  have sampled : Γ ⊢[PRAAx] distanceBounded x y one Q :=
    GaussianBarnesCanonicalCofinalTaylorGridObservations.scheduled_bound k t s z h R B (norm1 h) r e
      hz (normSq_le_norm1_square h) (grid_admission p h R B M hs) hn (le_add_right A C) ht (le_add_right O T)
  have first : Γ ⊢[PRAAx] distanceBounded x y V (Q*V) :=
    distance_radius_mono _ _ _ _ _ _ hq hd (le_of_eq_add (d := zero) (by ipra_ring)) sampled
  have middle : Γ ⊢[PRAAx] distanceBounded y f (two*V) (Q*V) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product Q Q hq hq) hd (le_of_eq_add (d := zero) (by ipra_ring))
      (GaussianBarnesCanonicalFiniteTaylorDiskGridLimit.rate k z h R B r M s k hz hn hs (le_add_left T O))
  have cofinal := GaussianBarnesCanonicalFixedTaylorDerivativeUniformConvergence.late_rate k z (R+one) B r M e disk
    (le_refl e) (le_add_left C A)
  have lastRaw := GaussianNamedInverseRate.rate_at G F (gd z (R+one) B M e) (fd z (R+one) B r M e) one Q u k cofinal
  have he := GaussianNamedInverseRate.denominator_positive Q u k hq
  have last : Γ ⊢[PRAAx] distanceBounded f w (two*V+Q) (Q*V) :=
    distance_radius_mono _ _ _ _ _ _ he hd
      (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,V,Q]; ipra_ring))
      (distance_symmetric _ _ _ _ he lastRaw)
  have pay : Γ ⊢[PRAAx] le (num 5*U) Q := query_budget _ _
  have radius : Γ ⊢[PRAAx] le ((V+two*V+(two*V+Q))*(U*V)) ((U+V)*(Q*V)) := by
    ipra_le 𝔞(V)*𝔞(V)*sl pay
  exact distance_radius_mono _ _ _ _ _ _ hd (positive_product _ _ (unit_positive p) hv) radius
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd first middle) last)

theorem actual_Barnes_cofinal_value_disk_normalized_grid_limit_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (let p := var 0
       let z := var 1
       let h := var 2
       let R := var 3
       let B := var 4
       let M := var 5
       let t := var 6
       let u := var 7
       (source z R B ⋏ le one (normSq h)) ⟶
         (le (norm1 h*unit (stepClock p R M)) B ⋏ le (observationClock p B M) t) ⟶
         distanceBounded (value t z h R B M) (ap2 G u (gd z (R+one) B M (previous M)))
           (unit p+unit u) (unit p*unit u)) :=
  closeUniv 8 (.impI (.impI (rate _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalActualTaylorDiskGridLimit
