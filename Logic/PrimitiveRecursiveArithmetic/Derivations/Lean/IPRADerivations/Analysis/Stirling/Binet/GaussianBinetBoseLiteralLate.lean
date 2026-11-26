import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetBoseLiteralUniform

/-!
# Literal Bose observations at an independent later clock

Choose the geometric cutoff at the requested comparison precision.
The existing literal prefix can then be evaluated at any later
observation, keeping the same actual exponential row clock schedule.
-/

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralLate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseDenominator (reciprocalF reciprocalData reciprocal_regular)
open GaussianBinetBoseLiteralPrefix (budget value finite_error)
open GaussianBinetBoseLiteralUniform (clock row_clock_later)
open GaussianBinetBoseSeries (partial_error prefixValue)
open GaussianBinetBoseSeriesRows (rowClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem truncation_budget (p N A B K : PTm n) (hM : Γ ⊢[PRAAx] le B (K*A))
    (hN : Γ ⊢[PRAAx] le (K*K*unit p) N) :
    Γ ⊢[PRAAx] le ((B*B)*unit p) ((num 4*A)*(B+N*(num 4*A))) := by
  let C := num 4*A
  have ac : Γ ⊢[PRAAx] le A C :=
    le_of_eq_add (d := num 3*A) (by dsimp only [C]; ipra_ring)
  have c := mul_le_mul_right N (sq_le_sq ac)
  have first := mul_le_mul_right (unit p) (sq_le_sq hM)
  have middle := mul_le_mul_right (A*A) hN
  have second : Γ ⊢[PRAAx] le ((K*A)*(K*A)*unit p) (A*A*N) :=
    le_congr (by ipra_ring) (mul_comm N (A*A)) middle
  have last : Γ ⊢[PRAAx] le (C*C*N) (C*(B+N*C)) :=
    le_of_eq_add (d := C*B) (by ipra_ring)
  exact le_trans first (le_trans second (le_trans c last))

theorem finite_uniform_late (s p N A B K : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K)
    (hM : Γ ⊢[PRAAx] le B (K*A)) (hs : Γ ⊢[PRAAx] le s p) (hN : Γ ⊢[PRAAx] le (K*K*unit s) N) :
    Γ ⊢[PRAAx] distanceBounded (value (clock p N A B) N A B) (ap2 reciprocalF p (reciprocalData A B))
      (num 4) (unit s) := by
  let q := clock p N A B
  let r := rowClock q B
  let C := num 4*A
  let E := B+N*C
  let w := value q N A B
  let x := prefixValue q A B N
  let y := ap2 reciprocalF q (reciprocalData A B)
  let z := ap2 reciprocalF p (reciprocalData A B)
  have hp := unit_positive (Γ := Γ) p
  have hs' := unit_positive (Γ := Γ) s
  have hq : Γ ⊢[PRAAx] le p q := le_add_right _ _
  have hPositive := le_trans (positive_product _ _ (positive_product _ _ hK hK) hs') hN
  have scale := le_trans (GaussianFastValueCut.query_budget (Γ := Γ) (N*budget N A B) p)
    (GaussianExponentialReference.unit_monotone (row_clock_later q B))
  have rounded : Γ ⊢[PRAAx] distanceBounded w x one (unit p) :=
    distance_radius_mono _ _ _ _ one (unit p) (unit_positive r) hp
      (le_congr (.eqRefl _) (one_mul (unit r)).eqSymm scale) (finite_error q N A B hPositive hB)
  have literal := GaussianExponentialReference.dyadic_weaken w x one s p hs rounded
  have c : Γ ⊢[PRAAx] le one C := positive_product _ _ (by ipra_le 3) hA
  have e : Γ ⊢[PRAAx] le one E := le_trans hB (le_add_right B (N*C))
  have series : Γ ⊢[PRAAx] distanceBounded x y one (unit s) :=
    distance_radius_mono _ _ _ _ one (unit s) (positive_product _ _ c e) hs'
      (le_congr (.eqRefl _) (one_mul (C*E)).eqSymm (truncation_budget s N A B K hM hN))
      (partial_error q A B N hA hB)
  have later := GaussianNamedProductObservationBound.late_observation reciprocalF (reciprocalData A B) p q
    (reciprocal_regular A B hA hB) hq
  have observed := GaussianExponentialReference.dyadic_weaken y z two s p hs later
  have first := distance_triangle_same w x y one one (unit s) hs' literal series
  exact distance_congr (.eqRefl w) (.eqRefl z) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same w y z (one+one) two (unit s) hs' first observed)

end LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralLate
