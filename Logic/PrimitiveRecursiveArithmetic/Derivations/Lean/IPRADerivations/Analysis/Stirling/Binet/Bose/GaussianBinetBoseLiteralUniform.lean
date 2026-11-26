import IPRADerivations.Analysis.Stirling.Binet.Bose.GaussianBinetBoseLiteralCofinal

/-!
# A shared cutoff for the literal exponential sum away from zero

A lower bound on positive rational time fixes one truncation index
for the whole panel. The row clock pays the budget of each prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralUniform

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetBoseDenominator (reciprocalF reciprocalData reciprocal_regular)
open GaussianBinetBoseLiteralPrefix (budget value finite_error)
open GaussianBinetBoseSeries (denominatorClock partial_error)
open GaussianBinetBoseSeriesRows (rowClock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def clock (p N A B : PTm n) : PTm n := exponent (N*budget N A B) p

@[simp] theorem subst_clock {m : ℕ} (σ : Fin n → PTm m) (p N A B : PTm n) :
    Syn.subst σ (clock p N A B) = clock (Syn.subst σ p) (Syn.subst σ N) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [clock]

theorem row_clock_later (p B : PTm n) : Γ ⊢[PRAAx] le p (rowClock p B) := by
  have first : Γ ⊢[PRAAx] le (exponent (GaussianNameReciprocal.modulus B) p) (denominatorClock p B) :=
    le_add_right _ _
  exact le_trans (le_add_right p _) (le_trans first (le_add_right _ _))

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

theorem finite_uniform (p N A B K : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hK : Γ ⊢[PRAAx] le one K)
    (hM : Γ ⊢[PRAAx] le B (K*A)) (hN : Γ ⊢[PRAAx] le (K*K*unit p) N) :
    Γ ⊢[PRAAx] distanceBounded (value (clock p N A B) N A B) (ap2 reciprocalF p (reciprocalData A B))
      (num 4) (unit p) := by
  let q := clock p N A B
  let r := rowClock q B
  let C := num 4*A
  let E := B+N*C
  have hp := unit_positive (Γ := Γ) p
  have hq : Γ ⊢[PRAAx] le p q := le_add_right _ _
  have hPositive := le_trans (positive_product _ _ (positive_product _ _ hK hK) hp) hN
  have scale := le_trans (GaussianFastValueCut.query_budget (Γ := Γ) (N*budget N A B) p)
    (GaussianExponentialReference.unit_monotone (row_clock_later q B))
  have literal := distance_radius_mono _ _ _ _ one (unit p) (unit_positive r) hp
    (le_congr (.eqRefl _) (one_mul (unit r)).eqSymm scale) (finite_error q N A B hPositive hB)
  have c : Γ ⊢[PRAAx] le one C := positive_product _ _ (by ipra_le 3) hA
  have e : Γ ⊢[PRAAx] le one E := le_trans hB (le_add_right B (N*C))
  have series := distance_radius_mono _ _ _ _ one (unit p) (positive_product _ _ c e) hp
    (le_congr (.eqRefl _) (one_mul (C*E)).eqSymm (truncation_budget p N A B K hM hN))
    (partial_error q A B N hA hB)
  have later := GaussianNamedProductObservationBound.late_observation reciprocalF (reciprocalData A B) p q
    (reciprocal_regular A B hA hB) hq
  let u := value q N A B
  let v := GaussianBinetBoseSeries.prefixValue q A B N
  let w := ap2 reciprocalF q (reciprocalData A B)
  let target := ap2 reciprocalF p (reciprocalData A B)
  have first := distance_triangle_same u v w one one (unit p) hp literal series
  have both := distance_triangle_same u w target (one+one) two (unit p) hp first later
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl u) (.eqRefl target)
    (by ipra_ring : Γ ⊢[PRAAx] (one+one)+two ≐ num 4) (.eqRefl _) both

theorem actual_Bose_uniform_prefix_on_positive_margin_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (((le one (var 2) ⋏ le one (var 3)) ⋏ le one (var 4)) ⋏
      (le (var 3) (var 4*var 2) ⋏ le (var 4*var 4*unit (var 0)) (var 1)) ⟶
      distanceBounded (value (clock (var 0) (var 1) (var 2) (var 3)) (var 1) (var 2) (var 3))
        (ap2 reciprocalF (var 0) (reciprocalData (var 2) (var 3))) (num 4) (unit (var 0))) :=
  closeUniv 5 (.impI (finite_uniform _ _ _ _ _
    Prf.hyp0.andE₁.andE₁.andE₁ Prf.hyp0.andE₁.andE₁.andE₂ Prf.hyp0.andE₁.andE₂
    Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetBoseLiteralUniform
