import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactExhaustionScaleTransport

/-!
# Dyadic composition of the finite, image, and cofinal comparisons

The independent ordinary image observation may be taken earlier than
the inverse scale sample. Paying twice the scale bound at the earlier
clock absorbs this difference. The four source-side errors use the
same index s+2, leaving the final reference clock independent.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionComposition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerPowerScalingCell (scaleSample scaleBound)
open GaussianEulerPowerScalingParameter (scaled)
open GaussianEulerCompactExhaustionScaled (source referenceF referenceData cutoff clock)
open GaussianEulerPositivePowerChartImageCompactModulus (nameF data)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem independent_clock_budget (s p r M : PTm n) (h : Γ ⊢[PRAAx] le r p)
    (hb : Γ ⊢[PRAAx] le ((two*M)*unit s) (unit r)) :
    Γ ⊢[PRAAx] le ((M*(unit r+unit p))*unit s) (unit r*unit p) := by
  have hp := GaussianExponentialReference.unit_monotone h
  ipra_le (𝔞 M*𝔞(unit s))*sl hp+𝔞(unit p)*sl hb

theorem paid_independent_image_clock (s p r q z R B A e f d h L Q k a C E G T : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B A e f d h L Q k a C E G T)
    (hk : Γ ⊢[PRAAx] le (cutoff s z R B A e f d h L Q) k)
    (hp : Γ ⊢[PRAAx] le (clock s z R B A e f d h L Q) p)
    (hr : Γ ⊢[PRAAx] le r p)
    (hB : Γ ⊢[PRAAx] le ((two*scaleBound z B e f d h)*unit s) (unit r)) :
    Γ ⊢[PRAAx] distanceBounded
      (qmul (scaleSample p z B e f d h) (ap2 nameF r (data (scaled z f) (L*R) (B*e) a C E G T)))
      (ap2 referenceF q (referenceData z R B A e f d h L Q))
      (unit s+two*unit q) (unit s*unit q) := by
  let U := unit s
  let P := unit p
  let V := unit q
  let W := unit r
  let M := scaleBound z B e f d h
  have budget := independent_clock_budget s p r M hr hB
  have enough : Γ ⊢[PRAAx] le
      ((M*(W+P)*(U*V)+(U+V)*(W*P))*(U*V)) ((U+two*V)*((W*P)*(U*V))) := by
    ipra_le (𝔞 U*(𝔞 V)^2)*sl budget
  have hD : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ (unit_positive _) (unit_positive _)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (positive_product _ _ (unit_positive _) (unit_positive _)) hD)
    hD enough (GaussianEulerCompactExhaustionScaleTransport.original_independent_image_clock
      s p r q z R B A e f d h L Q k a C E G T hs hk hp)

theorem three_paid_comparisons (s q a b c d : PTm n)
    (h₀ : Γ ⊢[PRAAx] distanceBounded a b one (unit (s+two)))
    (h₁ : Γ ⊢[PRAAx] distanceBounded b c one (unit (s+two)))
    (h₂ : Γ ⊢[PRAAx] distanceBounded c d (unit (s+two)+two*unit q) (unit (s+two)*unit q)) :
    Γ ⊢[PRAAx] distanceBounded a d (unit s+unit q) (unit s*unit q) := by
  let U := unit (s+two)
  let V := unit q
  let P := unit s
  have hu : Γ ⊢[PRAAx] le one U := unit_positive _
  have hv : Γ ⊢[PRAAx] le one V := unit_positive _
  have huv : Γ ⊢[PRAAx] le one (U*V) := positive_product _ _ hu hv
  have first := distance_triangle_same _ b _ _ _ U hu h₀ h₁
  have refined : Γ ⊢[PRAAx] distanceBounded a c (two*V) (U*V) :=
    distance_radius_mono _ _ _ _ _ _ hu huv (le_of_eq_add (d := zero) (by ipra_ring)) first
  have next := distance_triangle_same _ c _ _ _ (U*V) huv refined h₂
  have square : Γ ⊢[PRAAx] pw two two ≐ num 4 :=
    (pw_succ two one).eqTrans ((congrMul (pw_one two) (.eqRefl _)).eqTrans (by ipra_ring))
  have price : Γ ⊢[PRAAx] U ≐ P*num 4 :=
    (pw_add two s two).eqTrans (congrMul (.eqRefl P) square)
  have exactly : Γ ⊢[PRAAx] le ((two*V+(U+two*V))*(P*V)) ((P+V)*(U*V)) := by
    apply le_of_eq_add (d := zero)
    have price' := natEq price
    apply deriveNat
    simp only [Q.mk_add,Q.mk_mul,map_add,map_mul] at price' ⊢
    ipra_simps
    linear_combination (𝔞 V)^2 * price'
  exact distance_radius_mono _ _ _ _ _ _ huv (positive_product _ _ (unit_positive _) hv) exactly next

theorem actual_dyadic_cofinal_image_composition_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((distanceBounded (var 2) (var 3) one (unit (var 0+two)) ⋏
        distanceBounded (var 3) (var 4) one (unit (var 0+two))) ⟶
      distanceBounded (var 4) (var 5) (unit (var 0+two)+two*unit (var 1)) (unit (var 0+two)*unit (var 1)) ⟶
      distanceBounded (var 2) (var 5) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 6 (.impI (.impI (three_paid_comparisons _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionComposition
