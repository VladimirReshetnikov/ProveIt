import IPRADerivations.Analysis.GaussianGammaCanonicalExponent
import IPRADerivations.Analysis.GaussianNamedInverseRate

/-!
# Observations of the two regularized pole products

The original constant-times-name product observes its arguments at its
actual precision clock. If the name is within the independent rate
`C/E` of one and the constant is within `I/D` of the target, a product
observation has error `M*C/E + I/D + 2*M/2^p` when the constant
has bound `M`. Canonical recoding adds no error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaPoleProductRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at multiplyRaw recode_congr)
open GaussianFastValueCut (exponent recode exponent_unit recode_distance)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate diagonal_rate)
open GaussianNameRingLaws (oneF one_at)
open GaussianRationalHorner (qmul canonical positive_product)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def numerator (M C E I D p : PTm n) : PTm n :=
  (M*C*D+I*E)*unit p+two*M*(E*D)
def denominator (E D p : PTm n) : PTm n := E*D*unit p

private theorem observation_clock (F : PR 2) (c x p : PTm n) : Γ ⊢[PRAAx]
    le (unit p) (unit (exponent (multiplyModulus constantF F c x) p)) := by
  let L := multiplyModulus constantF F c x
  exact le_congr (by ipra_ring) (exponent_unit L p).eqSymm
    (le_mul_mono (le_refl (unit p)) (unit_positive (GaussianFastValueCut.normalizer L)))

theorem actual_pole_product_observation (F : PR 2) (c c₀ x M C E I D p : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D)
    (hc : Γ ⊢[PRAAx] canonical c) (hM : Γ ⊢[PRAAx] bounded c M one)
    (hC : Γ ⊢[PRAAx] independentRate F oneF x zero C E)
    (hI : Γ ⊢[PRAAx] distanceBounded c c₀ I D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (multiplyF constantF F) p (multiplyData constantF F c x)) c₀
      (numerator M C E I D p) (denominator E D p) := by
  let k := exponent (multiplyModulus constantF F c x) p
  let y := qmul c (ap2 F k x)
  let d := denominator E D p
  have hk := unit_positive (Γ := Γ) k
  have hp := unit_positive (Γ := Γ) p
  have hd : Γ ⊢[PRAAx] le one d := positive_product _ _ (positive_product _ _ hE hD) hp
  have hEk := positive_product _ _ hE hk
  have raw := diagonal_rate F oneF x zero C E k hE hC
  have d₁ : Γ ⊢[PRAAx] distanceBounded (ap2 F k x) qone (C*unit k+two*E) (E*unit k) :=
    distance_congr (.eqRefl _) (one_at k zero) (.eqRefl _) (.eqRefl _) raw
  have d₂ : Γ ⊢[PRAAx] distanceBounded y c (M*(C*unit k+two*E)) (E*unit k) :=
    distance_congr (.eqRefl _) (GaussianReciprocalHorner.qmul_one_right c hc) (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance c (ap2 F k x) qone M _ _ hEk hM d₁)
  have monotone := observation_clock (Γ := Γ) F c x p
  have aligned : Γ ⊢[PRAAx] distanceBounded y c ((M*C*unit p+two*M*E)*D) d := by
    apply distance_radius_mono _ _ _ _ _ _ hEk hd _ d₂
    dsimp only [d, denominator]
    ipra_le 2*𝔞 M*𝔞 E*𝔞 E*𝔞 D*sl monotone
  have finite : Γ ⊢[PRAAx] distanceBounded c c₀ (I*E*unit p) d :=
    distance_radius_mono _ _ _ _ _ _ hD hd
      (le_of_eq_add (d := zero) (by dsimp only [d, denominator]; ipra_ring)) hI
  have first : Γ ⊢[PRAAx] distanceBounded (recode y) y zero d :=
    distance_radius_mono _ _ _ _ _ _ (le_refl one) hd
      (le_of_eq_add (d := zero) (by ipra_ring)) (recode_distance y)
  have program : Γ ⊢[PRAAx] ap2 (multiplyF constantF F) p (multiplyData constantF F c x) ≐ recode y :=
    (multiply_at constantF F c x p).eqTrans (recode_congr (qmul_congr (constant_at k c) (.eqRefl _)))
  exact distance_congr program.eqSymm (.eqRefl _) (by unfold numerator; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hd (distance_triangle_same _ _ _ _ _ _ hd first aligned) finite)

theorem original_pole_product_observation_closed (F : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((le one (var 5) ⋏ le one (var 7)) ⟶
      (canonical (var 0) ⋏ bounded (var 0) (var 3) one) ⟶
      independentRate F oneF (var 2) zero (var 4) (var 5) ⟶
      distanceBounded (var 0) (var 1) (var 6) (var 7) ⟶
      distanceBounded (ap2 (multiplyF constantF F) (var 8) (multiplyData constantF F (var 0) (var 2)))
        (var 1) (numerator (var 3) (var 4) (var 5) (var 6) (var 7) (var 8))
        (denominator (var 5) (var 7) (var 8))) :=
  closeUniv 9 (.impI (.impI (.impI (.impI (actual_pole_product_observation F _ _ _ _ _ _ _ _ _
    hyp2.wk.andE₁ hyp2.wk.andE₂ hyp2.andE₁ hyp2.andE₂ Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.GaussianGammaPoleProductRate
