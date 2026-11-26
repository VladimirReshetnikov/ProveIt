import IPRADerivations.Analysis.GaussianBoundedConstantProductRate

/-!
# A fractional leading bound for the actual constant product

A rational bound (A/E) on the multiplier scales the leading input
error by exactly (A/E). The original clock for the integral cap (A)
still pays for each observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRationalConstantProductRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBoundedConstantProductName (nameF data sample_at clock)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

theorem integral_bound (c A E : PTm n) (hE : Γ ⊢[PRAAx] le one E) (hc : Γ ⊢[PRAAx] bounded c A E) :
    Γ ⊢[PRAAx] bounded c A one :=
  bounded_radius_mono _ _ _ _ _ hE (le_refl one)
    (le_congr (mul_comm one A) (mul_comm E A) (mul_le_mul_right A hE)) hc

theorem observations (f g : PR 2) (p q A E c x y X D : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D) (hc : Γ ⊢[PRAAx] bounded c A E)
    (hr : Γ ⊢[PRAAx] independentRate f g x y X D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data A c x)) (ap2 (nameF g) q (data A c y))
      (rateNumerator (A*X) (E*D) p q) (rateDenominator (E*D) p q) := by
  let s := clock p A
  let t := clock q A
  let K := rateDenominator D s t
  have hK := denominator_positive D s t hD
  have new := denominator_positive (E*D) p q (positive_product _ _ hE hD)
  have raw := GaussianNamedInverseRate.rate_at f g x y X D s t hr
  have scaled : Γ ⊢[PRAAx] distanceBounded (qmul c (ap2 f s x)) (qmul c (ap2 g t y))
      (A*rateNumerator X D s t) (E*K) :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference c _ _).eqSymm
      (.eqRefl _) (.eqRefl _) (GaussianRationalReciprocal.bounded_product c _ A E _ _ hE hK hc raw)
  have bP : Γ ⊢[PRAAx] le (A*unit p) (E*unit s) :=
    le_trans (GaussianFastValueCut.query_budget A p)
      (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit s) hE))
  have bQ : Γ ⊢[PRAAx] le (A*unit q) (E*unit t) :=
    le_trans (GaussianFastValueCut.query_budget A q)
      (le_congr (one_mul _) (.eqRefl _) (mul_le_mul_right (unit t) hE))
  have narrow : Γ ⊢[PRAAx] distanceBounded (qmul c (ap2 f s x)) (qmul c (ap2 g t y))
      (rateNumerator (A*X) (E*D) p q) (rateDenominator (E*D) p q) :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hE hK) new
    (by
      dsimp only [rateNumerator,rateDenominator,K]
      ipra_le 𝔞(E)*𝔞(D)*𝔞(D)*𝔞(unit q)*𝔞(unit t)*sl bP+
        𝔞(E)*𝔞(D)*𝔞(D)*𝔞(unit p)*𝔞(unit s)*sl bQ) scaled
  exact distance_congr (sample_at f p A c x).eqSymm (sample_at g q A c y).eqSymm (.eqRefl _) (.eqRefl _) narrow

theorem rate (f g : PR 2) (A E c x y X D : PTm n)
    (hE : Γ ⊢[PRAAx] le one E) (hD : Γ ⊢[PRAAx] le one D) (hc : Γ ⊢[PRAAx] bounded c A E)
    (hr : Γ ⊢[PRAAx] independentRate f g x y X D) : Γ ⊢[PRAAx]
    independentRate (nameF f) (nameF g) (data A c x) (data A c y) (A*X) (E*D) := by
  let s (x : PTm n) := Syn.shift (Syn.shift x)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have he : Δ ⊢[PRAAx] le one (s E) := by simpa [Fm.shift,Syn.shift,s,Δ] using hE.shift.shift
  have hd : Δ ⊢[PRAAx] le one (s D) := by simpa [Fm.shift,Syn.shift,s,Δ] using hD.shift.shift
  have hb : Δ ⊢[PRAAx] bounded (s c) (s A) (s E) := by simpa [Fm.shift,Syn.shift,s,Δ] using hc.shift.shift
  have hx : Δ ⊢[PRAAx] independentRate f g (s x) (s y) (s X) (s D) := by simpa [Fm.shift,Syn.shift,s,Δ] using hr.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift,s,Δ,GaussianBoundedConstantProductName.subst_data,PTm.subst_mul] using
    observations f g (var 1) (var 0) (s A) (s E) (s c) (s x) (s y) (s X) (s D) he hd hb hx

theorem actual_rational_multiplier_named_rate_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (let A := var 0
     let E := var 1
     let c := var 2
     let x := var 3
     let y := var 4
     let X := var 5
     let D := var 6
     (le one E ⋏ (le one D ⋏ bounded c A E)) ⟶ independentRate f g x y X D ⟶
       independentRate (nameF f) (nameF g) (data A c x) (data A c y) (A*X) (E*D)) :=
  closeUniv 7 (.impI (.impI (rate f g _ _ _ _ _ _ _
      Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianRationalConstantProductRate
