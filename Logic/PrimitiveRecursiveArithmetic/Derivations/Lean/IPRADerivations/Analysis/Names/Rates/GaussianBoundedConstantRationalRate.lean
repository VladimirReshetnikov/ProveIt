import IPRADerivations.Analysis.Names.Rates.GaussianBoundedConstantProductRate

/-!
# Rational rates for the actual bounded constant-product program

An integer ceiling controls the original multiplication clock.
The sharper rational norm bound multiplies the leading distance,
and each scheduled observation still pays only its own dyadic error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBoundedConstantRationalRate

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianBoundedConstantProductName (nameF data sample_at clock)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator shift_independent_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalRoundedPower (multiplication_difference)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem clock_budget (p A P Qd : PTm n) (hClock : Γ ⊢[PRAAx] le P (A*Qd)) :
    Γ ⊢[PRAAx] le (P*unit p) (Qd*unit (clock p A)) :=
  le_trans (mul_le_mul_right (unit p) hClock)
    (le_congr (by ipra_ring) (.eqRefl _)
      (le_mul_mono (le_refl Qd) (GaussianFastValueCut.query_budget A p)))

theorem original_observations (f g : PR 2) (p q A c x y P Qd B D : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Qd) (hD : Γ ⊢[PRAAx] le one D)
    (hClock : Γ ⊢[PRAAx] le P (A*Qd)) (hc : Γ ⊢[PRAAx] bounded c P Qd)
    (hr : Γ ⊢[PRAAx] independentRate f g x y B D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data A c x)) (ap2 (nameF g) q (data A c y))
      (rateNumerator (P*B) (Qd*D) p q) (rateDenominator (Qd*D) p q) := by
  let s := clock p A
  let t := clock q A
  have hInput : Γ ⊢[PRAAx] le one (rateDenominator D s t) :=
    positive_product _ _ (positive_product _ _ hD (unit_positive s)) (unit_positive t)
  have hOld := positive_product Qd (rateDenominator D s t) hQ hInput
  have hNew : Γ ⊢[PRAAx] le one (rateDenominator (Qd*D) p q) :=
    positive_product _ _ (positive_product _ _ (positive_product _ _ hQ hD) (unit_positive p)) (unit_positive q)
  have raw := GaussianNamedInverseRate.rate_at f g x y B D s t hr
  have product : Γ ⊢[PRAAx] distanceBounded (qmul c (ap2 f s x)) (qmul c (ap2 g t y))
      (P*rateNumerator B D s t) (Qd*rateDenominator D s t) :=
    bound_congr (multiplication_difference c _ _).eqSymm (.eqRefl _) (.eqRefl _)
      (bounded_product c _ P Qd _ _ hQ hInput hc raw)
  have bP := clock_budget p A P Qd hClock
  have bQ := clock_budget q A P Qd hClock
  have widened := distance_radius_mono _ _ _ _ (rateNumerator (P*B) (Qd*D) p q) (rateDenominator (Qd*D) p q)
    hOld hNew (by
    unfold rateNumerator rateDenominator
    dsimp only [s, t]
    ipra_le (𝔞 Qd*𝔞 D*𝔞 D*𝔞 (unit q)*𝔞 (unit (clock q A)))*sl bP +
      (𝔞 Qd*𝔞 D*𝔞 D*𝔞 (unit p)*𝔞 (unit (clock p A)))*sl bQ) product
  exact distance_congr (sample_at f p A c x).eqSymm (sample_at g q A c y).eqSymm
    (.eqRefl _) (.eqRefl _) widened

theorem original_rate (f g : PR 2) (A c x y P Qd B D : PTm n)
    (hQ : Γ ⊢[PRAAx] le one Qd) (hD : Γ ⊢[PRAAx] le one D)
    (hClock : Γ ⊢[PRAAx] le P (A*Qd)) (hc : Γ ⊢[PRAAx] bounded c P Qd)
    (hr : Γ ⊢[PRAAx] independentRate f g x y B D) : Γ ⊢[PRAAx]
    independentRate (nameF f) (nameF g) (data A c x) (data A c y) (P*B) (Qd*D) := by
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  have hq := Order.shift_one_le (Order.shift_one_le hQ)
  have hd := Order.shift_one_le (Order.shift_one_le hD)
  have ha : Δ ⊢[PRAAx] le (sh P) (sh A * sh Qd) := by
    simpa [Δ, Fm.shift, Syn.shift, sh] using hClock.shift.shift
  have hb : Δ ⊢[PRAAx] bounded (sh c) (sh P) (sh Qd) := by
    simpa [Δ, Fm.shift, Syn.shift, sh] using hc.shift.shift
  have hh := shift_independent_rate (shift_independent_rate hr)
  refine .allI (.allI ?_)
  simpa only [Δ, independentRate, GaussianBoundedConstantProductName.subst_data, PTm.subst_mul, Syn.shift, sh] using
    original_observations f g (var 1) (var 0) (sh A) (sh c) (sh x) (sh y) (sh P) (sh Qd) (sh B) (sh D)
      hq hd ha hb hh

theorem actual_bounded_constant_rational_product_rate_closed (f g : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((le one (var 5) ⋏ (le one (var 7) ⋏ (le (var 4) (var 0 * var 5) ⋏
        (bounded (var 1) (var 4) (var 5) ⋏ independentRate f g (var 2) (var 3) (var 6) (var 7))))) ⟶
        independentRate (nameF f) (nameF g) (data (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 3))
          (var 4 * var 6) (var 5 * var 7)) :=
  closeUniv 8 (.impI (original_rate f g _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBoundedConstantRationalRate
