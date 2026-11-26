import IPRADerivations.Analysis.Logarithm.PositiveAxis.GaussianNamedPositiveLogarithm

/-!
# Quantitative transport through the original named positive logarithm

Two named inputs with the same positive lower margin carry a
quantitative distance into their actual named logarithms. The
margin multiplies the rational part of the bound. The original
logarithm clocks pay for the input observation errors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithmRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedPositiveLogarithm (source nameF data clock rationalData sample_at decoded_domain decoded_value)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open ConciseIPRA.PTm (succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem double_unit (p : PTm n) : Γ ⊢[PRAAx] unit (succ p) ≐ two*unit p :=
  (pw_succ two p).eqTrans (mul_comm _ _)

private theorem clock_budget (p E : PTm n) : Γ ⊢[PRAAx] le (two*E*unit p) (unit (clock p E)) :=
  le_congr ((congrMul (.eqRefl E) (double_unit p)).eqTrans (by ipra_ring)) (.eqRefl _)
    (GaussianFastValueCut.query_budget E (succ p))

theorem log_rate_at (f g : PR 2) (p q x y E T U A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E T) (hg : Γ ⊢[PRAAx] source g y E U)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] independentRate f g x y A D) :
    Γ ⊢[PRAAx] distanceBounded (ap2 (nameF f) p (data x E)) (ap2 (nameF g) q (data y E))
      (rateNumerator (E*A) D p q) (rateDenominator D p q) := by
  let r := clock p E
  let s := clock q E
  let B := rateNumerator A D r s
  let C := rateDenominator D r s
  have hC : Γ ⊢[PRAAx] le one C := denominator_positive D r s hD
  have hx := decoded_domain f r x E T hf
  have hy := decoded_domain g s y E U hg
  have inBound := distance_congr (decoded_value f r x E T hf).eqSymm (decoded_value g s y E U hg).eqSymm
    (.eqRefl _) (.eqRefl _) (rate_at f g x y A D r s h)
  have out := GaussianCompactLogarithmBounds.original_log_rate _ _ _ _ E B C hx.andE₁ hy.andE₁ hC
    hx.andE₂.andE₁ hy.andE₂.andE₁ inBound
  have raw := rate_at logF logF (rationalData f r x) (rationalData g s y) (E*B) C (succ p) (succ q) out
  have up := double_unit (Γ := Γ) p
  have uq := double_unit (Γ := Γ) q
  have eN : Γ ⊢[PRAAx] rateNumerator (E*B) C (succ p) (succ q) ≐
      (E*B)*(two*unit p)*(two*unit q)+C*(two*unit p+two*unit q) :=
    congrAdd (congrMul (congrMul (.eqRefl _) up) uq) (congrMul (.eqRefl _) (congrAdd up uq))
  have eD : Γ ⊢[PRAAx] rateDenominator C (succ p) (succ q) ≐ C*(two*unit p)*(two*unit q) :=
    congrMul (congrMul (.eqRefl _) up) uq
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (positive_product _ _ hC (positive_product _ _ RationalAlgebra.two_positive (unit_positive p)))
      (positive_product _ _ RationalAlgebra.two_positive (unit_positive q))) (denominator_positive D p q hD) ?_
    (distance_congr (sample_at f p x E).eqSymm (sample_at g q y E).eqSymm eN eD raw)
  dsimp only [B,C,rateNumerator,rateDenominator]
  ipra_le (2*(𝔞 D)^2*𝔞(unit p)*𝔞(unit q)*𝔞(unit s)*𝔞(unit q))*sl (clock_budget p E)+
    (2*(𝔞 D)^2*𝔞(unit p)*𝔞(unit q)*𝔞(unit r)*𝔞(unit p))*sl (clock_budget q E)

theorem log_rate (f g : PR 2) (x y E T U A D : PTm n)
    (hf : Γ ⊢[PRAAx] source f x E T) (hg : Γ ⊢[PRAAx] source g y E U)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] independentRate f g x y A D) :
    Γ ⊢[PRAAx] independentRate (nameF f) (nameF g) (data x E) (data y E) (E*A) D := by
  refine .allI (.allI ?_)
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have hs : Δ ⊢[PRAAx] source f (sh x) (sh E) (sh T) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift.shift
  have gs : Δ ⊢[PRAAx] source g (sh y) (sh E) (sh U) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift.shift
  have ds : Δ ⊢[PRAAx] le one (sh D) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hD.shift.shift
  have rs : Δ ⊢[PRAAx] independentRate f g (sh x) (sh y) (sh A) (sh D) := by
    simpa [Δ,Fm.shift,Syn.shift,sh] using h.shift.shift
  simpa only [independentRate,GaussianNamedPositiveLogarithm.subst_data,sh,Syn.shift,PTm.subst_mul] using
    log_rate_at f g (var 1) (var 0) (sh x) (sh y) (sh E) (sh T) (sh U) (sh A) (sh D) hs gs ds rs

theorem actual_named_positive_logarithm_rate_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((source f (var 0) (var 2) (var 3) ⋏ source g (var 1) (var 2) (var 6)) ⟶
      (le one (var 5) ⋏ independentRate f g (var 0) (var 1) (var 4) (var 5)) ⟶
      independentRate (nameF f) (nameF g) (data (var 0) (var 2)) (data (var 1) (var 2))
        (var 2*var 4) (var 5)) :=
  closeUniv 7 (.impI (.impI (log_rate f g _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianNamedPositiveLogarithmRate
