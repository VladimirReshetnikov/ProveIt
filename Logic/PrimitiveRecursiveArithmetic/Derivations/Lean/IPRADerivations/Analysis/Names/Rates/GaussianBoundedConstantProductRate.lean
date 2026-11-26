import IPRADerivations.Analysis.Names.FiniteOperations.GaussianBoundedConstantProductName
import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-!
# Exact input rates for the actual bounded constant-product program

Both original queries are retained. The supplied numerical constant
bound multiplies only the leading input distance; each actual Fast clock
pays its own observation allowance. No denominator-dependent gain or
extra regularity/output premise is used.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBoundedConstantProductRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBoundedConstantProductName (nameF data sample_at clock)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalHorner (positive_product)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem original_observations (f g : PR 2) (p q A c x y X D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hc : Γ ⊢[PRAAx] bounded c A one)
    (hr : Γ ⊢[PRAAx] independentRate f g x y X D) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF f) p (data A c x)) (ap2 (nameF g) q (data A c y))
      (rateNumerator (A*X) D p q) (rateDenominator D p q) := by
  let s := clock p A
  let t := clock q A
  let P := unit p
  let Qr := unit q
  let U := unit s
  let V := unit t
  have hOld : Γ ⊢[PRAAx] le one (rateDenominator D s t) :=
    positive_product _ _ (positive_product _ _ hD (unit_positive s)) (unit_positive t)
  have hNew : Γ ⊢[PRAAx] le one (rateDenominator D p q) :=
    positive_product _ _ (positive_product _ _ hD (unit_positive p)) (unit_positive q)
  have raw := GaussianNamedInverseRate.rate_at f g x y X D s t hr
  have product := GaussianRationalReciprocal.bounded_product c _ A one _ _ (le_refl one) hOld hc raw
  have difference : Γ ⊢[PRAAx] distanceBounded
      (GaussianRationalHorner.qmul c (ap2 f s x)) (GaussianRationalHorner.qmul c (ap2 g t y))
      (A*rateNumerator X D s t) (rateDenominator D s t) :=
    GaussianRationalReciprocal.bound_congr (GaussianRationalRoundedPower.multiplication_difference c _ _).eqSymm
      (.eqRefl _) (one_mul _) product
  have bP : Γ ⊢[PRAAx] le (A*P) U := GaussianFastValueCut.query_budget A p
  have bQ : Γ ⊢[PRAAx] le (A*Qr) V := GaussianFastValueCut.query_budget A q
  have coarse := distance_radius_mono _ _ _ _ (rateNumerator (A*X) D p q) (rateDenominator D p q) hOld hNew
    (by unfold rateNumerator rateDenominator; dsimp only [P,Qr,U,V,s,t] at bP bQ ⊢
        ipra_le (𝔞 D*𝔞 D*𝔞 (unit q)*𝔞 (unit (clock q A)))*sl bP+
          (𝔞 D*𝔞 D*𝔞 (unit p)*𝔞 (unit (clock p A)))*sl bQ) difference
  exact distance_congr (sample_at f p A c x).eqSymm (sample_at g q A c y).eqSymm (.eqRefl _) (.eqRefl _) coarse

theorem original_rate (f g : PR 2) (A c x y X D : PTm n)
    (hD : Γ ⊢[PRAAx] le one D) (hc : Γ ⊢[PRAAx] bounded c A one)
    (hr : Γ ⊢[PRAAx] independentRate f g x y X D) : Γ ⊢[PRAAx]
    independentRate (nameF f) (nameF g) (data A c x) (data A c y) (A*X) D := by
  let sh (u : PTm n) := Syn.shift (Syn.shift u)
  have hd : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,one] using hD.shift.shift
  have hb : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] bounded (sh c) (sh A) one := by simpa [Fm.shift,Syn.shift,sh,one] using hc.shift.shift
  have hh : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate f g (sh x) (sh y) (sh X) (sh D) := by
    simpa [Fm.shift,Syn.shift,sh] using hr.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,GaussianBoundedConstantProductName.subst_data,PTm.subst_mul,Syn.shift,sh] using
    original_observations f g (var 1) (var 0) (sh A) (sh c) (sh x) (sh y) (sh X) (sh D) hd hb hh

theorem actual_bounded_constant_product_input_rate_closed (f g : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 5) ⋏ (bounded (var 1) (var 0) one ⋏ independentRate f g (var 2) (var 3) (var 4) (var 5))) ⟶
      independentRate (nameF f) (nameF g) (data (var 0) (var 1) (var 2)) (data (var 0) (var 1) (var 3))
        (var 0*var 4) (var 5)) :=
  closeUniv 6 (.impI (original_rate f g _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBoundedConstantProductRate
