import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-! Increase the leading radius of an independent rate while retaining its
original two observation allowances. -/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRateRadius

open_ipra
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive rate_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem observation_at (F G : PR 2) (p q x y A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] le (A*D) (C*B))
    (hr : Γ ⊢[PRAAx] independentRate F G x y A B) :
    Γ ⊢[PRAAx] distanceBounded (ap2 F p x) (ap2 G q y) (rateNumerator C D p q) (rateDenominator D p q) :=
  distance_radius_mono _ _ _ _ _ _ (denominator_positive B p q hB) (denominator_positive D p q hD)
    (by dsimp only [rateNumerator,rateDenominator]; ipra_le (𝔞(unit p)*𝔞(unit q))^2*sl h)
    (rate_at F G x y A B p q hr)

theorem weaken (F G : PR 2) (x y A B C D : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] le (A*D) (C*B))
    (hr : Γ ⊢[PRAAx] independentRate F G x y A B) : Γ ⊢[PRAAx] independentRate F G x y C D := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  have bs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,one] using hB.shift.shift
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (sh D) := by simpa [Fm.shift,Syn.shift,sh,one] using hD.shift.shift
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (sh A*sh D) (sh C*sh B) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  have rs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate F G (sh x) (sh y) (sh A) (sh B) :=
    by simpa [Fm.shift,Syn.shift,sh] using hr.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,sh] using observation_at F G (var 1) (var 0) (sh x) (sh y) (sh A) (sh B) (sh C) (sh D) bs ds hs rs

/-- Keep the leading numerator and use an earlier dyadic precision. -/
theorem weaken_dyadic (F G : PR 2) (x y A p r : PTm n) (hp : Γ ⊢[PRAAx] le p r)
    (h : Γ ⊢[PRAAx] independentRate F G x y A (unit r)) :
    Γ ⊢[PRAAx] independentRate F G x y A (unit p) :=
  weaken F G x y A (unit r) A (unit p) (unit_positive r) (unit_positive p)
    (mul_le_mul_left A (GaussianFactorBudget.power_monotone_length two p r (le_succ_self one) hp)) h

theorem original_independent_rate_radius_weakening_closed (F G : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 3) ⋏ (le one (var 5) ⋏ le (var 2*var 5) (var 4*var 3))) ⟶
      independentRate F G (var 0) (var 1) (var 2) (var 3) ⟶ independentRate F G (var 0) (var 1) (var 4) (var 5)) :=
  closeUniv 6 (.impI (.impI (weaken F G _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedRateRadius
