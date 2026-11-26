import IPRADerivations.Analysis.Names.Rates.Reciprocals.GaussianNamedInverseRate

/-! Increase the leading radius of an independent rate while retaining its
original two observation allowances. -/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRateRadius

open_ipra
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator denominator_positive rate_at shift_independent_rate)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_radius_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem succ_clock_budget (p q : PTm n) : Γ ⊢[PRAAx] le
    (rateNumerator one (unit (succ p)) (succ p) (succ q)*(unit p*unit q))
    ((unit p+unit q)*rateDenominator (unit (succ p)) (succ p) (succ q)) := by
  have dp : Γ ⊢[PRAAx] unit (succ p) ≐ unit p*two := pw_succ two p
  have dq : Γ ⊢[PRAAx] unit (succ q) ≐ unit q*two := pw_succ two q
  have rd := congrMul (congrMul dp dp) dq
  have rn := congrAdd (congrMul (congrMul (.eqRefl one) dp) dq) (congrMul dp (congrAdd dp dq))
  exact le_congr (congrMul rn (.eqRefl _)).eqSymm (congrMul (.eqRefl _) rd).eqSymm
    (le_of_eq_add (d := two*two*unit p*unit p*unit p*unit q) (by ipra_ring))

/-- One leading error at the successor of the first clock leaves room for
both observation errors at the earlier requested precisions. -/
theorem distance_at_succ_clocks (a b p q : PTm n)
    (h : Γ ⊢[PRAAx] distanceBounded a b (rateNumerator one (unit (succ p)) (succ p) (succ q))
      (rateDenominator (unit (succ p)) (succ p) (succ q))) :
    Γ ⊢[PRAAx] distanceBounded a b (unit p+unit q) (unit p*unit q) :=
  distance_radius_mono _ _ _ _ _ _ (denominator_positive _ _ _ (unit_positive (succ p)))
    (positive_product _ _ (unit_positive p) (unit_positive q)) (succ_clock_budget p q) h

/-- Two observations at least one bit later than the requested precision
fit a single dyadic allowance at that precision. -/
theorem distance_at_later_clocks {a b : PTm n} (r t m : PTm n)
    (hr : Γ ⊢[PRAAx] le (succ m) r) (ht : Γ ⊢[PRAAx] le (succ m) t)
    (h : Γ ⊢[PRAAx] distanceBounded a b (unit r+unit t) (unit r*unit t)) :
    Γ ⊢[PRAAx] distanceBounded a b one (unit m) := by
  have double : Γ ⊢[PRAAx] unit (succ m) ≐ two*unit m := (pw_succ two m).eqTrans (mul_comm _ _)
  have rGrow : Γ ⊢[PRAAx] le (unit (succ m)) (unit r) :=
    GaussianFactorBudget.power_monotone_length two (succ m) r (le_succ_self one) hr
  have tGrow : Γ ⊢[PRAAx] le (unit (succ m)) (unit t) :=
    GaussianFactorBudget.power_monotone_length two (succ m) t (le_succ_self one) ht
  have left := mul_le_mul_right (unit t) (le_congr double (.eqRefl _) rGrow)
  have right := mul_le_mul_right (unit r) (le_congr double (.eqRefl _) tGrow)
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive r) (unit_positive t)) (unit_positive m) ?_ h
  exact RationalValueBounds.positive_cancel RationalAlgebra.two_positive
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ left right))

/-- At the successor of the first observation clock, both the leading error
and the first observation allowance fit the earlier unit if the leading
budget is paid by the denominator. -/
theorem distance_at_first_succ (a b A B p q : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (paid : Γ ⊢[PRAAx] le (A*unit (succ p)) B)
    (h : Γ ⊢[PRAAx] distanceBounded a b (rateNumerator A B (succ p) q) (rateDenominator B (succ p) q)) :
    Γ ⊢[PRAAx] distanceBounded a b (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let W := unit (succ p)
  apply distance_radius_mono _ _ _ _ _ _ (denominator_positive B (succ p) q hB)
    (positive_product _ _ (unit_positive p) (unit_positive q)) ?_ h
  change Γ ⊢[PRAAx] le ((A*W*V+B*(W+V))*(U*V)) ((U+V)*(B*W*V))
  refine le_of_eq_add (d := U*V*V*monus B (A*W)) ?_
  have paidEq : Γ ⊢[PRAAx] B ≐ A*W+monus B (A*W) := eq_add_of_le paid
  have doubled : Γ ⊢[PRAAx] W ≐ U*two := pw_succ two p
  have budget := natEq paidEq
  have next := natEq doubled
  apply deriveNat
  ipra_simps
  linear_combination 𝔞(U)*𝔞(V)^2*budget + 𝔞(B)*𝔞(V)^2*next

/-- Enlarge the second dyadic allowance while keeping both observations and
the first allowance fixed. -/
theorem relax_second_clock (a b p q r : PTm n) (hqr : Γ ⊢[PRAAx] le q r)
    (h : Γ ⊢[PRAAx] distanceBounded a b (unit p+unit r) (unit p*unit r)) :
    Γ ⊢[PRAAx] distanceBounded a b (unit p+unit q) (unit p*unit q) := by
  let U := unit p
  let V := unit q
  let W := unit r
  have grow : Γ ⊢[PRAAx] le V W :=
    GaussianFactorBudget.power_monotone_length two q r (le_succ_self one) hqr
  apply distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive p) (unit_positive r))
    (positive_product _ _ (unit_positive p) (unit_positive q)) ?_ h
  change Γ ⊢[PRAAx] le ((U+W)*(U*V)) ((U+V)*(U*W))
  ipra_le 𝔞(U)*𝔞(U)*sl grow

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
  have bs := Order.shift_one_le (Order.shift_one_le hB)
  have ds := Order.shift_one_le (Order.shift_one_le hD)
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (sh A*sh D) (sh C*sh B) :=
    by simpa [Fm.shift,Syn.shift,sh] using h.shift.shift
  have rs := shift_independent_rate (shift_independent_rate hr)
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
