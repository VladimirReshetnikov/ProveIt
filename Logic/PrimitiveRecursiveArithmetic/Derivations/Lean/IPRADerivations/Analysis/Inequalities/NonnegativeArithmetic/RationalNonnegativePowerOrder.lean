import IPRADerivations.Analysis.Inequalities.NonnegativeArithmetic.RationalNonnegativePowers
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# Runtime order reflection and exponent order for nonnegative rational powers

The normalized program power A B k represents the actual fraction A^k/B^k.
Its positive-degree order reflects the order of the two original fractions.
The proof uses the derived strict natural power comparison, rather than a
root operation or a supplied order law. Exponents are antitone below one
and monotone above one, without cancelling a possibly zero numerator or
power. Every numerator, denominator and exponent is an internal number.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.RationalNonnegativePowerOrder

open_ipra
open LeanProofs.IPRA.Analysis.RationalNonnegativePowers (power power_represents denominator_positive)
open LeanProofs.IPRA.Analysis.GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open LeanProofs.IPRA.Analysis.RationalArgmin (rationalLE)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem positive_multiplier_strict (a b c : PTm n) (hab : Γ ⊢[PRAAx] lt a b)
    (hc : Γ ⊢[PRAAx] le one c) : Γ ⊢[PRAAx] lt (a*c) (b*c) :=
  le_trans (le_congr (by ipra_ring) (by ipra_ring) (add_le_add_right (a*c) hc)) (mul_le_mul_right c hab)

/-- A positive exponent is internal. The smaller base may be zero. -/
theorem natural_power_strict (a b k : PTm n) (hab : Γ ⊢[PRAAx] lt a b)
    (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx] lt (pw a k) (pw b k) := by
  have hb : Γ ⊢[PRAAx] le one b := le_trans (zero_lt_succ a) hab
  have first := mul_le_mul_right a (pw_le_pw (pred k) (le_of_lt hab))
  have second := positive_multiplier_strict a b (pw b (pred k)) hab (denominator_positive b (pred k) hb)
  have joined := lt_of_le_of_lt first (lt_congr (mul_comm _ _) (mul_comm _ _) second)
  have shape := RationalIntegerNormalization.positive_form hk
  exact lt_congr ((congrAp2 powF shape (.eqRefl a)).eqTrans (pw_succ a (pred k))).eqSymm
    ((congrAp2 powF shape (.eqRefl b)).eqTrans (pw_succ b (pred k))).eqSymm joined

theorem natural_power_order_reflect (a b k : PTm n) (hk : Γ ⊢[PRAAx] le one k)
    (hPower : Γ ⊢[PRAAx] le (pw a k) (pw b k)) : Γ ⊢[PRAAx] le a b := by
  refine .orE (lt_or_le b a) ?_ Prf.hyp0
  exact le_lt_absurd (le a b) hPower.wk (natural_power_strict b a k Prf.hyp0 hk.wk)

/-- Exact cross-clearing of the actual normalized power fractions. -/
theorem power_order_cleared (A B C D k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hPower : Γ ⊢[PRAAx] rationalLE (power A B k) (power C D k)) : Γ ⊢[PRAAx]
    le (pw (A*D) k) (pw (C*B) k) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (power_represents A B k hB) (power_represents C D k hD) hPower
  exact le_congr (pw_mul_base A D k).eqSymm (pw_mul_base C B k).eqSymm
    (le_congr (mul_comm _ _) (.eqRefl _) raw)

theorem power_order_reflect (A B C D k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k)
    (hPower : Γ ⊢[PRAAx] rationalLE (power A B k) (power C D k)) : Γ ⊢[PRAAx]
    rationalLE (fraction A B) (fraction C D) :=
  fraction_order _ _ _ _ hB hD (le_congr (mul_comm _ _) (.eqRefl _)
    (natural_power_order_reflect (A*D) (C*B) k hk (power_order_cleared A B C D k hB hD hPower)))

theorem power_order_preserve (A B C D k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] rationalLE (fraction A B) (fraction C D)) : Γ ⊢[PRAAx]
    rationalLE (power A B k) (power C D k) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (fraction_represents A B hB) (fraction_represents C D hD) h
  have crossed : Γ ⊢[PRAAx] le (A*D) (C*B) := le_congr (mul_comm _ _) (.eqRefl _) raw
  exact fraction_order _ _ _ _ (denominator_positive B k hB) (denominator_positive D k hD)
    (le_congr ((pw_mul_base A D k).eqTrans (mul_comm _ _)) (pw_mul_base C B k) (pw_le_pw k crossed))

theorem power_order_iff (A B C D k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k) : Γ ⊢[PRAAx]
    Fm.iff (rationalLE (power A B k) (power C D k)) (rationalLE (fraction A B) (fraction C D)) :=
  .iffI (.impI (power_order_reflect A B C D k hB.wk hD.wk hk.wk Prf.hyp0))
    (.impI (power_order_preserve A B C D k hB.wk hD.wk Prf.hyp0))

theorem power_factor (A i j : PTm n) (hij : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx]
    pw A j ≐ pw A i*pw A (monus j i) :=
  (congrAp2 powF (eq_add_of_le hij) (.eqRefl A)).eqTrans (pw_add A i (monus j i))

/-- No numerator or power is cancelled: this includes A=0 and i=0. -/
theorem exponent_cross_antitone (A B i j : PTm n) (hAB : Γ ⊢[PRAAx] le A B)
    (hij : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx]
    le (pw B i*pw A j) (pw A i*pw B j) := by
  have first := mul_le_mul_right (pw A i*pw B i) (pw_le_pw (monus j i) hAB)
  have a := natEq (power_factor (Γ := Γ) A i j hij)
  have b := natEq (power_factor (Γ := Γ) B i j hij)
  apply le_congr (a' := pw B i*pw A j) (b' := pw A i*pw B j) ?_ ?_ first
  · apply deriveNat
    ipra_simps
    rw [a]
    ring
  · apply deriveNat
    ipra_simps
    rw [b]
    ring

theorem power_exponent_antitone (A B i j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hAB : Γ ⊢[PRAAx] le A B) (hij : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx]
    rationalLE (power A B j) (power A B i) :=
  fraction_order _ _ _ _ (denominator_positive B j hB) (denominator_positive B i hB)
    (exponent_cross_antitone A B i j hAB hij)

theorem power_exponent_monotone (A B i j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hBA : Γ ⊢[PRAAx] le B A) (hij : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx]
    rationalLE (power A B i) (power A B j) :=
  fraction_order _ _ _ _ (denominator_positive B i hB) (denominator_positive B j hB)
    (le_congr (mul_comm _ _) (mul_comm _ _) (exponent_cross_antitone B A i j hBA hij))

theorem power_exponent_antitone_of_le_one (A B i j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hUnit : Γ ⊢[PRAAx] rationalLE (fraction A B) (fraction one one))
    (hij : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx] rationalLE (power A B j) (power A B i) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (fraction_represents A B hB) (fraction_represents one one (le_refl one)) hUnit
  exact power_exponent_antitone A B i j hB (le_congr (one_mul _) (one_mul _) raw) hij

theorem power_exponent_monotone_of_one_le (A B i j : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hUnit : Γ ⊢[PRAAx] rationalLE (fraction one one) (fraction A B))
    (hij : Γ ⊢[PRAAx] le i j) : Γ ⊢[PRAAx] rationalLE (power A B i) (power A B j) := by
  have raw := GaussianRationalMetric.comparison_to_cleared _ _ _ _ _ _
    (fraction_represents one one (le_refl one)) (fraction_represents A B hB) hUnit
  exact power_exponent_monotone A B i j hB (le_congr (by ipra_ring) (by ipra_ring) raw) hij

theorem power_le_one (A B k : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hAB : Γ ⊢[PRAAx] le A B) : Γ ⊢[PRAAx]
    rationalLE (power A B k) (fraction one one) :=
  RationalArgmin.rationalLE_congr (.eqRefl _) (RationalNonnegativePowers.power_zero A B)
    (power_exponent_antitone A B zero k hB hAB (zero_le k))

/- The actual PR5 returns the two normalized powers and the two original
normalized fractions. Reflection below applies to these returned fields. -/
def output (A B C D k : PTm n) : PTm n :=
  pairT (power A B k) (pairT (power C D k) (pairT (fraction A B) (fraction C D)))
def outputF : PR 5 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3) (var 4))
def run (A B C D k : PTm n) : PTm n := PTm.app outputF ![A,B,C,D,k]
ipra_subst output
ipra_subst run
theorem program_at (A B C D k : PTm n) : Γ ⊢[PRAAx] run A B C D k ≐ output A B C D k := by
  simpa [run,outputF] using toPR_eq (Γ := Γ)
    (output (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) ![A,B,C,D,k]
theorem returned_left_power (A B C D k : PTm n) : Γ ⊢[PRAAx]
    fstT (run A B C D k) ≐ power A B k :=
  (program_at A B C D k).fstE
theorem returned_right_power (A B C D k : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (run A B C D k)) ≐ power C D k :=
  (program_at A B C D k).sndE.fstE
theorem returned_left_base (A B C D k : PTm n) : Γ ⊢[PRAAx]
    fstT (sndT (sndT (run A B C D k))) ≐ fraction A B :=
  (program_at A B C D k).sndE.sndE.fstE
theorem returned_right_base (A B C D k : PTm n) : Γ ⊢[PRAAx]
    sndT (sndT (sndT (run A B C D k))) ≐ fraction C D :=
  (program_at A B C D k).sndE.sndE.sndE
theorem returned_order_reflection (A B C D k : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hD : Γ ⊢[PRAAx] le one D) (hk : Γ ⊢[PRAAx] le one k)
    (hPower : Γ ⊢[PRAAx] rationalLE (fstT (run A B C D k)) (fstT (sndT (run A B C D k)))) : Γ ⊢[PRAAx]
    rationalLE (fstT (sndT (sndT (run A B C D k)))) (sndT (sndT (sndT (run A B C D k)))) :=
  RationalArgmin.rationalLE_congr (returned_left_base A B C D k).eqSymm (returned_right_base A B C D k).eqSymm
    (power_order_reflect A B C D k hB hD hk
      (RationalArgmin.rationalLE_congr (returned_left_power A B C D k) (returned_right_power A B C D k) hPower))

theorem natural_positive_power_order_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 2) ⟶ le (pw (var 0) (var 2)) (pw (var 1) (var 2)) ⟶ le (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (natural_power_order_reflect _ _ _ Prf.hyp1 Prf.hyp0)))
theorem rational_positive_power_order_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ le one (var 4) ⟶
      rationalLE (power (var 0) (var 1) (var 4)) (power (var 2) (var 3) (var 4)) ⟶
        rationalLE (fraction (var 0) (var 1)) (fraction (var 2) (var 3))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (power_order_reflect _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))
theorem rational_positive_power_order_iff_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ le one (var 4) ⟶
      Fm.iff (rationalLE (power (var 0) (var 1) (var 4)) (power (var 2) (var 3) (var 4)))
        (rationalLE (fraction (var 0) (var 1)) (fraction (var 2) (var 3)))) :=
  closeUniv 5 (.impI (.impI (.impI (power_order_iff _ _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem rational_power_exponent_antitone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶ le (var 2) (var 3) ⟶
      rationalLE (power (var 0) (var 1) (var 3)) (power (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (power_exponent_antitone _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem rational_power_exponent_monotone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ le (var 1) (var 0) ⟶ le (var 2) (var 3) ⟶
      rationalLE (power (var 0) (var 1) (var 2)) (power (var 0) (var 1) (var 3))) :=
  closeUniv 4 (.impI (.impI (.impI (power_exponent_monotone _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem actual_unit_interval_power_antitone_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 1) ⟶ rationalLE (fraction (var 0) (var 1)) (fraction one one) ⟶ le (var 2) (var 3) ⟶
      rationalLE (power (var 0) (var 1) (var 3)) (power (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (.impI (.impI (power_exponent_antitone_of_le_one _ _ _ _ Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0))))
theorem unit_interval_power_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (le one (var 1) ⟶ le (var 0) (var 1) ⟶ rationalLE (power (var 0) (var 1) (var 2)) (fraction one one)) :=
  closeUniv 3 (.impI (.impI (power_le_one _ _ _ Prf.hyp1 Prf.hyp0)))
theorem power_order_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (run (var 0) (var 1) (var 2) (var 3) (var 4) ≐ output (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (program_at _ _ _ _ _)
theorem returned_positive_power_order_reflection_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le one (var 1) ⟶ le one (var 3) ⟶ le one (var 4) ⟶
      rationalLE (fstT (run (var 0) (var 1) (var 2) (var 3) (var 4)))
        (fstT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))) ⟶
      rationalLE (fstT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))
        (sndT (sndT (sndT (run (var 0) (var 1) (var 2) (var 3) (var 4)))))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI
    (returned_order_reflection _ _ _ _ _ Prf.hyp0.wk.wk.wk Prf.hyp0.wk.wk Prf.hyp1 Prf.hyp0)))))

end LeanProofs.IPRA.Analysis.RationalNonnegativePowerOrder
