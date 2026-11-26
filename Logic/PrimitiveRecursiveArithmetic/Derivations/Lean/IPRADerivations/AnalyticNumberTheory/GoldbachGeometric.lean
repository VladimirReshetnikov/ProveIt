import IPRADerivations.Core.SumReflect
import IPRADerivations.Core.BoundedSums
import IPRADerivations.Core.Powers
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.AnalyticNumberTheory.PowerCleared
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Core.ProdLemmas
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# Finite geometric expansions for the Goldbach–Euler theorem

Packet: `goldbach_euler_ipra`, `goldbach_euler_ipra.tex`, Lemmas `lem:geom-den` and `lem:geom-exp`,
with the number of terms as an iPRA variable and denominators cleared.

* `geom_sum`: for `x ≥ 1`, `x^I = (x − 1) ∑_{i<I} x^i + 1`, by induction on `I`;
* `geom_den` (`lem:geom-den`): with `x = r^s`, multiplying
  `1/(x − 1) = ∑_{i=1}^{I} x^{−i} + 1/(x^I (x − 1))` by `x^I (x − 1)` gives exactly `geom_sum`;
  `geom_den_tail`: for `r, s ≥ 2`, `2^{2I} ≤ r^{sI}`, so the remainder is at most `2^{−2I}`;
* `geom_exp` (`lem:geom-exp`): `∑_{s=2}^{T} 1/m^s = 1/(m(m − 1)) − 1/(m^T (m − 1))` multiplied by
  `m^T (m − 1)`: `(m − 1) ∑_{s=2}^{T} m^{T−s} + 1 = m^{T−1}`, the sum written as the reflection
  `∑_{i<T−1} m^{T−2−i}` of `∑_{i<T−1} m^i` (`sum_reflect`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.GoldbachGeometric

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `x^i`; variables `0 = i`, `1 = x`. -/
abbrev gB : PTm 2 := pw (var 1) (var 0)

theorem inst2_gB (i x : PTm n) : inst2 gB i x = pw x i := by simp [inst2]

theorem geom_step {x I : PTm n} (hx : Γ ⊢[PRAAx] le one x)
    (ih : Γ ⊢[PRAAx] pw x I ≐ monus x one * ap2 (sumF gB) I x + one) :
    Γ ⊢[PRAAx] pw x (succ I) ≐ monus x one * ap2 (sumF gB) (succ I) x + one := by
  have s := sum_succ' (Γ := Γ) gB I x
  rw [inst2_gB] at s
  have s' := natEq s; have i' := natEq ih; have p := natEq (pw_succ (Γ := Γ) x I)
  have e := natEq (eq_add_of_le hx)
  apply deriveNat; ipra_simps
  linear_combination p - 𝔞 (monus x one) * s' + i' + 𝔞 (pw x I) * e

/-- Variables `0 = I`, `1 = x`. -/
private abbrev geomF : Fm PTm 2 :=
  le one (var 1) ⟶ pw (var 1) (var 0) ≐ monus (var 1) one * ap2 (sumF gB) (var 0) (var 1) + one

private theorem geom₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] geomF := by
  ipra_ind (⟨le_QF _ _, trivial⟩) [subst_le, subst_ap2]
  · refine .impI ((pw_zero _).eqTrans ?_)
    ipra_lc -𝔞 (monus (var 0) one) * natEq (sum_zero (Γ := [le one (var 0 : PTm 1)]) gB (var 0))
  · exact .impI (geom_step Prf.hyp0 (.impE Prf.hyp1 Prf.hyp0))

/-- `x^I = (x − 1) ∑_{i<I} x^i + 1` for `x ≥ 1`. -/
theorem geom_sum {x : PTm n} (hx : Γ ⊢[PRAAx] le one x) (I : PTm n) :
    Γ ⊢[PRAAx] pw x I ≐ monus x one * ap2 (sumF gB) I x + one := by
  have i := inst (Γ := Γ) geom₀ (![I, x] : Fin 2 → PTm n)
  simp only [geomF, Fm.subst_imp, Fm.subst_eq, subst_le, subst_ap2, PTm.subst_mul, PTm.subst_add,
    PTm.subst_monus, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ] at i
  exact .impE i hx

theorem one_le_pw {r : PTm n} (hr : Γ ⊢[PRAAx] le one r) (s : PTm n) : Γ ⊢[PRAAx] le one (pw r s) :=
  le_congr (Order.pw_one_base s) (.eqRefl _) (pw_le_pw s hr)

/-- `lem:geom-den`, cleared by `x^I (x − 1)` with `x = r^s`: `r^{sI} = (r^s − 1) ∑_{i<I} r^{si} + 1`
(the terms `x^{I−i}`, `1 ≤ i ≤ I`, are the `x^i`, `i < I`). -/
theorem geom_den {r : PTm n} (hr : Γ ⊢[PRAAx] le two r) (s I : PTm n) :
    Γ ⊢[PRAAx] pw (pw r s) I ≐ monus (pw r s) one * ap2 (sumF gB) I (pw r s) + one :=
  geom_sum (one_le_pw (le_trans (le_succ_self _) hr) s) I

/-- The remainder of `lem:geom-den`: for `r, s ≥ 2`, `2^{2I} ≤ (r^s)^I`. -/
theorem geom_den_tail {r s : PTm n} (hr : Γ ⊢[PRAAx] le two r) (hs : Γ ⊢[PRAAx] le two s) (I : PTm n) :
    Γ ⊢[PRAAx] le (pw two (two * I)) (pw (pw r s) I) := by
  have rpos : Γ ⊢[PRAAx] r ≐ succ (pred r) := pos_of_eq_succ (c := succ (monus r two))
    ((eq_add_of_le hr).eqTrans (by ipra_ring))
  have h4 : Γ ⊢[PRAAx] le (pw two two) (pw r s) :=
    le_trans (pw_le_pw two hr) (pw_le_exp rpos hs)
  exact le_congr (pw_mul two two I) (.eqRefl _) (pw_le_pw I h4)

/-- `lem:geom-exp`, cleared by `m^T (m − 1)`: `(m − 1) ∑_{s=2}^{T} m^{T−s} + 1 = m^{T−1}`, the sum as
`∑_{i<T−1} m^{(T−1)−1−i}`. -/
theorem geom_exp {m : PTm n} (hm : Γ ⊢[PRAAx] le two m) (T : PTm n) :
    Γ ⊢[PRAAx] monus m one * ap2 (sumF (rflBody gB)) (monus T one) (pairT (monus T one) m) + one ≐
      pw m (monus T one) := by
  have r := sum_reflect (Γ := Γ) gB (monus T one) m
  exact ((congrAdd (congrMul (.eqRefl _) r.eqSymm) (.eqRefl _))).eqTrans
    (geom_sum (le_trans (le_succ_self _) hm) _).eqSymm

end LeanProofs.IPRA.AnalyticNumberTheory.GoldbachGeometric
