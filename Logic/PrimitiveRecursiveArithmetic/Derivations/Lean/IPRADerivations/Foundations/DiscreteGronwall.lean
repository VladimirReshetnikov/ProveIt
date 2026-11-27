import IPRADerivations.Analysis.RationalArithmetic.Powers.PowerSums
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.AnalyticNumberTheory.RSA
import IPRADerivations.AnalyticNumberTheory.LocalFactor
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.InductionTactic
import IPRADerivations.Core.Header

/-!
# The discrete Gronwall estimate with a rational growth bound

Packet: `foundations/ipra_local_global`, `paper/04_ode.tex`, "Discrete Gronwall with an entirely rational
growth bound": Lemma `lem:ode-growth`, `(1 + a/k)^k ≤ 3^{⌈a⌉}`, and Lemma `lem:ode-gronwall`: if
`e_{j+1} ≤ r e_j + δ_j` with `r ≥ 1`, then `e_j ≤ r^j (e_0 + ∑_{i<j} δ_i)`; and for `r = 1 + a/k`,
`e_j ≤ 3^{⌈a⌉} (e_0 + ∑ δ_i)` for `j ≤ k` (`eq:ode-gronwall`). These control the Euler polygons of the
packet's ODE construction.

With `r = p/q` (`q ≤ p`) and samples `e(j, x)`, `δ(j, x)`:

* `gronwall` (`lem:ode-gronwall`): if `q e(j+1) ≤ p e(j) + q δ(j)` for `j < N`, then
  `q^N e(N) ≤ p^N (e(0) + ∑_{i<N} δ(i))`;
* `bern`: `k^A (k + A) ≤ k (k+1)^A`, i.e. `1 + A/k ≤ (1 + 1/k)^A`;
* `growth_quad`: for `j ≤ k`, `(k+1)^j k² ≤ k^j (k² + jk + j²)`, i.e.
  `(1 + 1/k)^j ≤ 1 + j/k + (j/k)²`; `three_bound`: `(k+1)^k ≤ 3 k^k` for `k ≥ 1`. The paper bounds
  `(1 + 1/k)^k` by the binomial expansion; the quadratic bound is inductive in `j` and needs no binomial
  coefficients;
* `growth` (`lem:ode-growth`, integer `a = A`): `(k + A)^k ≤ 3^A k^k` for `k ≥ 1`;
* `gronwall_three` (`eq:ode-gronwall`): for `p = k + A`, `q = k ≥ 1` and `N + d = k`,
  `e(N) ≤ 3^A (e(0) + ∑_{i<N} δ(i))`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.DiscreteGronwall

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

/-! ## The Gronwall induction -/

/-- `q^k e(k) ≤ p^k (e(0) + ∑_{i<k} δ(i))`. -/
abbrev GInv (e dl : PTm 2) (k x p q : PTm n) : Fm PTm n :=
  le (pw q k * inst2 e k x) (pw p k * (inst2 e zero x + ap2 (sumF dl) k x))

theorem g_base (e dl : PTm 2) (x p q : PTm n) : Γ ⊢[PRAAx] GInv e dl zero x p q := by
  have z := natEq (sum_zero (Γ := Γ) dl x)
  have pp := natEq (pw_zero (Γ := Γ) p); have pq := natEq (pw_zero (Γ := Γ) q)
  ipra_le 0 using rw [z, pp, pq]; ring

theorem g_step {e dl : PTm 2} {k x p q : PTm n} (hq : Γ ⊢[PRAAx] le q p)
    (c : Γ ⊢[PRAAx] le (q * inst2 e (succ k) x) (p * inst2 e k x + q * inst2 dl k x))
    (ih : Γ ⊢[PRAAx] GInv e dl k x p q) : Γ ⊢[PRAAx] GInv e dl (succ k) x p q := by
  have hpw := pw_le_pw (succ k) hq
  have es := natEq (sum_succ' (Γ := Γ) dl k x)
  have pp := natEq (pw_succ (Γ := Γ) p k); have pq := natEq (pw_succ (Γ := Γ) q k)
  ipra_le 𝔞 (pw q k) * sl c + 𝔞 p * sl ih + sl hpw * 𝔞 (inst2 dl k x) using
    rw [es, pp, pq]; ring

/-- `lem:ode-gronwall`: if `q e(j+1) ≤ p e(j) + q δ(j)` for `j < N` and `q ≤ p`, then
`q^N e(N) ≤ p^N (e(0) + ∑_{i<N} δ(i))`. -/
theorem gronwall (e dl : PTm 2) (x N p q : PTm n) (hq : Γ ⊢[PRAAx] le q p)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift q * inst2 e (succ (var 0)) (Syn.shift x))
        (Syn.shift p * inst2 e (var 0) (Syn.shift x) + Syn.shift q * inst2 dl (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] GInv e dl N x p q := by
  let P := GInv e dl (var 0) (Syn.shift x) (Syn.shift p) (Syn.shift q)
  have atBound : Γ ⊢[PRAAx] P.subst (Syn.inst N) := by
    refine qfIndUpTo N (le_QF _ _) ?_ ?_
    · simpa [P] using g_base (Γ := Γ) e dl x p q
    · simp only [P, subst_le, subst_ap2, subst_inst2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
        Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_zero]
      have hq' : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift q) (Syn.shift p) := by
        simpa only [Fm.shift, subst_le, Syn.shift] using hq.shift
      exact .impI (g_step hq'.wk.wk (.impE h.allOpen.wk.wk Prf.hyp0) Prf.hyp1)
  simpa [P] using atBound

/-! ## Bernoulli, cleared -/

theorem bern_base (k : PTm n) : Γ ⊢[PRAAx] le (pw k zero * (k + zero)) (k * pw (succ k) zero) := by
  have a := natEq (pw_zero (Γ := Γ) k); have b := natEq (pw_zero (Γ := Γ) (succ k))
  ipra_le 0 using rw [a, b]; ring

theorem bern_step {k A : PTm n} (ih : Γ ⊢[PRAAx] le (pw k A * (k + A)) (k * pw (succ k) A)) :
    Γ ⊢[PRAAx] le (pw k (succ A) * (k + succ A)) (k * pw (succ k) (succ A)) := by
  have hp := pw_le_pw A (le_succ_self (Γ := Γ) k)
  have a := natEq (pw_succ (Γ := Γ) k A); have b := natEq (pw_succ (Γ := Γ) (succ k) A)
  ipra_le 𝔞 k * sl ih + 𝔞 k * sl hp using rw [a, b]; ring

/-- Variables: `0 = A` (induction), `1 = k`. -/
private abbrev bernF : Fm PTm 2 := le (pw (var 1) (var 0) * (var 1 + var 0)) (var 1 * pw (succ (var 1)) (var 0))

private theorem bern₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] bernF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · exact bern_base _
  · exact bern_step Prf.hyp0

/-- `1 + A/k ≤ (1 + 1/k)^A`, cleared: `k^A (k + A) ≤ k (k+1)^A`. -/
theorem bern (k A : PTm n) : Γ ⊢[PRAAx] le (pw k A * (k + A)) (k * pw (succ k) A) := by
  have h := inst (Γ := Γ) bern₀ (![A, k] : Fin 2 → PTm n)
  simp at h
  exact h

/-! ## `(1 + 1/k)^k ≤ 3` -/

/-- `(k+1)^j k² ≤ k^j (k² + jk + j²)`. -/
abbrev QInv (j k : PTm n) : Fm PTm n :=
  le (pw (succ k) j * (k * k)) (pw k j * (k * k + j * k + j * j))

theorem quad_base (k : PTm n) : Γ ⊢[PRAAx] QInv zero k := by
  have a := natEq (pw_zero (Γ := Γ) k); have b := natEq (pw_zero (Γ := Γ) (succ k))
  ipra_le 0 using rw [a, b]; ring

theorem quad_step {j k : PTm n} (hj : Γ ⊢[PRAAx] le (succ j) k) (ih : Γ ⊢[PRAAx] QInv j k) :
    Γ ⊢[PRAAx] QInv (succ j) k := by
  have a := natEq (pw_succ (Γ := Γ) k j); have b := natEq (pw_succ (Γ := Γ) (succ k) j)
  ipra_le (𝔞 k + 1) * sl ih + 𝔞 (pw k j) * (𝔞 j * (sl hj + 1) + 𝔞 k) using rw [a, b]; ring

/-- Variables: `0 = j` (induction), `1 = k`. -/
private abbrev quadF : Fm PTm 2 := le (var 0) (var 1) ⟶ QInv (var 0) (var 1)

private theorem quad₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] quadF := by
  ipra_ind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
  · exact .impI (quad_base _)
  · exact .impI (quad_step Prf.hyp0 (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) Prf.hyp0)))

/-- `(1 + 1/k)^j ≤ 1 + j/k + (j/k)²` for `j ≤ k`. -/
theorem growth_quad {j k : PTm n} (hj : Γ ⊢[PRAAx] le j k) : Γ ⊢[PRAAx] QInv j k := by
  have h := inst (Γ := Γ) quad₀ (![j, k] : Fin 2 → PTm n)
  simp at h
  exact Prf.impE h hj

theorem sq_pos (k₀ : PTm n) : Γ ⊢[PRAAx] succ k₀ * succ k₀ ≐ succ (k₀ * k₀ + two * k₀) := by
  ipra_ring

/-- `(k+1)^k ≤ 3 k^k` for `k = k₀ + 1`. -/
theorem three_bound (k₀ : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ (succ k₀)) (succ k₀)) (num 3 * pw (succ k₀) (succ k₀)) := by
  have g := growth_quad (Γ := Γ) (le_refl (succ k₀))
  refine mul_le_cancel (d' := k₀ * k₀ + two * k₀)
    (le_congr (congrMul (sq_pos k₀) (.eqRefl _)) (congrMul (sq_pos k₀) (.eqRefl _)) ?_)
  ipra_le sl g

/-! ## The rational growth bound (`lem:ode-growth`) -/

/-- `(k + A)^k ≤ 3^A k^k` for `k = k₀ + 1`: `(1 + A/k)^k ≤ 3^A`. -/
theorem growth (k₀ A : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ k₀ + A) (succ k₀)) (pw (num 3) A * pw (succ k₀) (succ k₀)) := by
  have b' := pw_le_pw (succ k₀) (bern (Γ := Γ) (succ k₀) A)
  have g' := pw_le_pw A (three_bound (Γ := Γ) k₀)
  have cm : Γ ⊢[PRAAx] A * succ k₀ ≐ succ k₀ * A := mul_comm _ _
  have E1 : Γ ⊢[PRAAx] pw (pw (succ k₀) A * (succ k₀ + A)) (succ k₀) ≐
      pw (succ k₀) (succ k₀ * A) * pw (succ k₀ + A) (succ k₀) :=
    (pw_mul_base _ _ _).eqTrans (congrMul ((pw_mul _ _ _).eqTrans (congrAp2 powF cm (.eqRefl _))) (.eqRefl _))
  have E2 : Γ ⊢[PRAAx] pw (succ k₀ * pw (succ (succ k₀)) A) (succ k₀) ≐
      pw (succ k₀) (succ k₀) * pw (succ (succ k₀)) (succ k₀ * A) :=
    (pw_mul_base _ _ _).eqTrans (congrMul (.eqRefl _) ((pw_mul _ _ _).eqTrans (congrAp2 powF cm (.eqRefl _))))
  have E3 : Γ ⊢[PRAAx] pw (pw (succ (succ k₀)) (succ k₀)) A ≐ pw (succ (succ k₀)) (succ k₀ * A) := pw_mul _ _ _
  have E4 : Γ ⊢[PRAAx] pw (num 3 * pw (succ k₀) (succ k₀)) A ≐
      pw (num 3) A * pw (succ k₀) (succ k₀ * A) :=
    (pw_mul_base _ _ _).eqTrans (congrMul (.eqRefl _) (pw_mul _ _ _))
  have e1 := natEq E1; have e2 := natEq E2; have e3 := natEq E3; have e4 := natEq E4
  have hZ := pw_pos' (Γ := Γ) (p := succ k₀) (congrSucc (pred_succ k₀).eqSymm) (succ k₀ * A)
  refine mul_le_cancel (d' := pred (pw (succ k₀) (succ k₀ * A)))
    (le_congr (congrMul hZ (.eqRefl _)) (congrMul hZ (.eqRefl _)) ?_)
  ipra_le sl b' + 𝔞 (pw (succ k₀) (succ k₀)) * sl g' using rw [e1, e2, e3, e4]; ring

/-! ## Gronwall with the growth bound (`eq:ode-gronwall`) -/

/-- `eq:ode-gronwall`: for `r = (k + A)/k`, `k = k₀ + 1`, and `N + d = k` steps,
`e(N) ≤ 3^A (e(0) + ∑_{i<N} δ(i))`. -/
theorem gronwall_three (e dl : PTm 2) (x N d k₀ A : PTm n) (hk : Γ ⊢[PRAAx] N + d ≐ succ k₀)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift (succ k₀) * inst2 e (succ (var 0)) (Syn.shift x))
        (Syn.shift (succ k₀ + A) * inst2 e (var 0) (Syn.shift x) +
          Syn.shift (succ k₀) * inst2 dl (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (inst2 e N x) (pw (num 3) A * (inst2 e zero x + ap2 (sumF dl) N x)) := by
  have hq : Γ ⊢[PRAAx] le (succ k₀) (succ k₀ + A) := le_add_right _ _
  have gw := gronwall e dl x N (succ k₀ + A) (succ k₀) hq h
  have hd := pw_le_pw d hq
  have gr := growth (Γ := Γ) k₀ A
  have eq1 := natEq ((congrAp2 powF hk.eqSymm (.eqRefl (succ k₀))).eqTrans (pw_add (succ k₀) N d))
  have eq2 := natEq ((congrAp2 powF hk.eqSymm (.eqRefl (succ k₀ + A))).eqTrans (pw_add (succ k₀ + A) N d))
  have hZ := pw_pos' (Γ := Γ) (p := succ k₀) (congrSucc (pred_succ k₀).eqSymm) (succ k₀)
  refine mul_le_cancel (d' := pred (pw (succ k₀) (succ k₀)))
    (le_congr (congrMul hZ (.eqRefl _)) (congrMul hZ (.eqRefl _)) ?_)
  ipra_le 𝔞 (pw (succ k₀) d) * sl gw +
      𝔞 (pw (succ k₀ + A) N) * sl hd * (𝔞 (inst2 e zero x) + 𝔞 (ap2 (sumF dl) N x)) +
      sl gr * (𝔞 (inst2 e zero x) + 𝔞 (ap2 (sumF dl) N x)) using
    rw [eq1, eq2]; ring

end LeanProofs.IPRA.Foundations.DiscreteGronwall
