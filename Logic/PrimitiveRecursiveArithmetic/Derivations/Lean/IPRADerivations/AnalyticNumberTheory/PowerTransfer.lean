import IPRADerivations.AnalyticNumberTheory.PowerBudget
import IPRADerivations.AnalyticNumberTheory.StepParams
import IPRADerivations.AnalyticNumberTheory.AbsDiff
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# The witness transfer along perfect powers (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, proof of Theorem
`thm:powerdivisor`: "It remains to bound either signed sum. Write its `d`th term as `t_d`, set `m_d = ⌊N/d^h⌋` …
the bound at `2r` gives `|t_d|^{4r} ≤ c m_d^{2r+1}`. For `N ≥ 1` put `X = max_{1≤d≤N} d|t_d|`. As `d²m_d ≤ N`,
`(d|t_d|)^{4r} ≤ c N^{2r+1}` … `|Σ t_d| ≤ (ℓ+2)X` … Taking `k = 4r` therefore bounds `|Σ t_d|^{4r}` by
`c(8r)^{4r}N^{2r+2}`. Comparison with the square of `C_r(c)N^{r+1}` proves the assertion." Here `C_r(c) = (c+1)(8r)^{2r}`.

Signed terms are pairs of bodies `t(i) = t⁺(i, y) − t⁻(i, y)` with `|t(i)| = absd(t⁺, t⁻)`; the index `i < N`
stands for `d = i + 1`.

* `mx`: the bounded maximum `max_{i<N} f(i, x)` (`mx_zero`, `mx_succ`), with `le_mx` (every term is below it) and
  `mx_pow_bound` (`f(i)^R ≤ K` for every `i < N` gives `(max)^R ≤ K`, `R ≥ 1`);
* `term_pow`: `((i+1)|t_i|)^{4r} ≤ c N^{2r+1}` from `(i+1)² m_i ≤ N` and `|t_i|^{4r} ≤ c m_i^{2r+1}`;
* `transfer`: `|Σ_{i<N} t(i)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}` for `r ≥ 1` (the packet's `power_divisor_transfer`),
  with `ℓ = ell(N+1)` (`2^ℓ ≤ N ≤ 2^{ℓ+1}`), `PowerBudget.budget_below` and `PowerBudget.log_absorb` at `k = 4r`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PowerBudget (BudgetBelow budget_below log_absorb mul_one')
open LeanProofs.IPRA.AnalyticNumberTheory.StepParams (ell clog_bracket)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd adB inst2_adB absd_sum)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp pw_le_cancel)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The bounded maximum -/

/-- `max(a, b) = a + (b ∸ a)`. -/
abbrev maxT (a b : PTm n) : PTm n := a + monus b a

theorem le_maxT_l (a b : PTm n) : Γ ⊢[PRAAx] le a (maxT a b) := le_add_right a _

theorem le_maxT_r (a b : PTm n) : Γ ⊢[PRAAx] le b (maxT a b) := by
  have m := natEq (monus_max (Γ := Γ) a b)
  ipra_le 𝔞 (monus a b) with m

/-- `max(a, b)` is `a` or `b`. -/
theorem maxT_cases (a b : PTm n) : Γ ⊢[PRAAx] (maxT a b ≐ a) ⋎ (maxT a b ≐ b) := by
  refine .orE (lt_or_le b a) ?_ ?_
  · refine .orI₁ ?_
    have h : (lt b a :: Γ) ⊢[PRAAx] monus b a ≐ zero := le_trans (le_succ_self b) Prf.hyp0
    exact (congrAdd (.eqRefl a) h).eqTrans (add_zero a)
  · exact .orI₂ (eq_add_of_le Prf.hyp0).eqSymm

/-- `M(N, x) = max_{i<N} f(i, x)` (`0` for `N = 0`). -/
def mxF (body : PTm 2) : PR 2 := rec2 zero (maxT (var 1) (bodyStep body))

abbrev mx (body : PTm 2) (N x : PTm n) : PTm n := ap2 (mxF body) N x

@[simp] theorem subst_mx {m : ℕ} (σ : Fin n → PTm m) (body : PTm 2) (N x : PTm n) :
    Syn.subst σ (mx body N x) = mx body (Syn.subst σ N) (Syn.subst σ x) := by simp only [mx, subst_ap2]

theorem mx_zero (body : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] mx body zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (maxT (var 1) (bodyStep body)) x
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem mx_succ (body : PTm 2) (y x : PTm n) :
    Γ ⊢[PRAAx] mx body (succ y) x ≐ maxT (mx body y x) (inst2 body y x) := by
  have h := rec2_succ (Γ := Γ) zero (maxT (var 1) (bodyStep body)) y x
  have e : Syn.subst ![y, ap2 (mxF body) y x, x] (maxT (var 1) (bodyStep body))
      = maxT (ap2 (mxF body) y x) (inst2 body y x) := by
    have hb : Syn.subst ![y, ap2 (mxF body) y x, x] (bodyStep body) = inst2 body y x := by
      rw [bodyStep, Syn.subst_subst]
      exact congrArg (fun σ => Syn.subst σ body) (by funext i; fin_cases i <;> rfl)
    simp only [maxT, PTm.subst_add, PTm.subst_monus, hb]
    rfl
  exact e ▸ h

/-- Every term below `N` is at most the maximum. -/
theorem le_mx (body : PTm 2) {i N x : PTm n} (h : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (inst2 body i x) (mx body N x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (lt (Syn.shift i) (var 0) ⟶
      le (inst2 body (Syn.shift i) (Syn.shift x)) (mx body (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_lt, subst_inst2, subst_mx, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact .impI (lt_zero_absurd _ Prf.hyp0)
    · simp only [Fm.subst_imp, subst_le, subst_lt, subst_inst2, subst_mx, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let φ : Fm PTm (n + 1) := lt (Syn.shift i) (var 0) ⟶
        le (inst2 body (Syn.shift i) (Syn.shift x)) (mx body (var 0) (Syn.shift x))
      let Δ : List (Fm PTm (n + 1)) := lt (Syn.shift i) (succ (var 0)) :: φ :: Γ.map Fm.shift
      have hs : Δ ⊢[PRAAx] mx body (succ (var 0)) (Syn.shift x) ≐
          maxT (mx body (var 0) (Syn.shift x)) (inst2 body (var 0) (Syn.shift x)) := mx_succ _ _ _
      refine le_congr (.eqRefl _) hs.eqSymm ?_
      refine .orE (lt_succ_cases (Prf.hyp0 : Δ ⊢[PRAAx] lt (Syn.shift i) (succ (var 0)))) ?_ ?_
      · have ih : (lt (Syn.shift i) (var 0) :: Δ) ⊢[PRAAx]
            le (inst2 body (Syn.shift i) (Syn.shift x)) (mx body (var 0) (Syn.shift x)) :=
          .impE (hyp2 : (lt (Syn.shift i) (var 0) :: Δ) ⊢[PRAAx] φ) Prf.hyp0
        exact le_trans ih (le_maxT_l _ _)
      · have he : ((Syn.shift i ≐ var 0) :: Δ) ⊢[PRAAx] inst2 body (Syn.shift i) (Syn.shift x) ≐
            inst2 body (var 0) (Syn.shift x) := congrInst2 body Prf.hyp0 (.eqRefl _)
        exact le_congr he.eqSymm (.eqRefl _) (le_maxT_r _ _)
  have a := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_inst2, subst_mx, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at a
  exact .impE a h

/-- `f(i)^R ≤ K` for every `i < N` and `R ≥ 1` give `(max_{i<N} f(i))^R ≤ K`. -/
theorem mx_pow_bound (body : PTm 2) {N x R K : PTm n} (hR : Γ ⊢[PRAAx] le one R)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (pw (inst2 body (var 0) (Syn.shift x)) (Syn.shift R)) (Syn.shift K))) :
    Γ ⊢[PRAAx] le (pw (mx body N x) R) K := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (pw (mx body (var 0) (Syn.shift x)) (Syn.shift R)) (Syn.shift K)) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, subst_mx, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      refine .impI ?_
      have hp := pos_of_one_le (Γ := le zero N :: Γ) hR.wk
      have z : (le zero N :: Γ) ⊢[PRAAx] pw (mx body zero x) R ≐ zero :=
        (congrPw (mx_zero body x) hp).eqTrans ((pw_succ zero (pred R)).eqTrans (mul_zero _))
      exact le_congr z.eqSymm (.eqRefl _) (by ipra_le 𝔞 K)
    · simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, subst_mx, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      refine .impI ?_
      let φ : Fm PTm (n + 1) := le (var 0) (Syn.shift N) ⟶
        le (pw (mx body (var 0) (Syn.shift x)) (Syn.shift R)) (Syn.shift K)
      let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) :: φ :: Γ.map Fm.shift
      have hlt : Δ ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] le (pw (mx body (var 0) (Syn.shift x)) (Syn.shift R)) (Syn.shift K) :=
        .impE Prf.hyp1 (le_trans (le_succ_self _) hlt)
      have ht : Δ ⊢[PRAAx] le (pw (inst2 body (var 0) (Syn.shift x)) (Syn.shift R)) (Syn.shift K) :=
        .impE h.allOpen.wk.wk hlt
      have hs : Δ ⊢[PRAAx] mx body (succ (var 0)) (Syn.shift x) ≐
          maxT (mx body (var 0) (Syn.shift x)) (inst2 body (var 0) (Syn.shift x)) := mx_succ _ _ _
      refine .orE (maxT_cases (Γ := Δ) (mx body (var 0) (Syn.shift x)) (inst2 body (var 0) (Syn.shift x))) ?_ ?_
      · exact le_congr (congrPw (hs.wk.eqTrans Prf.hyp0) (.eqRefl _)).eqSymm (.eqRefl _) ih.wk
      · exact le_congr (congrPw (hs.wk.eqTrans Prf.hyp0) (.eqRefl _)).eqSymm (.eqRefl _) ht.wk
  have a := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, subst_mx, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at a
  exact .impE a (le_refl N)

/-! ## The transfer -/

section Transfer

variable (tP tN mB : PTm 2)

/-- The weighted absolute term `(i+1)|t(i)|`. -/
abbrev wB : PTm 2 := succ (var 0) * adB tP tN

theorem inst2_wB (i y : PTm n) :
    inst2 (wB tP tN) i y = succ i * absd (inst2 tP i y) (inst2 tN i y) := by simp [inst2]

/-- `4r`. -/
abbrev k4 (r : PTm n) : PTm n := two * (two * r)
/-- `8r`. -/
abbrev r8 (r : PTm n) : PTm n := two * k4 r

/-- The argument bound `(i+1)² m_i ≤ N` for `i < N`. -/
abbrev ArgBound (N y : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶ le (pw (succ (var 0)) two * inst2 mB (var 0) (Syn.shift y)) (Syn.shift N))

/-- The input bound `|t_i|^{4r} ≤ c m_i^{2r+1}` for `i < N`. -/
abbrev TermBound (N y r c : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N) ⟶
    le (pw (absd (inst2 tP (var 0) (Syn.shift y)) (inst2 tN (var 0) (Syn.shift y))) (k4 (Syn.shift r)))
      (Syn.shift c * pw (inst2 mB (var 0) (Syn.shift y)) (succ (two * Syn.shift r))))

/-- One weighted term: `((i+1)|t_i|)^{4r} ≤ c N^{2r+1}`. -/
theorem term_pow {i N r c : PTm n} {u m : PTm n}
    (harg : Γ ⊢[PRAAx] le (pw (succ i) two * m) N)
    (hterm : Γ ⊢[PRAAx] le (pw u (k4 r)) (c * pw m (succ (two * r)))) :
    Γ ⊢[PRAAx] le (pw (succ i * u) (k4 r)) (c * pw N (succ (two * r))) := by
  have e1 : Γ ⊢[PRAAx] pw (succ i * u) (k4 r) ≐ pw (succ i) (k4 r) * pw u (k4 r) := pw_mul_base _ _ _
  have hi : Γ ⊢[PRAAx] succ i ≐ succ (pred (succ i)) := pos_of_one_le (by ipra_le 𝔞 i)
  have x1 : Γ ⊢[PRAAx] le (pw (succ i) (k4 r)) (pw (succ i) (two * (succ (two * r)))) :=
    pw_le_exp hi (by ipra_le 2)
  have e2 : Γ ⊢[PRAAx] pw (pw (succ i) two) (succ (two * r)) ≐ pw (succ i) (two * (succ (two * r))) := pw_mul _ _ _
  have x2 : Γ ⊢[PRAAx] le (pw (succ i) (k4 r) * pw u (k4 r)) (pw (pw (succ i) two) (succ (two * r)) * (c * pw m (succ (two * r)))) :=
    le_mul_mono (le_congr (.eqRefl _) e2.eqSymm x1) hterm
  have e3 : Γ ⊢[PRAAx] pw (pw (succ i) two * m) (succ (two * r)) ≐ pw (pw (succ i) two) (succ (two * r)) * pw m (succ (two * r)) := pw_mul_base _ _ _
  have x3 : Γ ⊢[PRAAx] le (c * pw (pw (succ i) two * m) (succ (two * r))) (c * pw N (succ (two * r))) :=
    le_mul_mono (le_refl c) (pw_le_pw (succ (two * r)) harg)
  have r3 : Γ ⊢[PRAAx] pw (pw (succ i) two) (succ (two * r)) * (c * pw m (succ (two * r))) ≐ c * pw (pw (succ i) two * m) (succ (two * r)) := by
    ipra_lc -(𝔞 c) * natEq e3
  exact le_congr e1.eqSymm (.eqRefl _) (le_trans x2 (le_congr r3.eqSymm (.eqRefl _) x3))

/-- `x² = x x`. -/
alias pw_two_sq := Common.pw_two

/-- `a^h a^h = a^{h+h}`. -/
theorem pw_dbl (a h : PTm n) : Γ ⊢[PRAAx] pw a h * pw a h ≐ pw a (h + h) := (pw_add a h h).eqSymm

/-- `|Σ_{i<N} t(i)|^{2r} ≤ (c+1)(8r)^{2r} N^{r+1}` for `r ≥ 1`. -/
theorem transfer {N y r c : PTm n} (hr : Γ ⊢[PRAAx] le one r)
    (harg : Γ ⊢[PRAAx] ArgBound mB N y) (hterm : Γ ⊢[PRAAx] TermBound tP tN mB N y r c) :
    Γ ⊢[PRAAx] le (pw (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (two * r))
      (succ c * pw (r8 r) (two * r) * pw N (succ r)) := by
  have hk : Γ ⊢[PRAAx] le one (k4 r) := by ipra_le sl hr + 𝔞 r + 𝔞 r + 𝔞 r
  refine .orE (lt_or_le zero N) ?_ ?_
  swap
  · -- `N = 0`: both sums vanish.
    have hN : (le N zero :: Γ) ⊢[PRAAx] N ≐ zero := (monus_zero N).eqSymm.eqTrans Prf.hyp0
    have s1 : (le N zero :: Γ) ⊢[PRAAx] ap2 (sumF tP) N y ≐ zero := (congrAp2 _ hN (.eqRefl _)).eqTrans (sum_zero _ _)
    have s2 : (le N zero :: Γ) ⊢[PRAAx] ap2 (sumF tN) N y ≐ zero := (congrAp2 _ hN (.eqRefl _)).eqTrans (sum_zero _ _)
    have hA : (le N zero :: Γ) ⊢[PRAAx] (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) ≐ zero :=
      (congrAdd (congrMonus s1 s2) (congrMonus s2 s1)).eqTrans
        ((congrAdd (monus_zero _) (monus_zero _)).eqTrans (add_zero _))
    have h2 : (le N zero :: Γ) ⊢[PRAAx] two * r ≐ succ (pred (two * r)) :=
      pos_of_one_le (by ipra_le sl hr.wk + 𝔞 r)
    have z : (le N zero :: Γ) ⊢[PRAAx] pw (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (two * r) ≐ zero :=
      (congrPw hA h2).eqTrans ((pw_succ zero _).eqTrans (mul_zero _))
    exact le_congr z.eqSymm (.eqRefl _) (by ipra_le 𝔞 (succ c * pw (r8 r) (two * r) * pw N (succ r)))
  -- `N ≥ 1`
  let Θ : List (Fm PTm n) := lt zero N :: Γ
  have hN1 : Θ ⊢[PRAAx] le one N := Prf.hyp0
  have br := clog_bracket (Γ := Θ) (x := succ N) (by ipra_le sl hN1)
  have b1 : Θ ⊢[PRAAx] le (pw two (ell (succ N))) N := by have a := Prf.andE₁ br; ipra_le sl a
  have b2 : Θ ⊢[PRAAx] le N (pw two (succ (ell (succ N)))) := by have a := Prf.andE₂ br; ipra_le sl a + 1
  -- the maximum of the weighted terms
  have hX : Θ ⊢[PRAAx] le (pw (mx (wB tP tN) N y) (k4 r)) (c * pw N (succ (two * r))) := by
    refine mx_pow_bound (wB tP tN) hk.wk (.allI (.impI ?_))
    rw [inst2_wB]
    let Λ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift N) :: Θ.map Fm.shift
    have ha : Λ ⊢[PRAAx] le (pw (succ (var 0)) two * inst2 mB (var 0) (Syn.shift y)) (Syn.shift N) :=
      .impE ((harg.wk : Θ ⊢[PRAAx] _).allOpen.wk) Prf.hyp0
    have ht : Λ ⊢[PRAAx] le (pw (absd (inst2 tP (var 0) (Syn.shift y)) (inst2 tN (var 0) (Syn.shift y)))
        (k4 (Syn.shift r))) (Syn.shift c * pw (inst2 mB (var 0) (Syn.shift y)) (succ (two * Syn.shift r))) :=
      .impE ((hterm.wk : Θ ⊢[PRAAx] _).allOpen.wk) Prf.hyp0
    have g := term_pow ha ht
    rw [show Syn.shift (k4 r) = k4 (Syn.shift r) by simp [Syn.shift],
      show Syn.shift (c * pw N (succ (two * r))) = Syn.shift c * pw (Syn.shift N) (succ (two * Syn.shift r)) by
        simp [Syn.shift]]
    exact g
  -- the budget `(i+1)|t_i| ≤ (mx (wB tP tN) N y)`
  have hb : Θ ⊢[PRAAx] BudgetBelow (adB tP tN) N y (mx (wB tP tN) N y) := by
    refine .allI (.impI ?_)
    have l := le_mx (Γ := lt (var 0) (Syn.shift N) :: Θ.map Fm.shift) (wB tP tN)
      (x := Syn.shift y) Prf.hyp0
    rw [inst2_wB] at l
    rw [inst2_adB]
    simpa [Syn.shift] using l
  have hs : Θ ⊢[PRAAx] le (ap2 (sumF (adB tP tN)) N y) (succ (succ (ell (succ N))) * (mx (wB tP tN) N y)) := budget_below _ hb b2
  have hA : Θ ⊢[PRAAx] le (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (succ (succ (ell (succ N))) * (mx (wB tP tN) N y)) := le_trans (absd_sum tP tN N y) hs
  -- raise to `4r`
  have p1 : Θ ⊢[PRAAx] le (pw (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (k4 r)) (pw (succ (succ (ell (succ N))) * (mx (wB tP tN) N y)) (k4 r)) := pw_le_pw _ hA
  have e1 : Θ ⊢[PRAAx] pw (succ (succ (ell (succ N))) * (mx (wB tP tN) N y)) (k4 r) ≐ pw ((ell (succ N)) + two) (k4 r) * pw (mx (wB tP tN) N y) (k4 r) :=
    (congrPw (congrMul (by ipra_ring) (.eqRefl (mx (wB tP tN) N y))) (.eqRefl _)).eqTrans (pw_mul_base _ _ _)
  have la := log_absorb (Γ := Θ) hk.wk (ell (succ N))
  have la' : Θ ⊢[PRAAx] le (pw ((ell (succ N)) + two) (k4 r)) (pw (r8 r) (k4 r) * N) :=
    le_trans la (le_mul_mono (le_refl _) b1)
  have p2 : Θ ⊢[PRAAx] le (pw (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (k4 r)) ((pw (r8 r) (k4 r) * N) * (c * pw N (succ (two * r)))) :=
    le_trans p1 (le_congr e1.eqSymm (.eqRefl _) (le_mul_mono la' hX))
  -- compare with `(succ c * pw (r8 r) (two * r) * pw N (succ r))²`
  have q1 : Θ ⊢[PRAAx] pw (pw (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (two * r)) two ≐ pw (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (k4 r) :=
    (pw_two_sq _).eqTrans ((pw_dbl (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (two * r)).eqTrans (congrPw (.eqRefl (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y))) (by ipra_ring)))
  have q2 : Θ ⊢[PRAAx] pw (r8 r) (two * r) * pw (r8 r) (two * r) ≐ pw (r8 r) (k4 r) :=
    (pw_dbl _ _).eqTrans (congrPw (.eqRefl _) (by ipra_ring))
  have q3 : Θ ⊢[PRAAx] pw N (succ r) * pw N (succ r) ≐ pw N (succ (two * r)) * N :=
    (pw_dbl _ _).eqTrans ((congrPw (.eqRefl N) (by ipra_ring)).eqTrans (pw_succ N (succ (two * r))))
  have q4 : Θ ⊢[PRAAx] pw (succ c * pw (r8 r) (two * r) * pw N (succ r)) two ≐ (succ c * pw (r8 r) (two * r) * pw N (succ r)) * (succ c * pw (r8 r) (two * r) * pw N (succ r)) := pw_two_sq (succ c * pw (r8 r) (two * r) * pw N (succ r))
  have f1 := natEq q1
  have f4 := natEq q4
  have gYY : Θ ⊢[PRAAx] (succ c * pw (r8 r) (two * r) * pw N (succ r)) * (succ c * pw (r8 r) (two * r) * pw N (succ r)) ≐ (succ c * succ c) * pw (r8 r) (k4 r) * (pw N (succ (two * r)) * N) := by
    ipra_lc ((𝔞 c + 1) * (𝔞 c + 1) * 𝔞 (pw N (succ r)) * 𝔞 (pw N (succ r))) * natEq q2 +
      ((𝔞 c + 1) * (𝔞 c + 1) * 𝔞 (pw (r8 r) (k4 r))) * natEq q3
  have g := natEq gYY
  have sq : Θ ⊢[PRAAx] le (pw (pw (absd (ap2 (sumF tP) N y) (ap2 (sumF tN) N y)) (two * r)) two) (pw (succ c * pw (r8 r) (two * r) * pw N (succ r)) two) := by
    ipra_le sl p2 + 𝔞 (c * c * pw (r8 r) (k4 r) * pw N (succ (two * r)) * N) + 𝔞 (c * pw (r8 r) (k4 r) * pw N (succ (two * r)) * N) +
      𝔞 (pw (r8 r) (k4 r) * pw N (succ (two * r)) * N) with f4 + g - f1
  exact pw_le_cancel sq

end Transfer

end LeanProofs.IPRA.AnalyticNumberTheory.PowerTransfer
