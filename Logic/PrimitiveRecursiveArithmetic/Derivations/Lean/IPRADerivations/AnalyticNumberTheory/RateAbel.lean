import IPRADerivations.AnalyticNumberTheory.PowerDivisorUniform
import IPRADerivations.DiophantineNumberTheory.Dirichlet

/-!
# Dyadic shell weights and the recovery of growth from bounded weighted sums
(`riemann_ipra_equivalences_2026-11-20`, `thm:rate`, direction (2) ⇒ (1))

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `series.tex`, Theorem `thm:rate`: with
`B = 2^{2r}`, `j(n) = ⌊⌊log₂ n⌋/(2r)⌋`, `u_n = 2^{(r+1)j(n)}` and `S_r(N) = Σ_{n≤N} a_n/u_n`, "For (2) to (1),
finite summation by parts gives `M(N) = u_N S_r(N) − Σ_{i<N} (u_{i+1} − u_i) S_r(i)` … the absolute value is at most
`2^{K+1} u_N`. Now `u_N^{2r} = (B^{j(N)})^{r+1} ≤ N^{r+1}`. Hence the output witness is `c = 2^{2r(K+1)}`."

Denominators are cleared exactly: `W(N) = u_N S_r(N)` is the primitive recursion `W(0) = 0`,
`W(N+1) = ρ_N W(N) + a(N+1)` with `ρ_N = u_{N+1}/u_N = 2^{(r+1)(j(N+1) − j(N))}`. Signed coefficients are pairs of
bodies `a = a⁺ − a⁻`, and `M(N) = Σ_{m<N} a(m+1)`.

* `lg` (`⌊log₂ x⌋ = ell(x+1)`), `lg_bracket`, `lg_mono`; `jj`, `uu`, `rho`, `uu_succ` (`u_{N+1} = ρ_N u_N` for
  `N ≥ 1`), `uu_pow` (`u_N^{2r} ≤ N^{r+1}`);
* `Wv`, `W_zero`, `W_succ`;
* `diff_bound`: if `|W(i)| ≤ 2^K u_i` for every `i`, then `|M(N) − W(N)| ≤ 2^K u_N`, by induction — the difference
  `D = M − W` satisfies `D(N+1) = D(N) − (ρ_N − 1) W(N)` (the summation by parts, telescoped);
* `recover`: then `|M(N)|^{2r} ≤ 2^{2r(K+1)} N^{r+1}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.RateAbel

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.StepParams (ell clog_bracket)
open LeanProofs.IPRA.DiophantineNumberTheory.Dirichlet (quo_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerCleared (pw_le_exp)
open LeanProofs.IPRA.AnalyticNumberTheory.RSA (pw_mul)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockChain (one_le_pw')
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open LeanProofs.IPRA.AnalyticNumberTheory.AbsDiff (absd absd_le le_absd_l le_absd_r)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Shells -/

/-- `⌊log₂ x⌋` for `x ≥ 1`. -/
abbrev lg (x : PTm n) : PTm n := ell (succ x)

theorem lg_bracket {x : PTm n} (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] le (pw two (lg x)) x ⋏ lt x (pw two (succ (lg x))) := by
  have b := clog_bracket (Γ := Γ) (x := succ x) (by ipra_le sl hx)
  refine .andI ?_ (Prf.andE₂ b)
  have a := Prf.andE₁ b
  ipra_le sl a

theorem two_pos : Γ ⊢[PRAAx] (two : PTm n) ≐ succ (pred two) := pos_of_one_le (by ipra_le 1)

theorem lg_mono {x : PTm n} (hx : Γ ⊢[PRAAx] le one x) : Γ ⊢[PRAAx] le (lg x) (lg (succ x)) := by
  refine .orE (lt_or_le (lg (succ x)) (lg x)) ?_ Prf.hyp0
  let C : List (Fm PTm n) := lt (lg (succ x)) (lg x) :: Γ
  have h : C ⊢[PRAAx] lt (lg (succ x)) (lg x) := Prf.hyp0
  have b1 := Prf.andE₁ (lg_bracket (Γ := C) hx.wk)
  have b2 := Prf.andE₂ (lg_bracket (Γ := C) (x := succ x) (by ipra_le sl hx.wk + 1))
  have p := pw_le_exp (Γ := C) two_pos h
  have c : C ⊢[PRAAx] le (succ (succ x)) x := le_trans b2 (le_trans p b1)
  exact lt_irrefl x _ (le_trans (le_succ_self _) c)

/-- `j(x) = ⌊⌊log₂ x⌋/(2r)⌋`. -/
abbrev jj (r x : PTm n) : PTm n := quo (lg x) (two * r)
/-- `u_x = 2^{(r+1) j(x)}`. -/
abbrev uu (r x : PTm n) : PTm n := pw two (succ r * jj r x)
/-- `ρ_x = 2^{(r+1)(j(x+1) − j(x))}`. -/
abbrev rho (r x : PTm n) : PTm n := pw two (succ r * monus (jj r (succ x)) (jj r x))

theorem two_r_pos {r : PTm n} (hr : Γ ⊢[PRAAx] le one r) : Γ ⊢[PRAAx] two * r ≐ succ (pred (two * r)) :=
  pos_of_one_le (by ipra_le sl hr + 𝔞 r)

theorem jj_mono {r x : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] le (jj r x) (jj r (succ x)) := quo_mono (two_r_pos hr) (lg_mono hx)

/-- `u_{x+1} = ρ_x u_x` for `x ≥ 1`. -/
theorem uu_succ {r x : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hx : Γ ⊢[PRAAx] le one x) :
    Γ ⊢[PRAAx] uu r (succ x) ≐ rho r x * uu r x := by
  have e := eq_add_of_le (jj_mono hr hx)
  refine Prf.eqTrans ?_ (pw_add two _ _)
  refine congrPw (.eqRefl _) ?_
  have f := natEq e
  apply deriveNat; ipra_simps
  linear_combination (𝔞 r + 1) * f

theorem rho_pos (r x : PTm n) : Γ ⊢[PRAAx] le one (rho r x) := one_le_pw' (by ipra_le 1) _

theorem uu_pos (r x : PTm n) : Γ ⊢[PRAAx] le one (uu r x) := one_le_pw' (by ipra_le 1) _

/-- `u_N^{2r} ≤ N^{r+1}` for `N ≥ 1`. -/
theorem uu_pow {r N : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] le (pw (uu r N) (two * r)) (pw N (succ r)) := by
  have d := div_mod_at (Γ := Γ) (x := lg N) (y := two * r) (c := pred (two * r)) (two_r_pos hr)
  have e1 := natEq (Prf.andE₁ d)
  have hle : Γ ⊢[PRAAx] le (two * r * jj r N) (lg N) := by ipra_le 𝔞 (rem (lg N) (two * r)) with e1
  have p1 := le_trans (pw_le_exp two_pos hle) (Prf.andE₁ (lg_bracket hN))
  have p2 := pw_le_pw (succ r) p1
  have e2 : Γ ⊢[PRAAx] pw (uu r N) (two * r) ≐ pw (pw two (two * r * jj r N)) (succ r) :=
    (pw_mul _ _ _).eqTrans ((congrPw (.eqRefl _) (by apply deriveNat; ipra_simps; ring)).eqTrans (pw_mul _ _ _).eqSymm)
  exact le_congr e2.eqSymm (.eqRefl _) p2

/-! ## The cleared weighted sums -/

variable (a : PTm 2)

/-- `W(N+1) = ρ_N W(N) + a(N+1)` over `0 = N`, `1 = W(N)`, `2 = ⟨r, y⟩`. -/
def wStep : PTm 3 :=
  rho (fstT (var 2)) (var 0) * var 1 + Syn.subst ![succ (var 0), sndT (var 2)] a

def Wf : PR 2 := rec2 zero (wStep a)

/-- `W(N) = u_N S_r(N)`. -/
abbrev Wv (r y N : PTm n) : PTm n := ap2 (Wf a) N (pairT r y)

/-- `M(N) = Σ_{m<N} a(m+1)`. -/
abbrev Mv (y N : PTm n) : PTm n := ap2 (sumF (shiftBody a)) N y

theorem W_zero (r y : PTm n) : Γ ⊢[PRAAx] Wv a r y zero ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (wStep a) (pairT r y)
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem W_succ (r y N : PTm n) :
    Γ ⊢[PRAAx] Wv a r y (succ N) ≐ rho r N * Wv a r y N + inst2 a (succ N) y := by
  have h : Γ ⊢[PRAAx] ap2 (Wf a) (succ N) (pairT r y) ≐
      Syn.subst ![N, ap2 (Wf a) N (pairT r y), pairT r y] (wStep a) :=
    rec2_succ (Γ := Γ) zero (wStep a) N (pairT r y)
  have e : Syn.subst ![N, ap2 (Wf a) N (pairT r y), pairT r y] (wStep a) =
      rho (fstT (pairT r y)) N * ap2 (Wf a) N (pairT r y) + inst2 a (succ N) (sndT (pairT r y)) := by
    have ha : Syn.subst ![N, ap2 (Wf a) N (pairT r y), pairT r y] (Syn.subst ![succ (var 0), sndT (var 2)] a) =
        inst2 a (succ N) (sndT (pairT r y)) := by
      simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> simp
    simp only [wStep, PTm.subst_add, PTm.subst_mul, ha]
    simp
  rw [e] at h
  refine h.eqTrans (congrAdd (congrMul ?_ (.eqRefl _)) (congrInst2 a (.eqRefl _) (snd_pair _ _)))
  have f : Γ ⊢[PRAAx] fstT (pairT r y) ≐ r := fst_pair _ _
  exact congrPw (.eqRefl _) (congrMul (congrSucc f) (congrMonus (congrAp2 quoF (.eqRefl _) (congrMul (.eqRefl _) f))
    (congrAp2 quoF (.eqRefl _) (congrMul (.eqRefl _) f))))

theorem M_succ (y N : PTm n) : Γ ⊢[PRAAx] Mv a y (succ N) ≐ Mv a y N + inst2 a (succ N) y := by
  have h := sum_succ (Γ := Γ) (shiftBody a) N y
  have e : Syn.subst ![N, y] (shiftBody a) = inst2 a (succ N) y := inst2_shiftBody a N y
  rw [e] at h
  exact h

/-! ## Recovering the growth bound -/

variable (aP aN : PTm 2)

/-- `u_x` as a body over `0 = x`, `1 = r`. -/
def uBody : PTm 2 := uu (var 1) (var 0)

/-- The hypothesis `|W(i)| ≤ 2^K u_i` for every `i`. -/
abbrev WBound (r y K : PTm n) : Fm PTm n :=
  Fm.all (le (absd (Wv aP (Syn.shift r) (Syn.shift y) (var 0)) (Wv aN (Syn.shift r) (Syn.shift y) (var 0)))
    (pw two (Syn.shift K) * uu (Syn.shift r) (var 0)))

/-- `|M(N) − W(N)| ≤ 2^K u_N`, written as `|(M⁺ + W⁻) − (M⁻ + W⁺)|`. -/
abbrev DiffF (r y K N : PTm n) : Fm PTm n :=
  le (absd (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N)) (pw two K * uu r N)

/-- One step of the difference: `D(N+1) = D(N) − (ρ_N − 1) W(N)` gives the bound at `N + 1` (`N ≥ 1`). -/
theorem diff_step {r y K N : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hN : Γ ⊢[PRAAx] le one N)
    (ih : Γ ⊢[PRAAx] DiffF aP aN r y K N)
    (hW : Γ ⊢[PRAAx] le (absd (Wv aP r y N) (Wv aN r y N)) (pw two K * uu r N)) :
    Γ ⊢[PRAAx] DiffF aP aN r y K (succ N) := by
  have mP := natEq (M_succ (Γ := Γ) aP y N)
  have mN := natEq (M_succ (Γ := Γ) aN y N)
  have wP := natEq (W_succ (Γ := Γ) aP r y N)
  have wN := natEq (W_succ (Γ := Γ) aN r y N)
  have hρ : Γ ⊢[PRAAx] rho r N ≐ succ (pred (rho r N)) := pos_of_one_le (rho_pos r N)
  have qq : ∀ (W : PTm n), Γ ⊢[PRAAx] rho r N * W ≐ pred (rho r N) * W + W := fun W =>
    (congrMul hρ (.eqRefl W)).eqTrans (by apply deriveNat; ipra_simps; ring)
  have q1 := natEq (qq (Wv aP r y N))
  have q2 := natEq (qq (Wv aN r y N))
  have q3 := natEq ((congrMul (.eqRefl (pw two K)) ((uu_succ hr hN).eqTrans
    (congrMul hρ (.eqRefl _)))).eqTrans (by apply deriveNat; ipra_simps; ring) :
    Γ ⊢[PRAAx] pw two K * uu r (succ N) ≐ pw two K * (pred (rho r N) * uu r N) + pw two K * uu r N)
  have l1 := le_absd_l (Γ := Γ) (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N)
  have l2 := le_absd_r (Γ := Γ) (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N)
  have h1 : Γ ⊢[PRAAx] le (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N + pw two K * uu r N) := by
    ipra_le sl l1 + sl ih
  have h2 : Γ ⊢[PRAAx] le (Mv aN y N + Wv aP r y N) (Mv aP y N + Wv aN r y N + pw two K * uu r N) := by
    ipra_le sl l2 + sl ih
  have w1 : Γ ⊢[PRAAx] le (Wv aN r y N) (Wv aP r y N + pw two K * uu r N) := by
    have l := le_absd_r (Γ := Γ) (Wv aP r y N) (Wv aN r y N); ipra_le sl l + sl hW
  have w2 : Γ ⊢[PRAAx] le (Wv aP r y N) (Wv aN r y N + pw two K * uu r N) := by
    have l := le_absd_l (Γ := Γ) (Wv aP r y N) (Wv aN r y N); ipra_le sl l + sl hW
  have m1 := le_mul_mono (le_refl (pred (rho r N))) w1
  have m2 := le_mul_mono (le_refl (pred (rho r N))) w2
  refine absd_le ?_ ?_
  · ipra_le sl h1 + sl m1 with mN + wP - mP - wN + q1 - q2 + q3
  · ipra_le sl h2 + sl m2 with mP + wN - mN - wP + q2 - q1 + q3

/-- The first step `N = 0`: `M(1) = W(1) = a(1)`. -/
theorem diff_one (r y K : PTm n) : Γ ⊢[PRAAx] DiffF aP aN r y K one := by
  have mP := natEq (M_succ (Γ := Γ) aP y zero)
  have mN := natEq (M_succ (Γ := Γ) aN y zero)
  have wP := natEq (W_succ (Γ := Γ) aP r y zero)
  have wN := natEq (W_succ (Γ := Γ) aN r y zero)
  have m0P := natEq (sum_zero (Γ := Γ) (shiftBody aP) y)
  have m0N := natEq (sum_zero (Γ := Γ) (shiftBody aN) y)
  have z1 := natEq ((congrMul (.eqRefl (rho r zero)) (W_zero (Γ := Γ) aP r y)).eqTrans (mul_zero _))
  have z2 := natEq ((congrMul (.eqRefl (rho r zero)) (W_zero (Γ := Γ) aN r y)).eqTrans (mul_zero _))
  refine absd_le ?_ ?_
  · ipra_le 𝔞 (pw two K * uu r one) with mN + wP - mP - wN + m0N - m0P + z1 - z2
  · ipra_le 𝔞 (pw two K * uu r one) with mP + wN - mN - wP + m0P - m0N + z2 - z1

/-- `|M(N) − W(N)| ≤ 2^K u_N` for every `N`, from `|W(i)| ≤ 2^K u_i` for every `i`. -/
theorem diff_bound {r y K : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hW : Γ ⊢[PRAAx] WBound aP aN r y K) (N : PTm n) :
    Γ ⊢[PRAAx] DiffF aP aN r y K N := by
  have hall : Γ ⊢[PRAAx] Fm.all (DiffF aP aN (Syn.shift r) (Syn.shift y) (Syn.shift K) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [DiffF, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT, LeanProofs.IPRA.PTm.subst_pred,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have e1 := natEq (sum_zero (Γ := Γ) (shiftBody aP) y)
      have e2 := natEq (sum_zero (Γ := Γ) (shiftBody aN) y)
      have e3 := natEq (W_zero (Γ := Γ) aP r y)
      have e4 := natEq (W_zero (Γ := Γ) aN r y)
      refine absd_le ?_ ?_
      · ipra_le 𝔞 (pw two K * uu r zero) with e2 + e3 - e1 - e4
      · ipra_le 𝔞 (pw two K * uu r zero) with e1 + e4 - e2 - e3
    · simp only [DiffF, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT, LeanProofs.IPRA.PTm.subst_pred,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      let φ : Fm PTm (n + 1) := DiffF aP aN (Syn.shift r) (Syn.shift y) (Syn.shift K) (var 0)
      let Δ : List (Fm PTm (n + 1)) := φ :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] φ := Prf.hyp0
      have hr' : Δ ⊢[PRAAx] le one (Syn.shift r) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift r) := by simpa [Fm.shift, Syn.shift] using hr.shift
        exact b.wk
      have hW' : Δ ⊢[PRAAx] le (absd (Wv aP (Syn.shift r) (Syn.shift y) (var 0)) (Wv aN (Syn.shift r) (Syn.shift y) (var 0)))
          (pw two (Syn.shift K) * uu (Syn.shift r) (var 0)) := hW.allOpen.wk
      refine .orE (lt_or_le zero (var 0)) ?_ ?_
      · exact diff_step aP aN hr'.wk (Prf.hyp0 : (lt zero (var 0) :: Δ) ⊢[PRAAx] _) ih.wk hW'.wk
      · have hz : (le (var 0) zero :: Δ) ⊢[PRAAx] var 0 ≐ zero := (monus_zero _).eqSymm.eqTrans Prf.hyp0
        let C0 : List (Fm PTm (n + 1)) := le (var 0) zero :: Δ
        have d := diff_one (Γ := C0) aP aN (Syn.shift r) (Syn.shift y) (Syn.shift K)
        have e : C0 ⊢[PRAAx] (one : PTm (n + 1)) ≐ succ (var 0) := (congrSucc hz).eqSymm
        have cMP : C0 ⊢[PRAAx] Mv aP (Syn.shift y) one ≐ Mv aP (Syn.shift y) (succ (var 0)) := congrAp2 _ e (.eqRefl _)
        have cMN : C0 ⊢[PRAAx] Mv aN (Syn.shift y) one ≐ Mv aN (Syn.shift y) (succ (var 0)) := congrAp2 _ e (.eqRefl _)
        have cWP : C0 ⊢[PRAAx] Wv aP (Syn.shift r) (Syn.shift y) one ≐ Wv aP (Syn.shift r) (Syn.shift y) (succ (var 0)) :=
          congrAp2 _ e (.eqRefl _)
        have cWN : C0 ⊢[PRAAx] Wv aN (Syn.shift r) (Syn.shift y) one ≐ Wv aN (Syn.shift r) (Syn.shift y) (succ (var 0)) :=
          congrAp2 _ e (.eqRefl _)
        have cu : C0 ⊢[PRAAx] uu (Syn.shift r) one ≐ uu (Syn.shift r) (succ (var 0)) :=
          congrPw (.eqRefl _) (congrMul (.eqRefl _) (congrAp2 quoF (congrPred (congrAp2 _ (congrSucc (congrSucc e))
            (congrSucc e))) (.eqRefl _)))
        exact le_congr (congrAdd (congrMonus (congrAdd cMP cWN) (congrAdd cMN cWP))
          (congrMonus (congrAdd cMN cWP) (congrAdd cMP cWN))) (congrMul (.eqRefl _) cu) d
  have a := Prf.allE N hall
  simp only [DiffF, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
    LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at a
  exact a

/-- `thm:rate` (2) ⇒ (1), core: `|W(i)| ≤ 2^K u_i` for every `i` gives `|M(N)|^{2r} ≤ 2^{2r(K+1)} N^{r+1}`. -/
theorem recover {r y K : PTm n} (hr : Γ ⊢[PRAAx] le one r) (hW : Γ ⊢[PRAAx] WBound aP aN r y K) (N : PTm n) :
    Γ ⊢[PRAAx] le (pw (absd (Mv aP y N) (Mv aN y N)) (two * r)) (pw two (two * r * succ K) * pw N (succ r)) := by
  refine .orE (lt_or_le zero N) ?_ ?_
  · let C : List (Fm PTm n) := lt zero N :: Γ
    have hN : C ⊢[PRAAx] le one N := Prf.hyp0
    have d := diff_bound (Γ := C) aP aN hr.wk hW.wk N
    have w : C ⊢[PRAAx] le (absd (Wv aP r y N) (Wv aN r y N)) (pw two K * uu r N) := by
      have b := Prf.allE N (hW.wk : C ⊢[PRAAx] _)
      simp only [WBound, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_pairT,
        LeanProofs.IPRA.PTm.subst_pred, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
        Syn.inst_zero, Syn.subst_inst_shift] at b
      exact b
    have l1 := le_absd_l (Γ := C) (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N)
    have l2 := le_absd_r (Γ := C) (Mv aP y N + Wv aN r y N) (Mv aN y N + Wv aP r y N)
    have l3 := le_absd_l (Γ := C) (Wv aP r y N) (Wv aN r y N)
    have l4 := le_absd_r (Γ := C) (Wv aP r y N) (Wv aN r y N)
    have e2 := natEq ((congrMul (pw_succ (Γ := C) two K) (.eqRefl (uu r N))).eqTrans
      (by apply deriveNat; ipra_simps; ring) :
      C ⊢[PRAAx] pw two (succ K) * uu r N ≐ pw two K * uu r N + pw two K * uu r N)
    have hM : C ⊢[PRAAx] le (absd (Mv aP y N) (Mv aN y N)) (pw two (succ K) * uu r N) := by
      refine absd_le ?_ ?_
      · ipra_le sl l1 + sl d + sl l3 + sl w with e2
      · ipra_le sl l2 + sl d + sl l4 + sl w with e2
    have p1 := pw_le_pw (two * r) hM
    have e3 : C ⊢[PRAAx] pw (pw two (succ K) * uu r N) (two * r) ≐
        pw two (two * r * succ K) * pw (uu r N) (two * r) :=
      (pw_mul_base _ _ _).eqTrans (congrMul ((pw_mul _ _ _).eqTrans (congrPw (.eqRefl _)
        (by apply deriveNat; ipra_simps; ring))) (.eqRefl _))
    have p2 := le_mul_mono (le_refl (pw two (two * r * succ K))) (uu_pow hr.wk hN)
    exact le_trans p1 (le_congr e3.eqSymm (.eqRefl _) p2)
  · let C : List (Fm PTm n) := le N zero :: Γ
    have hz : C ⊢[PRAAx] N ≐ zero := (monus_zero N).eqSymm.eqTrans Prf.hyp0
    have s1 : C ⊢[PRAAx] Mv aP y N ≐ zero := (congrAp2 _ hz (.eqRefl _)).eqTrans (sum_zero _ _)
    have s2 : C ⊢[PRAAx] Mv aN y N ≐ zero := (congrAp2 _ hz (.eqRefl _)).eqTrans (sum_zero _ _)
    have hA : C ⊢[PRAAx] absd (Mv aP y N) (Mv aN y N) ≐ zero :=
      (congrAdd (congrMonus s1 s2) (congrMonus s2 s1)).eqTrans
        ((congrAdd (monus_zero _) (monus_zero _)).eqTrans (add_zero _))
    have h2 : C ⊢[PRAAx] two * r ≐ succ (pred (two * r)) := two_r_pos hr.wk
    have z : C ⊢[PRAAx] pw (absd (Mv aP y N) (Mv aN y N)) (two * r) ≐ zero :=
      (congrPw hA h2).eqTrans ((pw_succ zero _).eqTrans (mul_zero _))
    exact le_congr z.eqSymm (.eqRefl _) (by ipra_le 𝔞 (pw two (two * r * succ K) * pw N (succ r)))

end LeanProofs.IPRA.AnalyticNumberTheory.RateAbel
