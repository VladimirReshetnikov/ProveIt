import IPRADerivations.AnalyticNumberTheory.PowerDivisorGrowth

/-!
# Euler's constant without an unspecified convergence rate (`robin_ipra_research_2026-11-19`, `lem:gamma`)

Packet: `analytic-number-theory/robin_ipra_research_2026-11-19`, `paper/report.tex`, Lemma `lem:gamma`: for
`a_m = H_m − log m − 1/(2m)`, "`a_m ≤ γ ≤ a_m + 1/(12m²)` … these bounds follow from a finite telescoping estimate with an
explicit tail": with `z = 1/(2m+1)`, `a_{m+1} − a_m = 2z/(1−z²) − 2 artanh z`, `0 < a_{m+1} − a_m ≤ 1/(12m²) − 1/(12(m+1)²)`,
"Each displayed infinite sum can be replaced by a finite sum and its explicit geometric tail."

Here `log(1 + 1/m) = 2 artanh z` is named by the truncations `S_K(z) = 2 Σ_{j<K} z^{2j+1}/(2j+1)` (the packet's
`eq:logtail`), written with cleared denominators: for `s = 2m + 1`,
`S_K(1/s) = N_K / D_K`, `D_K = L_K s^{2K+1}`, `L_K = Π_{j<K} (2j+1)`, `N_{K+1} = (2K+1)s² N_K + 2 s² L_K` (`Nv`, `Lv`).
With `W = 4m(m+1) = s² − 1` the increment `δ_K(m) = (1/(2m) + 1/(2(m+1))) − S_K(1/s) = 2s/W − N_K/D_K`, and:

* `q_inv`: `N_K W + 2 L_K s² ≤ 2 s D_K` for every `K`, i.e. `S_K(z) + 2z^{2K+1}/(1−z²) ≤ 2z/(1−z²)`: the increment
  stays at least the explicit geometric tail, which dominates the truncation error `log − S_K ≤ 2z^{2K+1}/((2K+1)(1−z²))`
  (so `a_{m+1} − a_m ≥ 0` for the true logarithm);
* `p_inv`: `6 s W D_K ≤ 4 s D_K + 3 W² N_K` for `K ≥ 2`, i.e. `δ_K(m) ≤ 1/(12m²) − 1/(12(m+1)²)`;
* `step_lower`, `step_upper`: `δ_K(m) = n/d` (`nn`, `dd`) with `n ≥ 2 L_K s²` and `12 m²(m+1)² n ≤ s d`;
* `gamma_tail`: the finite telescoping estimate. For `m₀ ≥ 1`, `K ≥ 2`, the partial sums `P_t/Q_t = Σ_{i<t} δ_K(m₀+i)`
  (primitive recursions `Pt`, `Qt`) satisfy `12 m₀² M² P_t + m₀² Q_t ≤ M² Q_t`, `M = m₀ + t`, i.e.
  `a^{(K)}_{M} − a^{(K)}_{m₀} = Σ δ_K ≤ 1/(12m₀²) − 1/(12M²)`: an explicit Cauchy modulus for the `a_m`, uniform in the
  truncation `K ≥ 2`.

The identification of the limit name with the usual Euler constant (and `log` with the analytic logarithm) is the external
interpretation stated in the packet; at `m₀ = 1` the estimate gives `1/2 ≤ γ ≤ 7/12`.
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The cleared truncations -/

/-- `L_K = Π_{j<K} (2j+1)` (the parameter is unused). -/
def Lf : PR 2 := rec2 (succ zero) (succ (two * var 0) * var 1)
/-- `N_{K+1} = (2K+1) s² N_K + 2 s² L_K` at the parameter `s`. -/
def Nf : PR 2 := rec2 zero (var 1 * succ (two * var 0) * (var 2 * var 2) + two * ap2 Lf (var 0) (var 2) * (var 2 * var 2))

abbrev Lv (K s : PTm n) : PTm n := ap2 Lf K s
abbrev Nv (K s : PTm n) : PTm n := ap2 Nf K s
/-- `s^{2K+1}`. -/
abbrev Pv (K s : PTm n) : PTm n := pw s (succ (two * K))
/-- `s = 2m + 1` and `W = 4m(m+1) = s² − 1`. -/
abbrev sv (m : PTm n) : PTm n := succ (two * m)
abbrev Wv (m : PTm n) : PTm n := two * two * m * succ m

theorem L_zero (s : PTm n) : Γ ⊢[PRAAx] Lv zero s ≐ one := by
  have h := rec2_zero (Γ := Γ) (succ zero) (succ (two * var 0) * var 1) s
  simp only [ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem L_succ (K s : PTm n) : Γ ⊢[PRAAx] Lv (succ K) s ≐ succ (two * K) * Lv K s := by
  have h : Γ ⊢[PRAAx] ap2 Lf (succ K) s ≐ Syn.subst ![K, ap2 Lf K s, s] (succ (two * var 0) * var 1) :=
    rec2_succ (Γ := Γ) (succ zero) (succ (two * var 0) * var 1) K s
  have e : Syn.subst ![K, ap2 Lf K s, s] (succ (two * var 0) * var 1) = succ (two * K) * ap2 Lf K s := by simp
  rw [e] at h
  exact h

theorem N_zero (s : PTm n) : Γ ⊢[PRAAx] Nv zero s ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero
    (var 1 * succ (two * var 0) * (var 2 * var 2) + two * ap2 Lf (var 0) (var 2) * (var 2 * var 2)) s
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem N_succ (K s : PTm n) :
    Γ ⊢[PRAAx] Nv (succ K) s ≐ Nv K s * succ (two * K) * (s * s) + two * Lv K s * (s * s) := by
  have h : Γ ⊢[PRAAx] ap2 Nf (succ K) s ≐ Syn.subst ![K, ap2 Nf K s, s]
      (var 1 * succ (two * var 0) * (var 2 * var 2) + two * ap2 Lf (var 0) (var 2) * (var 2 * var 2)) :=
    rec2_succ (Γ := Γ) zero
      (var 1 * succ (two * var 0) * (var 2 * var 2) + two * ap2 Lf (var 0) (var 2) * (var 2 * var 2)) K s
  have e : Syn.subst ![K, ap2 Nf K s, s]
      (var 1 * succ (two * var 0) * (var 2 * var 2) + two * ap2 Lf (var 0) (var 2) * (var 2 * var 2)) =
      ap2 Nf K s * succ (two * K) * (s * s) + two * ap2 Lf K s * (s * s) := by simp
  rw [e] at h
  exact h

theorem P_succ (K s : PTm n) : Γ ⊢[PRAAx] Pv (succ K) s ≐ Pv K s * s * s := by
  have ex : Γ ⊢[PRAAx] succ (two * succ K) ≐ succ (succ (succ (two * K))) := by
    ipra_ring
  refine (congrAp2 powF ex (.eqRefl _)).eqTrans ?_
  exact (pw_succ s _).eqTrans (congrMul (pw_succ s _) (.eqRefl _))

theorem P_zero (s : PTm n) : Γ ⊢[PRAAx] Pv zero s ≐ s := by
  have ex : Γ ⊢[PRAAx] succ (two * zero) ≐ succ zero := by ipra_ring
  refine (congrAp2 powF ex (.eqRefl _)).eqTrans ?_
  exact (pw_succ s _).eqTrans ((congrMul (pw_zero s) (.eqRefl _)).eqTrans (one_mul _))

/-! ## The two invariants -/

/-- `N_K W + 2 L_K s² ≤ 2 s L_K s^{2K+1}`. -/
abbrev QF (m K : PTm n) : Fm PTm n :=
  le (Nv K (sv m) * Wv m + two * Lv K (sv m) * (sv m * sv m)) (two * sv m * (Lv K (sv m) * Pv K (sv m)))

theorem q_step (m K : PTm n) (ih : Γ ⊢[PRAAx] QF m K) : Γ ⊢[PRAAx] QF m (succ K) := by
  have h1 := le_mul_mono ih (le_refl (succ (two * K) * (sv m * sv m)))
  have hN := N_succ (Γ := Γ) K (sv m)
  have hL := L_succ (Γ := Γ) K (sv m)
  have hP := P_succ (Γ := Γ) K (sv m)
  have e1 := natEq (congrMul hN (.eqRefl (Wv m)))
  have e2 := natEq (congrMul (congrMul (.eqRefl two) hL) (.eqRefl (sv m * sv m)))
  have e3 := natEq (congrMul (.eqRefl (two * sv m)) (congrMul hL hP))
  ipra_le sl h1 + 𝔞 (two * Lv K (sv m) * (sv m * sv m) * (two * K * Wv m)) with e3 - e1 - e2

theorem q_inv (m K : PTm n) : Γ ⊢[PRAAx] QF m K := by
  have hall : Γ ⊢[PRAAx] Fm.all (QF (Syn.shift m) (var 0)) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have hL := L_zero (Γ := Γ) (sv m)
      have e2 := natEq (congrMul (congrMul (.eqRefl two) hL) (.eqRefl (sv m * sv m)))
      have e3 := natEq (congrMul (.eqRefl (two * sv m)) (congrMul hL (P_zero (Γ := Γ) (sv m))))
      have e1 := natEq (congrMul (N_zero (Γ := Γ) (sv m)) (.eqRefl (Wv m)))
      ipra_le 0 with e3 - e1 - e2
    · simp only [Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact q_step _ _ Prf.hyp0
  have r := Prf.allE K hall
  simpa [Syn.subst_inst_shift] using r

/-- `6 s W L_K s^{2K+1} ≤ 4 s L_K s^{2K+1} + 3 W² N_K`. -/
abbrev PF (m K : PTm n) : Fm PTm n :=
  le (two * succ two * sv m * Wv m * (Lv K (sv m) * Pv K (sv m)))
    (two * two * sv m * (Lv K (sv m) * Pv K (sv m)) + succ two * (Wv m * Wv m) * Nv K (sv m))

theorem p_step (m K : PTm n) (ih : Γ ⊢[PRAAx] PF m K) : Γ ⊢[PRAAx] PF m (succ K) := by
  have h1 := le_mul_mono ih (le_refl (succ (two * K) * (sv m * sv m)))
  have hN := N_succ (Γ := Γ) K (sv m)
  have hL := L_succ (Γ := Γ) K (sv m)
  have hP := P_succ (Γ := Γ) K (sv m)
  have eA := natEq (congrMul (.eqRefl (two * succ two * sv m * Wv m)) (congrMul hL hP))
  have eB := natEq (congrMul (.eqRefl (two * two * sv m)) (congrMul hL hP))
  have eC := natEq (congrMul (.eqRefl (succ two * (Wv m * Wv m))) hN)
  ipra_le sl h1 + 𝔞 (two * succ two * (Wv m * Wv m) * Lv K (sv m) * (sv m * sv m)) with eB + eC - eA

theorem p_two (m : PTm n) : Γ ⊢[PRAAx] PF m (succ (succ zero)) := by
  have l1 : Γ ⊢[PRAAx] Lv (succ zero) (sv m) ≐ one :=
    (L_succ zero (sv m)).eqTrans ((congrMul (.eqRefl _) (L_zero (sv m))).eqTrans (by ipra_ring))
  have l2 : Γ ⊢[PRAAx] Lv (succ (succ zero)) (sv m) ≐ succ two :=
    (L_succ (succ zero) (sv m)).eqTrans ((congrMul (.eqRefl _) l1).eqTrans (by ipra_ring))
  have n1 : Γ ⊢[PRAAx] Nv (succ zero) (sv m) ≐ two * ((sv m) * (sv m)) :=
    (N_succ zero (sv m)).eqTrans (by
      refine withEq (N_zero (Γ := Γ) (sv m)) fun e0 => withEq (L_zero (Γ := Γ) (sv m)) fun e1 => ?_
      apply deriveNat; ipra_simps; rw [e0, e1]; ring)
  have n2 : Γ ⊢[PRAAx] Nv (succ (succ zero)) (sv m) ≐ two * succ two * ((sv m) * (sv m) * ((sv m) * (sv m))) + two * ((sv m) * (sv m)) :=
    (N_succ (succ zero) (sv m)).eqTrans (by
      refine withEq n1 fun e0 => withEq l1 fun e1 => ?_
      apply deriveNat; ipra_simps; rw [e0, e1]; ring)
  have p2 : Γ ⊢[PRAAx] Pv (succ (succ zero)) (sv m) ≐ (sv m) * (sv m) * (sv m) * (sv m) * (sv m) :=
    (P_succ (succ zero) (sv m)).eqTrans (congrMul (congrMul ((P_succ zero (sv m)).eqTrans
      (congrMul (congrMul (P_zero (sv m)) (.eqRefl _)) (.eqRefl _))) (.eqRefl _)) (.eqRefl _))
  have eA := natEq (congrMul (.eqRefl (two * succ two * sv m * Wv m)) (congrMul l2 p2))
  have eB := natEq (congrMul (.eqRefl (two * two * sv m)) (congrMul l2 p2))
  have eC := natEq (congrMul (.eqRefl (succ two * (Wv m * Wv m))) n2)
  ipra_le 𝔞 (two * succ two * (sv m * sv m) * (sv m * sv m + one)) with eB + eC - eA

theorem p_inv (m j : PTm n) : Γ ⊢[PRAAx] PF m (succ (succ j)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (PF (Syn.shift m) (succ (succ (var 0)))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      exact p_two m
    · simp only [Fm.subst_eq, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, ConciseIPRA.PTm.subst_succ,
        ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      exact p_step _ _ Prf.hyp0
  have r := Prf.allE j hall
  simpa [Syn.subst_inst_shift] using r

/-! ## One step of the telescoping -/

/-- `δ_K(m) = n/d`: `n = 2 s D_K − N_K W`, `d = W D_K`. -/
abbrev nn (m K : PTm n) : PTm n := monus (two * sv m * (Lv K (sv m) * Pv K (sv m))) (Nv K (sv m) * Wv m)
abbrev dd (m K : PTm n) : PTm n := Wv m * (Lv K (sv m) * Pv K (sv m))

theorem n_eq (m K : PTm n) :
    Γ ⊢[PRAAx] two * sv m * (Lv K (sv m) * Pv K (sv m)) ≐ Nv K (sv m) * Wv m + nn m K := by
  have q := q_inv (Γ := Γ) m K
  exact eq_add_of_le (by ipra_le sl q + 𝔞 (two * Lv K (sv m) * (sv m * sv m)))

/-- The increment stays above the geometric tail: `n ≥ 2 L_K s²`. -/
theorem step_lower (m K : PTm n) : Γ ⊢[PRAAx] le (two * Lv K (sv m) * (sv m * sv m)) (nn m K) := by
  have q := q_inv (Γ := Γ) m K
  have e := natEq (n_eq (Γ := Γ) m K)
  ipra_le sl q with e

/-- `δ_K(m) ≤ 1/(12m²) − 1/(12(m+1)²)` for `K ≥ 2`: `12 m²(m+1)² n ≤ s d`. -/
theorem step_upper (m j : PTm n) :
    Γ ⊢[PRAAx] le (two * two * succ two * (m * m) * (succ m * succ m) * nn m (succ (succ j)))
      (sv m * dd m (succ (succ j))) := by
  have p := p_inv (Γ := Γ) m j
  have e := natEq (congrMul (.eqRefl (succ two * Wv m)) (n_eq (Γ := Γ) m (succ (succ j))))
  have h3 : Γ ⊢[PRAAx] le (succ two * Wv m * nn m (succ (succ j)))
      (two * two * sv m * (Lv (succ (succ j)) (sv m) * Pv (succ (succ j)) (sv m))) := by
    ipra_le sl p with e
  have h4 := le_mul_mono h3 (le_refl (Wv m))
  have h5 : Γ ⊢[PRAAx] le (succ (succ two) * (two * two * succ two * (m * m) * (succ m * succ m) * nn m (succ (succ j))))
      (succ (succ two) * (sv m * dd m (succ (succ j)))) := by
    ipra_le sl h4
  exact mul_le_cancel h5

/-! ## The telescoped estimate -/

/-- `d`, `n` at `m₀ + t` over `0 = t`, `1 = ⟨m₀, K⟩`. -/
def dB : PTm 2 := dd (fstT (var 1) + var 0) (sndT (var 1))
def nB : PTm 2 := nn (fstT (var 1) + var 0) (sndT (var 1))

/-- `Q_t = Π_{i<t} d(m₀+i)`. -/
abbrev Qt (t x : PTm n) : PTm n := ap2 (prodF dB) t x
/-- `P_{t+1} = P_t d(m₀+t) + n(m₀+t) Q_t`, so that `P_t/Q_t = Σ_{i<t} δ_K(m₀+i)`. -/
def Pf : PR 2 := rec2 zero (var 1 * Syn.subst ![var 0, var 2] dB + Syn.subst ![var 0, var 2] nB * ap2 (prodF dB) (var 0) (var 2))
abbrev Pt (t x : PTm n) : PTm n := ap2 Pf t x

theorem inst2_dB (t x : PTm n) : inst2 dB t x = dd (fstT x + t) (sndT x) := by simp [inst2, dB]
theorem inst2_nB (t x : PTm n) : inst2 nB t x = nn (fstT x + t) (sndT x) := by simp [inst2, nB]

theorem dB_at (t m K : PTm n) : Γ ⊢[PRAAx] inst2 dB t (pairT m K) ≐ dd (m + t) K := by
  rw [inst2_dB]
  have c := congrInst2 (Γ := Γ) (dd (var 0) (var 1) : PTm 2) (congrAdd (fst_pair m K) (.eqRefl t)) (snd_pair m K)
  simpa [inst2] using c

theorem nB_at (t m K : PTm n) : Γ ⊢[PRAAx] inst2 nB t (pairT m K) ≐ nn (m + t) K := by
  rw [inst2_nB]
  have c := congrInst2 (Γ := Γ) (nn (var 0) (var 1) : PTm 2) (congrAdd (fst_pair m K) (.eqRefl t)) (snd_pair m K)
  simpa [inst2] using c

theorem Q_succ (t x : PTm n) : Γ ⊢[PRAAx] Qt (succ t) x ≐ Qt t x * inst2 dB t x := prod_succ _ _ _

theorem P_zero' (x : PTm n) : Γ ⊢[PRAAx] Pt zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero
    (var 1 * Syn.subst ![var 0, var 2] dB + Syn.subst ![var 0, var 2] nB * ap2 (prodF dB) (var 0) (var 2)) x
  simp only [ConciseIPRA.PTm.subst_zero] at h
  exact h

theorem P_succ' (t x : PTm n) : Γ ⊢[PRAAx] Pt (succ t) x ≐ Pt t x * inst2 dB t x + inst2 nB t x * Qt t x := by
  have h : Γ ⊢[PRAAx] ap2 Pf (succ t) x ≐ Syn.subst ![t, ap2 Pf t x, x]
      (var 1 * Syn.subst ![var 0, var 2] dB + Syn.subst ![var 0, var 2] nB * ap2 (prodF dB) (var 0) (var 2)) :=
    rec2_succ (Γ := Γ) zero
      (var 1 * Syn.subst ![var 0, var 2] dB + Syn.subst ![var 0, var 2] nB * ap2 (prodF dB) (var 0) (var 2)) t x
  have e : Syn.subst ![t, ap2 Pf t x, x]
      (var 1 * Syn.subst ![var 0, var 2] dB + Syn.subst ![var 0, var 2] nB * ap2 (prodF dB) (var 0) (var 2)) =
      ap2 Pf t x * inst2 dB t x + inst2 nB t x * ap2 (prodF dB) t x := by
    have h1 : Syn.subst ![t, ap2 Pf t x, x] (Syn.subst ![var 0, var 2] dB) = inst2 dB t x := by
      simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl
    have h2 : Syn.subst ![t, ap2 Pf t x, x] (Syn.subst ![var 0, var 2] nB) = inst2 nB t x := by
      simp only [inst2, Syn.subst_subst]; congr 1; funext k; fin_cases k <;> rfl
    simp only [PTm.subst_add, PTm.subst_mul, h1, h2, subst_ap2, Syn.subst_var]
    rfl
  rw [e] at h
  exact h

/-- `12 m₀² M² P_t + m₀² Q_t ≤ M² Q_t` at `M = m₀ + t`. -/
abbrev TF (m t K : PTm n) : Fm PTm n :=
  le (two * two * succ two * (m * m) * ((m + t) * (m + t)) * Pt t (pairT m K) + m * m * Qt t (pairT m K))
    ((m + t) * (m + t) * Qt t (pairT m K))

theorem t_step {m t j : PTm n} (hm : Γ ⊢[PRAAx] le one m) (ih : Γ ⊢[PRAAx] TF m t (succ (succ j))) :
    Γ ⊢[PRAAx] TF m (succ t) (succ (succ j)) := by
  have hd := dB_at (Γ := Γ) t m (succ (succ j))
  have hn := nB_at (Γ := Γ) t m (succ (succ j))
  have su := step_upper (Γ := Γ) (m + t) j
  -- IH times ((m + t)+1)² d, and the step bound times m² Q
  have h1 := le_mul_mono ih (le_refl (succ (m + t) * succ (m + t) * dd (m + t) (succ (succ j))))
  have h2 := le_mul_mono su (le_refl (m * m * Qt t (pairT m (succ (succ j)))))
  have eP := P_succ' (Γ := Γ) t (pairT m (succ (succ j)))
  have eQ := Q_succ (Γ := Γ) t (pairT m (succ (succ j)))
  have eP' : Γ ⊢[PRAAx] Pt (succ t) (pairT m (succ (succ j))) ≐ Pt t (pairT m (succ (succ j))) * dd (m + t) (succ (succ j)) + nn (m + t) (succ (succ j)) * Qt t (pairT m (succ (succ j))) :=
    eP.eqTrans (congrAdd (congrMul (.eqRefl _) hd) (congrMul hn (.eqRefl _)))
  have eQ' : Γ ⊢[PRAAx] Qt (succ t) (pairT m (succ (succ j))) ≐ Qt t (pairT m (succ (succ j))) * dd (m + t) (succ (succ j)) := eQ.eqTrans (congrMul (.eqRefl _) hd)
  have hM : Γ ⊢[PRAAx] le one (m + t) := by ipra_le sl hm + 𝔞 t
  have hp : Γ ⊢[PRAAx] (m + t) * (m + t) ≐ succ (pred ((m + t) * (m + t))) := pos_of_one_le (by
    have q := le_mul_mono hM hM
    ipra_le sl q)
  have fin : Γ ⊢[PRAAx] le ((m + t) * (m + t) * (two * two * succ two * (m * m) * (succ (m + t) * succ (m + t)) *
        (Pt t (pairT m (succ (succ j))) * dd (m + t) (succ (succ j)) + nn (m + t) (succ (succ j)) * Qt t (pairT m (succ (succ j)))) + m * m * (Qt t (pairT m (succ (succ j))) * dd (m + t) (succ (succ j)))))
      ((m + t) * (m + t) * (succ (m + t) * succ (m + t) * (Qt t (pairT m (succ (succ j))) * dd (m + t) (succ (succ j))))) := by
    ipra_le sl h1 + sl h2
  have c := mul_le_cancel (le_congr (congrMul hp (.eqRefl _)) (congrMul hp (.eqRefl _)) fin)
  have eM : Γ ⊢[PRAAx] m + succ t ≐ succ (m + t) := by ipra_ring
  refine le_congr ?_ ?_ c
  · exact (congrAdd (congrMul (congrMul (.eqRefl _) (congrMul eM eM)).eqSymm eP'.eqSymm)
      (congrMul (.eqRefl _) eQ'.eqSymm))
  · exact congrMul (congrMul eM eM).eqSymm eQ'.eqSymm

/-- `lem:gamma`, the finite telescoping estimate: for `m₀ ≥ 1` and `K ≥ 2`,
`Σ_{i<t} δ_K(m₀+i) ≤ 1/(12m₀²) − 1/(12(m₀+t)²)` in cleared form. -/
theorem gamma_tail {m : PTm n} (hm : Γ ⊢[PRAAx] le one m) (j t : PTm n) : Γ ⊢[PRAAx] TF m t (succ (succ j)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (TF (Syn.shift m) (var 0) (succ (succ (Syn.shift j)))) := by
    refine PRA.qfInd _ (le_QF _ _) ?_ ?_
    · simp only [Fm.subst_eq, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
      have p0 := natEq (congrMul (.eqRefl (two * two * succ two * (m * m) * ((m + zero) * (m + zero))))
        (P_zero' (Γ := Γ) (pairT m (succ (succ j))) : Γ ⊢[PRAAx] ap2 Pf zero (pairT m (succ (succ j))) ≐ zero))
      ipra_le 0 with -p0
    · simp only [Fm.subst_eq, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
      have hm' : (TF (Syn.shift m) (var 0) (succ (succ (Syn.shift j))) :: Γ.map Fm.shift) ⊢[PRAAx]
          le one (Syn.shift m) := by
        have b : (Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift m) := by simpa [Fm.shift, Syn.shift] using hm.shift
        exact b.wk
      exact t_step hm' Prf.hyp0
  have r := Prf.allE t hall
  simpa [Syn.subst_inst_shift] using r

end LeanProofs.IPRA.AnalyticNumberTheory.RobinGamma

export_ipra AnalyticNumberTheory.RobinGamma (L_succ L_zero P_succ P_zero)
